"""Live NSE / BSE fetches for the promoter-pledge screen.

BSE shareholding calls follow ipo-tool (same APIs, requests session after a
homepage visit instead of Playwright). Market figures follow blocks_tracker:
Yahoo .NS for live CMP. Daily bars from NSE bhavcopy archives when
www.nseindia.com is down; Yahoo history is the fallback. Delivery is
NSE DELIV_QTY only.
"""
from __future__ import annotations

import calendar
import csv
import json
import re
import threading
import time
import urllib.parse
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from io import StringIO
from pathlib import Path
from typing import Any
from xml.etree import ElementTree as ET

import requests

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
)
CRORE = 10_000_000
METRIC_WINDOWS = [("1d", 1), ("1w", 7), ("1m", 30)]
METRIC_HISTORY_DAYS = 75
MAX_SESSION_GAP_DAYS = 7
NSE_SERIES = ["EQ", "BE", "SM", "ST", "IV"]
EVENT_LOOKBACK_DAYS = 1095
# Yearly SHP samples behind the latest photo, back ~11 years.
SHP_WALK_STEP = 4
SHP_WALK_MAX = 44
_IST = timezone(timedelta(hours=5, minutes=30))
_Q_MONTHS = (3, 6, 9, 12)
_Q_NAMES = {3: "March", 6: "June", 9: "September", 12: "December"}

MONTHS = {
    "january": 1, "february": 2, "march": 3, "april": 4, "may": 5, "june": 6,
    "july": 7, "august": 8, "september": 9, "october": 10, "november": 11,
    "december": 12, "jan": 1, "feb": 2, "mar": 3, "apr": 4, "jun": 6,
    "jul": 7, "aug": 8, "sep": 9, "oct": 10, "nov": 11, "dec": 12,
}


_BSE_PLEDGE_LIST_URL = "https://beta.bseindia.com/corporates/Pledge_new.aspx"
_BSE_PLEDGE_LIST_URLS = (
    "https://beta.bseindia.com/corporates/Pledge_new.aspx",
    "https://www.bseindia.com/corporates/Pledge_new.aspx",
)
_BSE_REG31_URL = "https://beta.bseindia.com/corporates/Regulation_31.aspx"
_NSE_PLEDGED_CACHE = Path(__file__).with_name("nse_pledged_cache.json")
_BSE_PLEDGED_CACHE = Path(__file__).with_name("bse_pledged_cache.json")
_NSE_INVOKE_CACHE = Path(__file__).with_name("nse_invoke_cache.json")
_NSE_RAW_DIR = Path(__file__).resolve().parent / "data" / "raw"
_NSE_PLEDGED_JSON = "https://www.nseindia.com/api/corporate-pledgedata?index=equities"
_NSE_PLEDGED_CSV = "https://www.nseindia.com/api/corporate-pledgedata?index=equities&csv=true"


def _hidden_inputs(html: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for m in re.finditer(r"<input[^>]+type=\"hidden\"[^>]*>", html, flags=re.I):
        tag = m.group(0)
        name = re.search(r'name="([^"]+)"', tag)
        val = re.search(r'value="([^"]*)"', tag)
        if name:
            fields[name.group(1)] = val.group(1) if val else ""
    return fields


def _parse_bse_list_name(raw: str) -> tuple[str, str]:
    s = re.sub(r"\s+", " ", str(raw or "").replace("&amp;", "&")).strip()
    m = re.search(r"^(.*?)(?:-\$)?\((\d+)\)\s*$", s)
    if m:
        return m.group(1).strip(), m.group(2)
    return s, ""


def _csv_col(row: dict, *needles: str):
    for key, val in row.items():
        kl = (key or "").lower()
        if all(n.lower() in kl for n in needles):
            return val
    return None


def _clean_bse_target_name(raw: str) -> str:
    s = re.sub(r"\s+", " ", str(raw or "")).strip()
    s = re.sub(r"#.*$", "", s).strip()
    s = re.sub(r"\s+EQ\b.*$", "", s, flags=re.I)
    if s.isupper():
        s = s.title()
        s = re.sub(r"\bLtd\b", "Ltd", s)
        s = re.sub(r"\bLimited\b", "Limited", s)
        s = re.sub(r"\bAnd\b", "and", s)
    return s.strip()


def _num_field(row: dict, *keys):
    for key in keys:
        if key not in row:
            continue
        n = to_num(row.get(key))
        if n is not None:
            return n
    return None


def to_num(val) -> float | None:
    if val is None or val is False:
        return None
    if isinstance(val, bool):
        return None
    if isinstance(val, (int, float)):
        return float(val)
    s = str(val).strip().replace(",", "").replace("%", "")
    if s in {"", "-", "NA", "None", "null", "—"}:
        return None
    try:
        return float(s)
    except ValueError:
        return None


_DROP = {
    "limited", "ltd", "pvt", "private", "llp", "llc", "plc", "inc",
    "the", "co", "company",
}
_FILLER = {"and", "of", "on", "behalf", "as"}
_TITLES = {"mr", "mrs", "ms", "miss", "shri", "smt", "dr", "sri"}
_ROLES = {"promoter", "promoters", "pac"}


def norm_name(val: str) -> str:
    s = str(val or "").lower()
    s = s.replace("&", " and ")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " ".join(t for t in s.split() if t not in _DROP)


def _person_parts(val: str) -> tuple[list[str], bool]:
    """Tokens and HUF flag. Parentheses are spaces so '(HUF)' is kept."""
    s = str(val or "").lower().replace("&", " and ")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    tokens = [t for t in s.split() if t not in _DROP and t not in _TITLES and t not in _ROLES]
    is_huf = "huf" in tokens
    tokens = [t for t in tokens if t != "huf"]
    return tokens, is_huf


def parse_date(val) -> date | None:
    if val is None:
        return None
    if isinstance(val, datetime):
        return val.date()
    if isinstance(val, date):
        return val
    s = str(val).strip()
    if not s or s in {"-", "None", "null"}:
        return None
    s = s.split(" - ")[0].strip()
    if "T" in s:
        try:
            return datetime.fromisoformat(s.replace("Z", "+00:00")).date()
        except ValueError:
            s = s.split("T")[0]
    for raw in (s, s.split()[0]):
        for fmt in (
            "%Y-%m-%d",
            "%d-%b-%Y %H:%M:%S",
            "%d-%b-%Y %H:%M",
            "%d-%b-%Y",
            "%d-%B-%Y",
            "%d-%m-%Y %H:%M:%S",
            "%d-%m-%Y",
            "%d/%m/%Y",
        ):
            try:
                return datetime.strptime(raw, fmt).date()
            except ValueError:
                continue
    return None


def iso(d: date | None) -> str | None:
    return d.isoformat() if d else None


def fmt_date(d: date | None) -> str | None:
    return d.strftime("%d %b %Y") if d else None


def parse_quarter(qname: str) -> tuple[int, int] | None:
    parts = [p for p in (qname or "").replace(",", " ").replace("-", " ").split() if p]
    if len(parts) < 2:
        return None
    month = MONTHS.get(parts[0].lower())
    try:
        year = int(parts[-1])
    except ValueError:
        return None
    if year < 100:
        year += 2000
    if not month:
        return None
    return month, year


def quarter_end(qname: str) -> date | None:
    parsed = parse_quarter(qname)
    if not parsed:
        return None
    month, year = parsed
    return date(year, month, calendar.monthrange(year, month)[1])


def last_quarter_end(today: date | None = None) -> date:
    """Period-end of the last completed calendar quarter (the SHP photo date)."""
    today = today or date.today()
    q_month = ((today.month - 1) // 3) * 3
    if q_month == 0:
        month, year = 12, today.year - 1
    else:
        month, year = q_month, today.year
    return date(year, month, calendar.monthrange(year, month)[1])


def shp_qid_for(when: date) -> int:
    """BSE SHP quarter id for a period-end date (June 2016 = 90)."""
    if when.month in _Q_MONTHS:
        month, year = when.month, when.year
    else:
        month = ((when.month - 1) // 3) * 3
        if month == 0:
            month, year = 12, when.year - 1
        else:
            year = when.year
    return 90 + (year - 2016) * 4 + {3: -1, 6: 0, 9: 1, 12: 2}[month]


def recent_shp_qids(n: int = 4, today: date | None = None) -> list[int]:
    """BSE quarter ids ending at the last calendar quarter (June 2016 = 90)."""
    end = last_quarter_end(today)
    qid = 90 + (end.year - 2016) * 4 + {3: -1, 6: 0, 9: 1, 12: 2}[end.month]
    return [qid - i for i in range(n) if qid - i > 0]


def quarter_label(month: int, year: int) -> str:
    return f"{_Q_NAMES.get(month, str(month))} {year}"


def shift_quarter(month: int, year: int, steps_back: int) -> tuple[int, int]:
    idx = _Q_MONTHS.index(month) if month in _Q_MONTHS else 1
    idx -= steps_back
    year += idx // 4
    idx %= 4
    return _Q_MONTHS[idx], year


def _seg_rank(type_str: str) -> int:
    t = (type_str or "").lower()
    if "equity t+1" in t:
        return 0
    if "equity t+0" in t:
        return 3
    if "deriv" in t:
        return 4
    if "equity" in t:
        return 1
    return 2


def _fold_and(val: str) -> str:
    return re.sub(r"\s+", " ", re.sub(r"\band\b", " ", val or "")).strip()


# BSE quote-search drops '&' names. Map the seven that still miss.
_BSE_NAME_ALIASES = {
    "ajmera realty infra india": ("AJMERA", "513349"),
    "chambal fertilizers chemicals": ("CHAMBLFERT", "500085"),
    "foods inns": ("FOODSIN", "507552"),
    "kavveri defence wireless technologies": ("KAVDEFENCE", "590041"),
    "taj gvk hotels resorts": ("TAJGVK", "532390"),
    "yatharth hospital trauma care services": ("YATHARTH", "543950"),
    "zenith steel pipes industries": ("ZENITHSTL", "531845"),
}


def _bse_alias(name: str) -> tuple[str, str] | None:
    return _BSE_NAME_ALIASES.get(_fold_and(norm_name(name)))


def _name_rank(scripname: str, target: str) -> int:
    n = norm_name(scripname)
    if n and n == target:
        return 0
    if n and _fold_and(n) == _fold_and(target):
        return 0
    if n and (n.startswith(target) or target.startswith(n) or target in n or n in target):
        return 1
    fn, ft = _fold_and(n), _fold_and(target)
    if fn and (fn.startswith(ft) or ft.startswith(fn) or ft in fn or fn in ft):
        return 1
    return 2


def _initials_ok(short: list[str], long: list[str]) -> bool:
    """Single-letter middles (M, H) may stand for a full middle name."""
    if not short:
        return True
    for tok in short:
        if len(tok) == 1:
            if not any(other.startswith(tok) for other in long):
                return False
        elif tok not in long and not any(len(other) == 1 and tok.startswith(other) for other in long):
            if long and not any(other[0] == tok[0] for other in long):
                return False
    return True


def _token_eq(a: str, b: str) -> bool:
    """Exact token, or a simple singular/plural (Investment vs Investments)."""
    return a == b or a == b + "s" or b == a + "s"


def _clean_filing_name(val: str) -> str:
    s = re.sub(r"\s*\(\s*revised\s*\)\s*", " ", str(val or ""), flags=re.I)
    return re.sub(r"\s+", " ", s).strip()


def _norm_event_type(val: str) -> str | None:
    t = str(val or "").strip().lower()
    if not t:
        return None
    # "Release of invoked shares" is a return of stock, not a new invoke.
    if "releas" in t and "invoc" in t:
        return "Release of invoked shares"
    if "invoc" in t:
        return "Invocation"
    if "releas" in t:
        return "Release"
    if "creat" in t or t == "pledge":
        return "Creation"
    return str(val).strip() or None


def _event_kind(ev: dict) -> str:
    return (_norm_event_type(ev.get("event_type") or "") or "").lower()


def _event_dedupe_key(ev: dict) -> tuple:
    shares = ev.get("event_shares")
    qty = int(round(shares)) if shares is not None else 0
    return (_event_kind(ev), ev.get("event_date") or "", qty)


def _entity_parts(val: str) -> tuple[list[str], bool]:
    """Person parts plus drop 'and' / 'on behalf of' filler.

    Used to score a filing as one entity. Do not split Food and Farms or
    A & B (on behalf of X Trust) into two people.
    """
    tokens, is_huf = _person_parts(val)
    tokens = [t for t in tokens if t not in _FILLER]
    return tokens, is_huf


def _people_match_score(a: str, b: str) -> float:
    ta, ha = _person_parts(a)
    tb, hb = _person_parts(b)
    if not ta or not tb:
        return 0.0
    if ha != hb:
        return 0.0
    if ta == tb:
        return 100.0
    if not _token_eq(ta[0], tb[0]) or not _token_eq(ta[-1], tb[-1]):
        return 0.0
    ma = ta[1:-1]
    mb = tb[1:-1]
    # Extra initials on one side are common (Raaja Kanwar vs RAAJA R S KANWAR).
    if ma and mb and (not _initials_ok(ma, mb) or not _initials_ok(mb, ma)):
        return 0.0
    return 92.0 if ma or mb else 100.0


def match_score(a: str, b: str) -> float:
    """How well two promoter strings refer to the same person or vehicle. 0–100."""
    ea, ha = _entity_parts(a)
    eb, hb = _entity_parts(b)
    if ea and eb and ha == hb and ea == eb:
        return 100.0
    best = _people_match_score(a, b)
    # Slash only: "A / B" joint lines. Do not split on 'and' / '&' — that
    # turns Crosslink Food and Farms into two names, and the Adani family
    # trust into Gautam the individual.
    for src, other in ((a, b), (b, a)):
        parts = [p.strip() for p in re.split(r"\s*/\s*", str(src or "")) if p.strip()]
        if len(parts) < 2:
            continue
        best = max(best, max(_people_match_score(p, other) for p in parts))
    return best


def _pledged_value_cr(row: dict) -> float | None:
    """Company-level pledged book in Rs cr: pledged shares × last close."""
    for key in (
        "pledgedValueCr",
        "totPromoterSharesValue",
        "valPromoterShares",
        "valPromoterEncumbered",
        # NSE JSON: last-quarter encumbered value in Rs cr (name is misleading).
        "noOfPledgeShare",
    ):
        n = to_num(row.get(key))
        if n is not None:
            return n
    best = None
    for key, val in row.items():
        kl = re.sub(r"\s+", " ", str(key or "").lower())
        if "value" not in kl:
            continue
        if "depository" in kl or "demat" in kl or "public" in kl:
            continue
        n = to_num(val)
        if n is None:
            continue
        if "last quarter" in kl or "encumb" in kl or "(x)" in kl:
            return n
        if "cr" in kl or "rs" in kl:
            best = n
    return best


def snapshot_from_nse_row(row: dict) -> dict:
    """Company-level pledge figures from NSE's pledged-data tape.

    totPromoterShares / percPromoterShares = last SHP (promoter pledges only).
    numSharesPledged / percSharesPledged = depository pledged shares as % of demat,
    which is not the same as '% of promoter holding'.
    """
    promoter_shares = to_num(row.get("totPromoterHolding"))
    shp_pledged = to_num(row.get("totPromoterShares"))
    shp_pct = to_num(row.get("percPromoterShares"))
    if shp_pct is None and promoter_shares and promoter_shares > 0 and shp_pledged is not None:
        shp_pct = round(shp_pledged / promoter_shares * 100, 2)
    return {
        "promoter_holding_pct": to_num(row.get("percPromoterHolding")),
        "promoter_shares": promoter_shares,
        "shp_pledged_shares": shp_pledged,
        "shp_pledged_pct_of_promoter": shp_pct,
        "depository_pledged_shares": to_num(row.get("numSharesPledged")),
        "depository_pledged_pct_of_demat": to_num(row.get("percSharesPledged")),
        "depository_as_of": str(row.get("broadcastDt") or "").strip() or None,
        "shp_period": str(row.get("shp") or "").strip() or None,
        "pledged_value_cr": _pledged_value_cr(row),
    }


class NseLive:
    def __init__(self) -> None:
        self.s = requests.Session()
        self.s.headers.update(
            {
                "User-Agent": UA,
                "Accept": "application/json, text/plain, */*",
                "Accept-Language": "en-US,en;q=0.9",
                "Referer": "https://www.nseindia.com/companies-listing/corporate-filings-pledged-data",
            }
        )
        self._lock = threading.Lock()
        self._pledged_source = ""
        self._pledged_asof = ""
        self._pledged_mem: list[dict] | None = None

    def _warm(self) -> None:
        pages = [
            "https://www.nseindia.com/companies-listing/corporate-filings-pledged-data",
            "https://www.nseindia.com/companies-listing/corporate-filings-regulation-31",
        ]
        for url in pages:
            try:
                r = self.s.get(url, timeout=8)
                if r.status_code == 200:
                    return
            except requests.RequestException:
                continue

    def get(self, url: str, retries: int = 2, sleep: float = 0.6) -> requests.Response:
        with self._lock:
            last: Any = None
            for i in range(retries):
                try:
                    r = self.s.get(url, timeout=15)
                    if r.status_code in {401, 403} or "Resource not found" in r.text[:80]:
                        self._warm()
                        time.sleep(sleep * (i + 1))
                        last = r
                        continue
                    if r.status_code == 200:
                        return r
                    last = r
                except requests.RequestException as e:
                    last = e
                time.sleep(sleep * (i + 1))
            raise RuntimeError(f"NSE GET failed {url}: {last}")

    def _row_from_nse_payload(self, row: dict) -> dict | None:
        name = str(row.get("comName") or "").strip()
        if not name:
            return None
        rec = snapshot_from_nse_row(row)
        rec["name"] = name
        rec["nse_symbol"] = nse_symbol_for(name, row.get("symbol"))
        rec["isin"] = str(row.get("isin") or row.get("ISIN") or "").strip()
        return rec

    def _rows_from_nse_payload(self, data) -> list[dict]:
        raw = data["data"] if isinstance(data, dict) else data
        out = []
        for row in raw or []:
            rec = self._row_from_nse_payload(row)
            if rec:
                out.append(rec)
        return out

    def _pledged_from_json(self) -> list[dict]:
        return self._rows_from_nse_payload(self.get(_NSE_PLEDGED_JSON).json())

    def _pledged_from_csv(self) -> list[dict]:
        r = self.get(_NSE_PLEDGED_CSV)
        text = r.content.decode("utf-8-sig", errors="replace")
        out = []
        for row in csv.DictReader(StringIO(text)):
            payload = {
                "comName": _csv_col(row, "name of company") or "",
                "symbol": "",
                "isin": "",
                "totPromoterHolding": _csv_col(row, "total promoter holding no"),
                "percPromoterHolding": _csv_col(row, "total promoter holding %"),
                "totPromoterShares": _csv_col(row, "last quarter no. of shares"),
                "percPromoterShares": _csv_col(row, "last quarter % of promoter"),
                "numSharesPledged": _csv_col(row, "depository system no. of shares pledged"),
                "percSharesPledged": _csv_col(row, "pledge / demat"),
                "broadcastDt": _csv_col(row, "broadcast date"),
                "pledgedValueCr": _csv_col(row, "last quarter values")
                    or _csv_col(row, "encumbered as of last quarter values"),
            }
            rec = self._row_from_nse_payload(payload)
            if rec:
                out.append(rec)
        return out

    def _save_pledged_cache(self, rows: list[dict]) -> None:
        try:
            _NSE_PLEDGED_CACHE.write_text(json.dumps(rows), encoding="utf-8")
        except OSError:
            pass

    def _load_pledged_cache(self) -> list[dict]:
        try:
            if not _NSE_PLEDGED_CACHE.exists():
                return []
            data = json.loads(_NSE_PLEDGED_CACHE.read_text(encoding="utf-8"))
            return data if isinstance(data, list) else []
        except (OSError, ValueError):
            return []

    def _load_last_good_nse(self) -> list[dict]:
        """Live tape is empty: use last processed cache, else newest data/raw dump."""
        processed = self._load_pledged_cache()
        if processed and isinstance(processed[0], dict) and processed[0].get("name"):
            return processed
        if not _NSE_RAW_DIR.is_dir():
            return []
        for path in sorted(_NSE_RAW_DIR.glob("pledged_*.json"), reverse=True):
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                continue
            rows = self._rows_from_nse_payload(data)
            if not rows:
                continue
            m = re.search(r"pledged_(\d{4}-\d{2}-\d{2})", path.name)
            if m:
                self._pledged_asof = m.group(1)
            return rows
        return []

    def _pledged_rows(self) -> list[dict]:
        if self._pledged_mem:
            return self._pledged_mem
        out: list[dict] = []
        source = ""
        self._pledged_asof = ""
        try:
            out = self._pledged_from_json()
            if out:
                source = "json"
        except Exception:
            out = []
        if not out:
            try:
                out = self._pledged_from_csv()
                if out:
                    source = "csv"
            except Exception:
                out = []
        if out:
            out.sort(key=lambda x: x["name"].lower())
            self._save_pledged_cache(out)
            self._pledged_source = source
            self._pledged_mem = out
            return out
        cached = self._load_last_good_nse()
        if cached:
            cached.sort(key=lambda x: x["name"].lower())
            self._pledged_source = "cache"
            self._pledged_mem = cached
            return cached
        self._pledged_source = "empty"
        return []

    def pledged_companies(self) -> list[dict]:
        """Last-SHP promoter pledges only. New creates after that photo stay off the list."""
        best: dict[str, dict] = {}
        for rec in self._pledged_rows():
            shares = rec.get("shp_pledged_shares") or 0
            if shares <= 0:
                continue
            prom = rec.get("promoter_shares") or 0
            pct = round(shares / prom * 100, 2) if prom > 0 else rec.get("shp_pledged_pct_of_promoter")
            row = {
                "name": rec["name"],
                "nse_symbol": nse_symbol_for(rec["name"], rec.get("nse_symbol")),
                "isin": rec.get("isin") or "",
                "shp_pledged_shares": shares,
                "shp_pledged_pct_of_promoter": pct,
                "promoter_holding_pct": rec.get("promoter_holding_pct"),
                "pledged_value_cr": rec.get("pledged_value_cr"),
                "list_reason": "shp",
            }
            key = rec.get("nse_symbol") or norm_name(rec["name"])
            prev = best.get(key)
            if prev is None or shares > (prev.get("shp_pledged_shares") or 0):
                best[key] = row
        out = list(best.values())
        out.sort(key=lambda x: x["name"].lower())
        return out

    def pledged_snapshot(self, name: str) -> dict | None:
        target = norm_name(name)
        best = None
        for rec in self._pledged_rows():
            if norm_name(rec["name"]) != target:
                continue
            if best is None or (rec.get("shp_pledged_shares") or 0) > (best.get("shp_pledged_shares") or 0):
                best = rec
        return best

    def _sast_from_payload(self, payload) -> list[dict]:
        rows = payload.get("data") if isinstance(payload, dict) else payload
        out = []
        for row in rows or []:
            if not isinstance(row, dict):
                continue
            event_date = parse_date(row.get("eventDetailsToDate") or row.get("event_date"))
            broadcast = parse_date(row.get("broadcastdate") or row.get("broadcast"))
            kind = row.get("eventDetailsType") or row.get("event_type")
            encumbered = _num_field(row, "encumbHolding")
            if encumbered is None:
                encumbered = _num_field(row, "pre_event_encumbered_shares")
            # NSE puts total promoter holding in preeventHolding; already
            # encumbered is encumbHolding. An "Invocation" with 0 already
            # encumbered is the lender returning previously invoked shares.
            if _norm_event_type(kind) == "Invocation" and encumbered == 0:
                kind = "Release of invoked shares"
            else:
                kind = _norm_event_type(kind) or str(kind or "").strip()
            out.append(
                {
                    "nse_symbol": str(row.get("symbol") or row.get("nse_symbol") or "").strip().upper(),
                    "company": str(row.get("companyName") or row.get("company") or "").strip(),
                    "promoter": str(row.get("promoterName") or row.get("promoter") or "").strip(),
                    "event_type": kind,
                    "encumbrance_type": str(
                        row.get("eventDetailsTypeEncumb") or row.get("encumbrance_type") or ""
                    ).strip(),
                    "lender": str(row.get("eventDetailsEntity") or row.get("lender") or "").strip(),
                    "event_shares": _num_field(row, "eventDetailsHolding", "event_shares"),
                    "event_pct_equity": _num_field(row, "eventDetailsPerc", "event_pct_equity"),
                    "event_date": iso(event_date),
                    "event_date_label": fmt_date(event_date),
                    "broadcast": iso(broadcast),
                    "broadcast_label": fmt_date(broadcast),
                    "attachment": row.get("attachment") or None,
                    "pre_event_encumbered_shares": encumbered,
                    "pre_event_encumbered_pct": _num_field(
                        row, "encumbPerc", "pre_event_encumbered_pct"
                    ),
                    "post_event_encumbered_shares": _num_field(
                        row, "postEventHolding", "post_event_encumbered_shares"
                    ),
                    "post_event_encumbered_pct": _num_field(
                        row, "postEventHoldingPerc", "post_event_encumbered_pct"
                    ),
                    "source": row.get("source") or "NSE",
                    "_sort": event_date or broadcast or date.min,
                }
            )
        out.sort(key=lambda x: x["_sort"], reverse=True)
        return out

    def events(self, lookback_days: int = EVENT_LOOKBACK_DAYS) -> list[dict]:
        frm = (date.today() - timedelta(days=lookback_days)).strftime("%d-%m-%Y")
        to = date.today().strftime("%d-%m-%Y")
        url = (
            "https://www.nseindia.com/api/corporate-pledgedata-sast3132"
            f"?index=equities&from_date={frm}&to_date={to}"
        )
        return self._sast_from_payload(self.get(url).json())

    def price_history(self, symbol: str, start: date, end: date) -> list[dict]:
        symbol = (symbol or "").strip().upper()
        if not symbol:
            return []
        by_day: dict[date, dict] = {}
        for series in NSE_SERIES:
            url = (
                "https://www.nseindia.com/api/historicalOR/generateSecurityWiseHistoricalData"
                f"?from={start.strftime('%d-%m-%Y')}&to={end.strftime('%d-%m-%Y')}"
                f"&symbol={urllib.parse.quote(symbol)}&type=priceVolumeDeliverable&series={series}"
            )
            try:
                payload = self.get(url).json()
            except Exception:
                continue
            records = payload if isinstance(payload, list) else (payload.get("data") or [])
            for rec in records:
                try:
                    day = datetime.strptime(rec["mTIMESTAMP"], "%d-%b-%Y").date()
                    close = to_num(rec.get("CH_CLOSING_PRICE"))
                    qty = to_num(rec.get("CH_TOT_TRADED_QTY"))
                    value = to_num(rec.get("CH_TOT_TRADED_VAL"))
                except (KeyError, TypeError, ValueError):
                    continue
                if not close or close <= 0 or not qty or qty <= 0:
                    continue
                delivered = rec.get("COP_DELIV_QTY")
                by_day.setdefault(
                    day,
                    {
                        "day": day,
                        "close": close,
                        "quantity": qty,
                        "value": value or 0.0,
                        "delivery_qty": None
                        if delivered in (None, "", "-")
                        else to_num(delivered),
                    },
                )
            if by_day and max(by_day) >= end - timedelta(days=MAX_SESSION_GAP_DAYS):
                break
        return sorted(by_day.values(), key=lambda x: x["day"])


def _rows_from_bse_pledge_csv(text: str) -> list[dict]:
    out = []
    for rec in csv.DictReader(StringIO(text)):
        status = str(_csv_col(rec, "status") or "").strip().lower()
        if status == "suspended":
            continue
        shares = to_num(_csv_col(rec, "promoter shares encumbered", "no of shares")) or 0
        if shares <= 0:
            continue
        raw_name = _csv_col(rec, "name of the company") or ""
        name, scrip = _parse_bse_list_name(raw_name)
        if not name:
            continue
        pct = to_num(_csv_col(rec, "% of promoter shares"))
        prom = to_num(_csv_col(rec, "total promoter holding", "no of shares"))
        if pct is None and prom and prom > 0:
            pct = round(shares / prom * 100, 2)
        value = (
            to_num(_csv_col(rec, "last quarter", "value"))
            or to_num(_csv_col(rec, "encumbered", "values"))
            or to_num(_csv_col(rec, "value", "cr"))
        )
        out.append(
            {
                "name": name,
                "nse_symbol": "",
                "isin": "",
                "bse_scripcode": scrip,
                "shp_pledged_shares": shares,
                "shp_pledged_pct_of_promoter": pct,
                "pledged_value_cr": value,
                "list_reason": "shp",
                "list_exchange": "BSE",
            }
        )
    out.sort(key=lambda x: x["name"].lower())
    return out


class BseLive:
    def __init__(self) -> None:
        self.s = requests.Session()
        self.s.headers.update(
            {
                "User-Agent": UA,
                "Accept": "application/json, text/plain, */*",
                "Accept-Language": "en-US,en;q=0.9",
                "Referer": "https://www.bseindia.com/",
                "Origin": "https://www.bseindia.com",
            }
        )
        self._lock = threading.Lock()
        self._pledge_list: list[dict] | None = None
        self._pledged_source = ""

    def _download_aspx_csv(self, url: str) -> str:
        page = self.s.get(
            url,
            timeout=70,
            headers={"Accept": "text/html,application/xhtml+xml", "Referer": "https://www.bseindia.com/"},
        )
        page.raise_for_status()
        fields = _hidden_inputs(page.text or "")
        if not fields.get("__VIEWSTATE"):
            raise RuntimeError(f"BSE page had no form: {url}")
        fields["__EVENTTARGET"] = "ctl00$ContentPlaceHolder1$lnkDownload"
        fields["__EVENTARGUMENT"] = ""
        dl = self.s.post(
            url,
            data=fields,
            timeout=120,
            headers={
                "Accept": "text/csv,application/octet-stream,*/*",
                "Referer": url,
                "Origin": "https://beta.bseindia.com",
            },
        )
        dl.raise_for_status()
        return dl.content.decode("utf-8-sig", errors="replace")

    def _warm(self) -> None:
        for url in (
            "https://www.bseindia.com/",
            "https://www.bseindia.com/corporates/Sharehold_Searchnew.aspx",
        ):
            try:
                self.s.get(url, timeout=8)
            except requests.RequestException:
                continue

    def _looks_json(self, resp: requests.Response) -> bool:
        text = (resp.text or "").lstrip()[:80]
        if not text:
            return False
        if text[0] in "{[":
            return True
        ctype = (resp.headers.get("Content-Type") or "").lower()
        return "json" in ctype and "<" not in text[:20]

    def get_json(self, url: str, retries: int = 2) -> Any:
        with self._lock:
            last: Any = None
            for i in range(retries):
                try:
                    r = self.s.get(url, timeout=15)
                    if r.status_code in {401, 403} or not self._looks_json(r):
                        self._warm()
                        time.sleep(0.8 * (i + 1))
                        last = r
                        continue
                    r.raise_for_status()
                    return r.json()
                except (requests.RequestException, ValueError) as e:
                    last = e
                    self._warm()
                    time.sleep(0.8 * (i + 1))
            raise RuntimeError(f"BSE GET failed {url}: {last}")

    def _plain_json(self, url: str, timeout: float = 8) -> Any:
        """Fresh GET. Do not reuse the BSE homepage session; those cookies
        and the connection pool hang after a failed warm and then Open dies.
        Cap in-flight BSE JSON calls so SHP walks do not starve market cap.
        """
        last: Any = None
        for i in range(3):
            with _BSE_GATE:
                try:
                    r = requests.get(
                        url,
                        headers={
                            "User-Agent": UA,
                            "Accept": "application/json, text/plain, */*",
                            "Accept-Language": "en-US,en;q=0.9",
                            "Referer": "https://www.bseindia.com/",
                        },
                        timeout=timeout,
                    )
                    r.raise_for_status()
                    if not self._looks_json(r):
                        raise RuntimeError("BSE returned a non-JSON body")
                    return r.json()
                except Exception as e:
                    last = e
            time.sleep(0.35 * (i + 1))
        raise last if last else RuntimeError(f"BSE GET failed {url}")

    def search(
        self,
        name: str,
        symbol: str | None = None,
        isin: str | None = None,
        scripcode: str | None = None,
    ) -> dict | None:
        symbol = (symbol or "").strip().upper()
        isin = (isin or "").strip().upper()
        scripcode = str(scripcode or "").strip()
        alias = _bse_alias(name)
        if scripcode:
            ticker = symbol or ((alias[0] if alias else "") or "")
            return {
                "scripcode": scripcode,
                "bse_ticker": ticker,
                "name": name,
                "isin": isin,
            }
        if alias:
            ticker, code = alias
            return {
                "scripcode": code,
                "bse_ticker": symbol or ticker,
                "name": name,
                "isin": isin,
            }
        queries = []
        no_amp = re.sub(r"\s+", " ", re.sub(r"\s*&\s*", " ", name)).strip()
        words = [
            w for w in re.split(r"\s+", no_amp)
            if w.lower() not in {"and", "limited", "ltd", "the", "of"}
        ]
        short = " ".join(words[:2]) if len(words) >= 2 else ""
        for q in (
            symbol,
            short,
            no_amp,
            name,
            re.sub(r"\s+(limited|ltd)\.?$", "", no_amp, flags=re.IGNORECASE).strip(),
        ):
            q = re.sub(r"\s+", " ", str(q or "")).strip()
            if q and q.lower() not in {x.lower() for x in queries}:
                queries.append(q)
        target = norm_name(name)
        best = None
        best_key = (99, 99)
        for q in queries:
            url = (
                "https://api.bseindia.com/BseIndiaAPI/api/GetQuoteAllSearchDatabeta/w"
                f"?searchString={urllib.parse.quote(q, safe='')}"
            )
            try:
                payload = self._plain_json(url)
            except Exception:
                continue
            hits = payload if isinstance(payload, list) else (
                (payload or {}).get("Table") or (payload or {}).get("data") or []
            )
            if not isinstance(hits, list):
                continue
            loose = bool(short and q == short)
            for hit in hits:
                tick = str(hit.get("shortName") or "").strip().upper()
                hit_isin = str(hit.get("Isin") or "").strip().upper()
                hit_code = str(hit.get("strSricpCode") or "").strip()
                if scripcode and hit_code == scripcode:
                    name_rank = -2
                elif symbol and tick == symbol:
                    name_rank = -1
                elif isin and hit_isin == isin:
                    name_rank = -1
                else:
                    name_rank = _name_rank(hit.get("scripName") or "", target)
                if loose and name_rank > 1:
                    continue
                key = (name_rank, _seg_rank(hit.get("Type") or ""))
                if key < best_key:
                    best_key = key
                    best = hit
            if best and best_key[0] <= 0:
                break
        if not best:
            return None
        return {
            "scripcode": str(best.get("strSricpCode") or "").strip(),
            "bse_ticker": str(best.get("shortName") or "").strip().upper(),
            "name": str(best.get("scripName") or "").strip(),
            "isin": str(best.get("Isin") or "").strip(),
        }

    def pledged_companies(self) -> list[dict]:
        """BSE last-quarter promoter pledges only. Live tape first, saved list as fallback."""
        if self._pledge_list:
            return self._pledge_list
        with self._lock:
            if self._pledge_list:
                return self._pledge_list
            cached = self._load_pledged_cache()
            out: list[dict] = []
            last_err = ""
            try:
                text = self._download_aspx_csv(_BSE_PLEDGE_LIST_URL)
                out = _rows_from_bse_pledge_csv(text)
            except Exception as e:
                last_err = str(e)
                out = []
            if out:
                self._save_pledged_cache(out)
                self._pledge_list = out
                self._pledged_source = "live"
                return out
            if cached:
                self._pledge_list = cached
                self._pledged_source = "cache"
                return cached
            self._pledged_source = "empty"
            raise RuntimeError(last_err or "BSE pledge list returned no companies.")

    def _save_pledged_cache(self, rows: list[dict]) -> None:
        try:
            _BSE_PLEDGED_CACHE.write_text(json.dumps(rows), encoding="utf-8")
        except OSError:
            pass

    def _load_pledged_cache(self) -> list[dict]:
        try:
            if not _BSE_PLEDGED_CACHE.exists():
                return []
            data = json.loads(_BSE_PLEDGED_CACHE.read_text(encoding="utf-8"))
            return data if isinstance(data, list) else []
        except (OSError, ValueError):
            return []

    def market_cap_cr(self, scripcode: str) -> float | None:
        url = f"https://api.bseindia.com/BseIndiaAPI/api/StockTrading/w?scripcode={scripcode}"
        try:
            payload = self._plain_json(url, timeout=10) or {}
        except Exception:
            return None
        return _extract_mcap_cr(payload)

    def scrip_header(self, scripcode: str) -> dict | None:
        url = (
            "https://api.bseindia.com/BseIndiaAPI/api/getScripHeaderData/w"
            f"?Debtflag=&scripcode={scripcode}"
        )
        try:
            payload = self._plain_json(url) or {}
        except Exception:
            return None
        header = payload.get("Header") if isinstance(payload, dict) else None
        if not isinstance(header, dict):
            return None
        curr = payload.get("CurrRate") if isinstance(payload.get("CurrRate"), dict) else {}
        return {
            "cmp": to_num(header.get("LTP") or curr.get("LTP")),
            "open": to_num(header.get("Open")),
            "previous_close": to_num(header.get("PrevClose")),
            "quote_time": header.get("Ason") or None,
        }

    def _quarter_meta(self, qid: int, payload: dict | None = None) -> dict:
        parsed = self._quarter_from_payload(payload or {})
        if parsed:
            return parsed
        month, year = shift_quarter(6, 2016, int(90 - qid))
        return {
            "qid": qid,
            "qname": quarter_label(month, year),
            "filed": None,
            "company": "",
        }

    def _try_shp_qid(self, scripcode: str, qid: int) -> tuple[str, dict | None]:
        """Return ('ok', quarter), ('empty', None), or ('timeout', None).

        Promoter table only. The security-beta SHP URL often hangs; calling it
        after an empty quarter was aborting Open before older filings were tried.
        """
        url = (
            "https://api.bseindia.com/BseIndiaAPI/api/Corp_shpPromoterNGroup_ng/w"
            f"?SCRIPCODE={scripcode}&QtrCode={float(qid):.2f}"
        )
        try:
            payload = self._plain_json(url) or {}
        except requests.Timeout:
            return "timeout", None
        except Exception:
            return "empty", None
        if self._holders_from_payload(payload) or self._quarter_from_payload(payload):
            return "ok", self._quarter_meta(qid, payload)
        return "empty", None

    def latest_quarter(self, scripcode: str, hint: date | None = None) -> dict | None:
        """Newest filed BSE SHP for this scrip.

        Probe a short qid list and stop after two timeouts. A long yearly walk
        against a dead BSE API is what made Open hang for every name.
        """
        qids: list[int] = []
        if hint:
            hq = shp_qid_for(hint)
            qids.extend(hq + i for i in range(-1, 2) if hq + i > 0)
        qids.extend(recent_shp_qids(12))
        seen: set[int] = set()
        ordered = []
        for qid in qids:
            if qid not in seen:
                seen.add(qid)
                ordered.append(qid)

        timeouts = 0
        started = time.time()
        for qid in ordered:
            if time.time() - started > 15:
                return None
            status, found = self._try_shp_qid(scripcode, qid)
            if found:
                return found
            if status == "timeout":
                timeouts += 1
                if timeouts >= 3:
                    return None
        return None

    @staticmethod
    def _quarter_from_payload(payload: dict) -> dict | None:
        rows = []
        for key in ("Table", "Table4", "Table3"):
            tbl = payload.get(key) if isinstance(payload, dict) else None
            if isinstance(tbl, list):
                rows.extend(r for r in tbl if isinstance(r, dict))
        best = None
        best_qid = -1.0
        for row in rows:
            qid = row.get("Qtr_Id") or row.get("fld_quarterid")
            if qid is None:
                continue
            qid = float(qid)
            if qid > best_qid:
                best_qid = qid
                best = row
        if not best:
            return None
        qname = (best.get("Fld_qtrname") or best.get("fld_quartername") or "").strip()
        return {
            "qid": best.get("Qtr_Id") or best.get("fld_quarterid"),
            "qname": qname or quarter_label(*shift_quarter(6, 2016, int(90 - best_qid))),
            "filed": parse_date(best.get("Fld_AuthoriseDate")),
            "company": (best.get("slongname") or "").strip(),
        }

    @staticmethod
    def statement_urls(scripcode: str, qid, qname: str) -> tuple[str, str]:
        q = f"{float(qid):.2f}"
        enc = urllib.parse.quote(qname)
        base = "https://www.bseindia.com/corporates/"
        return (
            f"{base}ShpPromoterNGroup?scripcd={scripcode}&qtrid={q}&QtrName={enc}",
            f"{base}shpPublicShareholder?scripcd={scripcode}&qtrid={q}&QtrName={enc}",
        )

    @staticmethod
    def _largest_table(payload) -> list:
        big, blen = None, -1
        for k, v in (payload or {}).items():
            if isinstance(v, list) and len(v) > blen:
                big, blen = k, len(v)
        return (payload.get(big) if big else []) or []

    def promoter_table(self, scripcode: str, qid) -> list[dict]:
        """Named promoter / promoter-group rows for one quarter, including zero pledge."""
        return self._shp_holders(scripcode, qid)

    def _shp_holders(self, scripcode: str, qid) -> list[dict]:
        key = (str(scripcode), int(float(qid)))
        with _SHP_CACHE_LOCK:
            cached = _SHP_CACHE.get(key)
        if cached is not None:
            return cached
        url = (
            "https://api.bseindia.com/BseIndiaAPI/api/Corp_shpPromoterNGroup_ng/w"
            f"?SCRIPCODE={scripcode}&QtrCode={float(qid):.2f}"
        )
        try:
            payload = self._plain_json(url, timeout=12) or {}
            rows = self._holders_from_payload(payload)
        except Exception:
            rows = []
        if rows:
            with _SHP_CACHE_LOCK:
                _SHP_CACHE[key] = rows
        return rows

    def _holders_from_payload(self, payload) -> list[dict]:
        out = []
        for row in self._largest_table(payload):
            parsed = self._holder_from_shp(row)
            if parsed:
                out.append(parsed)
        return out

    @staticmethod
    def _holder_from_shp(row: dict) -> dict | None:
        name = re.sub(r"\s+", " ", (row.get("Fld_ShareHolderName") or "").strip())
        if not name:
            return None
        kind = (row.get("FLd_ShareholderType") or "").strip()
        if kind and kind not in ("Promoter", "Promoter Group"):
            return None
        pledged_shares = to_num(row.get("Fld_PledgeEncumberedNoOfShares")) or 0.0
        pledged_pct = to_num(row.get("Fld_PledgeEncumberedPercentage"))
        holding_shares = to_num(row.get("Fld_TotalNoOfShares"))
        holding_pct = to_num(row.get("Fld_TotalPercentageOf_A_B_C2"))
        if pledged_pct is None and holding_shares and holding_shares > 0:
            pledged_pct = round(pledged_shares / holding_shares * 100, 2)
        return {
            "name": name,
            "category": kind or "Promoter",
            "holding_shares": holding_shares,
            "holding_pct": holding_pct,
            "pledged_shares": pledged_shares,
            "pledged_pct_of_holding": pledged_pct,
            "ndu_shares": to_num(row.get("Fld_NDUNoOfShares")),
            "other_encumbered_shares": to_num(row.get("Fld_OtherencumbrancesNoOfShares")),
        }

    def pledged_promoters(self, scripcode: str, qid) -> list[dict]:
        out = []
        for row in self.promoter_table(scripcode, qid):
            pledged_shares = row.get("pledged_shares") or 0.0
            pledged_pct = row.get("pledged_pct_of_holding")
            if pledged_shares <= 0 and (pledged_pct is None or pledged_pct <= 0):
                continue
            item = dict(row)
            item["history"] = []
            item["later"] = []
            item["shp_walk"] = []
            item["shp_walk_note"] = None
            out.append(item)
        out.sort(key=lambda x: -(x["pledged_shares"] or 0))
        return out

    def shp_company_totals(self, scripcode: str, qid) -> dict:
        """Company-level promoter holding and pledged qty from the BSE SHP photo."""
        rows = self.promoter_table(scripcode, qid)
        hold_sh = sum((r.get("holding_shares") or 0) for r in rows)
        hold_pct = sum((r.get("holding_pct") or 0) for r in rows)
        pledged = sum((r.get("pledged_shares") or 0) for r in rows)
        pct = round(pledged / hold_sh * 100, 2) if hold_sh > 0 else None
        return {
            "promoter_holding_pct": round(hold_pct, 2) if hold_pct else None,
            "shp_pledged_shares": pledged or None,
            "shp_pledged_pct_of_promoter": pct,
        }

    def sast_events(self, scripcode: str, lookback_days: int = EVENT_LOOKBACK_DAYS) -> list[dict]:
        """BSE SAST Reg 31 create / invoke / release for one scrip."""
        url = (
            "https://api.bseindia.com/BseIndiaAPI/api/SASTPledge/w"
            f"?scripcode={scripcode}"
        )
        try:
            payload = self._plain_json(url) or {}
        except Exception:
            return []
        rows = payload.get("Table") if isinstance(payload, dict) else None
        if not isinstance(rows, list):
            return []
        cutoff = date.today() - timedelta(days=lookback_days)
        ticker_re = re.compile(r"/([A-Z0-9]{1,20})/\d+/?$", re.I)
        out = []
        for row in rows:
            if not isinstance(row, dict):
                continue
            event_date = parse_date(row.get("Date"))
            broadcast = parse_date(row.get("FLD_DateOfReporting") or row.get("Fld_AuthoriseDate"))
            when = event_date or broadcast
            if when and when < cutoff:
                continue
            kind = _norm_event_type(row.get("Fld_DetailsOfEvents"))
            if not kind:
                continue
            promoter = _clean_filing_name(row.get("Fld_PromoterName") or row.get("Fld_nameofAc") or "")
            if not promoter:
                continue
            page = str(row.get("NSUrl") or row.get("URL") or "")
            tick = ticker_re.search(page)
            out.append(
                {
                    "nse_symbol": (tick.group(1).upper() if tick else ""),
                    "bse_scripcode": str(row.get("FLD_ScripCode") or scripcode).strip(),
                    "company": str(row.get("Fld_NameOfTC") or "").strip(),
                    "promoter": promoter,
                    "event_type": kind,
                    "encumbrance_type": str(row.get("Fld_Details") or "").strip() or None,
                    "lender": str(row.get("ENTITY") or "").strip() or None,
                    "event_shares": to_num(row.get("Fld_Present_No")) or to_num(row.get("Fld_NoOfShares")),
                    "event_pct_equity": to_num(row.get("Fld_Present_Percent")),
                    "event_date": iso(event_date),
                    "event_date_label": fmt_date(event_date),
                    "broadcast": iso(broadcast),
                    "broadcast_label": fmt_date(broadcast),
                    "attachment": None,
                    "post_event_encumbered_shares": to_num(row.get("Fld_TotalShares_No")),
                    "post_event_encumbered_pct": to_num(row.get("Fld_TotalShares_Percent")),
                    "source": "BSE",
                    "_sort": event_date or broadcast or date.min,
                }
            )
        out.sort(key=lambda x: x["_sort"], reverse=True)
        return out

    def shp_walk(self, scripcode: str, latest: dict, promoters: list[dict]) -> None:
        """Attach earlier SHP photos under each pledged promoter."""
        if not promoters:
            return
        latest_qid = int(float(latest["qid"]))
        parsed = parse_quarter(latest.get("qname") or "")
        if not parsed:
            return
        ref_month, ref_year = parsed
        ids = _walk_qids(latest_qid)
        latest_rows = self._shp_holders(scripcode, latest_qid)
        for p in promoters:
            hit = _match_holder(
                p["name"],
                latest_rows,
                category=p.get("category"),
                pledged_shares=p.get("pledged_shares"),
                holding_shares=p.get("holding_shares"),
            )
            if hit and hit.get("category"):
                p["category"] = hit["category"]
        tables: dict[int, list[dict]] = {
            latest_qid: latest_rows or [dict(p) for p in promoters]
        }

        def load(qid: int):
            if qid == latest_qid:
                return
            tables[qid] = self._shp_holders(scripcode, qid)

        with ThreadPoolExecutor(max_workers=3) as pool:
            list(pool.map(load, ids))

        missed = [qid for qid in ids if qid != latest_qid and not tables.get(qid)]
        neighbors = []
        seen = set(tables) | set(ids)
        for qid in missed:
            for alt in (qid - 1, qid + 1):
                if 0 < alt < latest_qid and alt not in seen:
                    neighbors.append(alt)
                    seen.add(alt)
        extra = _gap_qids(ids, promoters, tables) + neighbors
        extra = [qid for qid in extra if qid not in tables]
        if extra:
            with ThreadPoolExecutor(max_workers=3) as pool:
                list(pool.map(load, extra))

        ordered = sorted((qid for qid, rows in tables.items() if rows), reverse=True)
        for p in promoters:
            points = []
            for qid in ordered:
                month, year = shift_quarter(ref_month, ref_year, latest_qid - qid)
                qname = quarter_label(month, year)
                row = _match_holder(
                    p["name"],
                    tables.get(qid) or [],
                    category=p.get("category"),
                    pledged_shares=p.get("pledged_shares"),
                    holding_shares=p.get("holding_shares"),
                )
                present = row is not None
                points.append(
                    {
                        "qid": qid,
                        "quarter": qname,
                        "quarter_end_label": fmt_date(quarter_end(qname)),
                        "present": present,
                        "pledged_shares": (row or {}).get("pledged_shares") if present else None,
                        "pledged_pct_of_holding": (row or {}).get("pledged_pct_of_holding") if present else None,
                        "holding_shares": (row or {}).get("holding_shares") if present else None,
                        "holding_pct": (row or {}).get("holding_pct") if present else None,
                    }
                )
            present_pts = [pt for pt in points if pt.get("present")]
            for i, pt in enumerate(present_pts):
                nxt = present_pts[i + 1] if i + 1 < len(present_pts) else None
                if (
                    nxt
                    and pt.get("pledged_shares") is not None
                    and nxt.get("pledged_shares") is not None
                ):
                    pt["delta_shares"] = pt["pledged_shares"] - nxt["pledged_shares"]
                else:
                    pt["delta_shares"] = None
            compact = _compact_walk(present_pts)
            p["shp_walk_note"] = _walk_note(points, bool(p.get("history")))
            shown = compact[1:] if compact and compact[0].get("qid") == latest_qid else compact
            p["shp_walk"] = [{k: v for k, v in pt.items() if k != "qid"} for pt in shown]


def _walk_qids(latest_qid: int) -> list[int]:
    """Yearly SHP samples behind the latest photo, plus one extra to hit empty filings."""
    ids = []
    qid = latest_qid - SHP_WALK_STEP
    stop = latest_qid - SHP_WALK_MAX
    while qid >= stop and qid > 0:
        ids.append(qid)
        qid -= SHP_WALK_STEP
    return ids


def _pledged_key(name: str, rows: list[dict], **hint):
    row = _match_holder(name, rows, **hint)
    if not rows:
        return ("empty", None)
    if not row:
        return ("absent", None)
    return ("in", row.get("pledged_shares") or 0.0)


def _gap_qids(ids: list[int], promoters: list[dict], tables: dict[int, list[dict]]) -> list[int]:
    ordered = sorted(tables, reverse=True)
    extra = []
    wanted = set(ids)
    for newer, older in zip(ordered, ordered[1:]):
        if newer - older <= 1:
            continue
        if newer not in wanted and older not in wanted:
            continue
        changed = False
        for p in promoters:
            hint = {
                "category": p.get("category"),
                "pledged_shares": p.get("pledged_shares"),
                "holding_shares": p.get("holding_shares"),
            }
            if _pledged_key(p["name"], tables.get(newer) or [], **hint) != _pledged_key(
                p["name"], tables.get(older) or [], **hint
            ):
                changed = True
                break
        if changed:
            extra.extend(qid for qid in range(newer - 1, older, -1) if qid not in tables)
    return extra


def _norm_holder_cat(val: str | None) -> str:
    s = re.sub(r"[^a-z]+", " ", str(val or "").lower()).strip()
    if "group" in s:
        return "promoter group"
    if "promoter" in s:
        return "promoter"
    return ""


def _match_holder(
    name: str,
    rows: list[dict],
    category: str | None = None,
    pledged_shares=None,
    holding_shares=None,
) -> dict | None:
    """Same name can appear twice (Promoter vs Promoter Group). Stay on the
    original tag; if that tag is missing that quarter, keep the pledged book
    that matches the photo, not the zero-pledge twin.
    """
    scored = []
    for row in rows:
        s = match_score(name, row.get("name") or "")
        if s >= 65:
            scored.append((s, row))
    if not scored:
        return None
    top = max(s for s, _ in scored)
    cands = [r for s, r in scored if s == top]
    if len(cands) == 1:
        return cands[0]
    want = _norm_holder_cat(category)
    if want:
        same = [r for r in cands if _norm_holder_cat(r.get("category")) == want]
        if same:
            cands = same
    want_pledged = to_num(pledged_shares) or 0.0
    if want_pledged > 0:
        pledged = [r for r in cands if (r.get("pledged_shares") or 0) > 0]
        if pledged:
            cands = pledged
    elif want_pledged == 0:
        zero = [r for r in cands if not (r.get("pledged_shares") or 0)]
        if zero:
            cands = zero
    want_hold = to_num(holding_shares)
    if want_hold and want_hold > 0:
        cands = sorted(cands, key=lambda r: abs((r.get("holding_shares") or 0) - want_hold))
    return cands[0]


def _same_shp(a: dict, b: dict) -> bool:
    return (
        a.get("present") == b.get("present")
        and a.get("pledged_shares") == b.get("pledged_shares")
        and a.get("holding_shares") == b.get("holding_shares")
        and a.get("pledged_pct_of_holding") == b.get("pledged_pct_of_holding")
    )


def _compact_walk(points: list[dict]) -> list[dict]:
    """Keep change quarters, plus the oldest quarter that still matches the current run.

    Otherwise a pledge that went to 0 and later came back is folded into the latest
    photo, and the table looks like 'previous = 0' against a pledged latest.
    """
    if not points:
        return []
    out = [points[0]]
    last_same = 0
    for i, pt in enumerate(points[1:], 1):
        if _same_shp(pt, out[-1]):
            last_same = i
            continue
        if last_same > 0 and points[last_same] is not out[-1]:
            out.append(points[last_same])
        out.append(pt)
        last_same = i
    return out


def _walk_note(points: list[dict], has_diary: bool) -> str | None:
    present = [pt for pt in points if pt.get("present")]
    if len(present) < 2:
        return "No earlier SHP row for this person." if len(points) > 1 else None
    newest = present[0]
    qty = newest.get("pledged_shares") or 0
    since = newest
    for pt in present[1:]:
        if (pt.get("pledged_shares") or 0) == qty:
            since = pt
        else:
            break
    since_q = since.get("quarter")
    if since is present[-1] and qty:
        note = f"Unchanged since {since_q}."
        if not has_diary:
            note += " Older than the 3-year diary."
        return note
    if qty and since is not newest:
        return f"This pledged qty is in the SHP from {since_q}. Earlier quarters were different."
    return None


def _window(sessions: list[dict], as_of: date, days: int):
    cutoff = as_of - timedelta(days=days)
    inside = [s for s in sessions if s["day"] > cutoff]
    earlier = [s for s in sessions if s["day"] <= cutoff]
    return inside, (earlier[-1] if earlier else None)


def _measure(sessions: list[dict]) -> dict:
    latest = sessions[-1]
    as_of = latest["day"]
    delivered_sessions = [s for s in sessions if s.get("delivery_qty") is not None]
    deliv_as_of = delivered_sessions[-1]["day"] if delivered_sessions else None
    measures: dict[str, Any] = {
        "as_of": as_of.isoformat(),
        "as_of_label": fmt_date(as_of),
        "close": round(latest["close"], 2),
    }
    for label, days in METRIC_WINDOWS:
        inside, reference = _window(sessions, as_of, days)
        if not inside:
            continue
        traded_value = sum(s["value"] for s in inside)
        traded_qty = sum(s["quantity"] for s in inside)
        if reference and reference["close"] > 0:
            change = latest["close"] / reference["close"] - 1
            measures[f"return_{label}_pct"] = round(change * 100, 2)
        measures[f"adtv_{label}_cr"] = round(traded_value / len(inside) / CRORE, 2)
        if traded_qty > 0:
            measures[f"vwap_{label}"] = round(traded_value / traded_qty, 2)
        if deliv_as_of:
            deliv_inside, _ = _window(sessions, deliv_as_of, days)
            disclosed = [s for s in deliv_inside if s.get("delivery_qty") is not None]
            disclosed_qty = sum(s["quantity"] for s in disclosed)
            if disclosed_qty > 0:
                delivered = sum(s["delivery_qty"] or 0 for s in disclosed)
                measures[f"delivery_{label}_pct"] = round(delivered / disclosed_qty * 100, 2)
        measures[f"sessions_{label}"] = len(inside)
    return measures


def _extract_mcap_cr(payload) -> float | None:
    """BSE quote payloads put full market cap in crores under a few key names."""
    blobs = [payload]
    if isinstance(payload, dict):
        for key in ("StockObj", "Header", "Table", "Table1", "CurrRate"):
            nest = payload.get(key)
            if isinstance(nest, dict):
                blobs.append(nest)
            elif isinstance(nest, list) and nest and isinstance(nest[0], dict):
                blobs.append(nest[0])
    keys = (
        "MktCapFull", "MktCapFF", "FullMktCap", "Mktcap", "MktCap",
        "MarketCap", "MKT_CAP", "mktcapfull",
    )
    for blob in blobs:
        if not isinstance(blob, dict):
            continue
        for key in keys:
            n = to_num(blob.get(key))
            if n and n > 0:
                if n > 1e8:
                    n = n / CRORE
                return round(n, 2)
    return None


def _mcap_from_holdings(promoters: list[dict], cmp) -> float | None:
    cmp = to_num(cmp)
    if not cmp or cmp <= 0:
        return None
    estimates = []
    for p in promoters or []:
        shares = to_num(p.get("holding_shares"))
        pct = to_num(p.get("holding_pct"))
        if shares and shares > 0 and pct and pct > 0:
            estimates.append(shares / (pct / 100.0) * cmp / CRORE)
    if not estimates:
        return None
    return round(sorted(estimates)[len(estimates) // 2], 2)


def yahoo_market_cap_cr(symbol: str) -> float | None:
    symbol = (symbol or "").strip().upper()
    if not symbol:
        return None
    url = (
        "https://query1.finance.yahoo.com/v7/finance/quote"
        f"?symbols={urllib.parse.quote(symbol, safe='-.')}.NS"
    )
    try:
        r = requests.get(
            url,
            headers={"User-Agent": UA, "Accept": "application/json"},
            timeout=12,
        )
        r.raise_for_status()
        row = ((r.json().get("quoteResponse") or {}).get("result") or [None])[0] or {}
    except Exception:
        return None
    n = to_num(row.get("marketCap"))
    return round(n / CRORE, 2) if n and n > 0 else None


def _pct_move(cmp: float, base) -> float | None:
    if cmp is None or not base or base <= 0:
        return None
    return round((cmp / base - 1) * 100, 2)


def _live_fields(cmp, open_price, previous_close, quote_time=None, source=None) -> dict:
    fields = {
        "cmp": round(cmp, 2) if cmp and cmp > 0 else None,
        "open": round(open_price, 2) if open_price and open_price > 0 else None,
        "previous_close": round(previous_close, 2) if previous_close and previous_close > 0 else None,
        "quote_time": quote_time or None,
        "quote_source": source,
        "intraday_return_pct": None,
        "daily_return_pct": None,
        "live_volume": None,
    }
    if fields["cmp"] is None:
        return fields
    fields["intraday_return_pct"] = _pct_move(fields["cmp"], fields["open"])
    fields["daily_return_pct"] = _pct_move(fields["cmp"], fields["previous_close"])
    return fields


def yahoo_nse_quote(symbol: str) -> dict | None:
    symbol = (symbol or "").strip().upper()
    if not symbol:
        return None
    url = (
        "https://query1.finance.yahoo.com/v8/finance/chart/"
        f"{urllib.parse.quote(symbol, safe='-.')}.NS?interval=1d&range=1d"
    )
    r = requests.get(
        url,
        headers={"User-Agent": UA, "Accept": "application/json"},
        timeout=20,
    )
    r.raise_for_status()
    result = ((r.json().get("chart") or {}).get("result") or [None])[0] or {}
    meta = result.get("meta") or {}
    bars = ((result.get("indicators") or {}).get("quote") or [{}])[0]
    opens = bars.get("open") or []
    volumes = bars.get("volume") or []
    open_price = to_num(meta.get("regularMarketOpen"))
    if (not open_price or open_price <= 0) and opens:
        open_price = to_num(opens[-1])
    volume = to_num(meta.get("regularMarketVolume"))
    if (not volume or volume <= 0) and volumes:
        volume = to_num(volumes[-1])
    stamp = meta.get("regularMarketTime")
    quote_time = None
    if stamp:
        try:
            instant = datetime.fromtimestamp(int(stamp), timezone.utc)
            quote_time = instant.astimezone(_IST).strftime("%d %b %Y %H:%M IST")
        except (TypeError, ValueError, OSError):
            quote_time = None
    fields = _live_fields(
        to_num(meta.get("regularMarketPrice")),
        open_price,
        to_num(meta.get("chartPreviousClose") or meta.get("previousClose")),
        quote_time,
        "NSE (Yahoo)",
    )
    fields["live_volume"] = int(volume) if volume and volume > 0 else None
    return fields if fields.get("cmp") else None


_NSE_BHAV_FULL = (
    "https://nsearchives.nseindia.com/products/content/sec_bhavdata_full_{stamp}.csv"
)


def nse_archives_history(symbol: str, calendar_days: int = 45) -> list[dict]:
    """Security-wise delivery from NSE daily bhav copies (nsearchives)."""
    symbol = (symbol or "").strip().upper()
    if not symbol:
        return []
    days: list[date] = []
    d = date.today()
    stop = d - timedelta(days=calendar_days)
    while d >= stop:
        if d.weekday() < 5:
            days.append(d)
        d -= timedelta(days=1)
    headers = {
        "User-Agent": UA,
        "Accept": "text/csv,*/*",
        "Referer": "https://nsearchives.nseindia.com/",
    }

    def one(day: date) -> dict | None:
        url = _NSE_BHAV_FULL.format(stamp=day.strftime("%d%m%Y"))
        try:
            r = requests.get(url, headers=headers, timeout=12)
        except requests.RequestException:
            return None
        if r.status_code != 200 or "SYMBOL" not in (r.text[:40] or ""):
            return None
        hits: list[dict] = []
        for rec in csv.DictReader(StringIO(r.text)):
            if str(_csv_col(rec, "symbol") or "").strip().upper() != symbol:
                continue
            series = str(_csv_col(rec, "series") or "").strip().upper()
            if series not in NSE_SERIES:
                continue
            close = to_num(_csv_col(rec, "close_price") or _csv_col(rec, "close"))
            qty = to_num(_csv_col(rec, "ttl_trd_qnty") or _csv_col(rec, "traded", "qty"))
            if not close or close <= 0 or not qty or qty <= 0:
                continue
            lacs = to_num(_csv_col(rec, "turnover_lacs"))
            delivered = _csv_col(rec, "deliv", "qty") or _csv_col(rec, "delivery", "qty")
            when = parse_date(_csv_col(rec, "date1") or _csv_col(rec, "date")) or day
            hits.append(
                {
                    "day": when,
                    "close": close,
                    "quantity": qty,
                    "value": (lacs * 100_000) if lacs else close * qty,
                    "delivery_qty": None if delivered in (None, "", "-") else to_num(delivered),
                    "_series": series,
                }
            )
        for pref in NSE_SERIES:
            for row in hits:
                if row.get("_series") == pref:
                    row.pop("_series", None)
                    return row
        return None

    def one_retry(day: date) -> dict | None:
        for _ in range(2):
            got = one(day)
            if got:
                return got
        return None

    out: list[dict] = []
    with ThreadPoolExecutor(max_workers=8) as pool:
        for fut in [pool.submit(one_retry, day) for day in days]:
            try:
                row = fut.result()
            except Exception:
                continue
            if row:
                out.append(row)
    out.sort(key=lambda x: x["day"])
    return out


def _merge_market_sessions(yahoo: list[dict], nse_rows: list[dict]) -> list[dict]:
    """Prefer NSE bhav rows (they carry delivery). Fill gaps from Yahoo."""
    if not nse_rows:
        return yahoo
    by_nse = {s["day"]: s for s in nse_rows}
    by_y = {s["day"]: s for s in yahoo}
    out = []
    for day in sorted(set(by_nse) | set(by_y)):
        if day in by_nse:
            rec = dict(by_nse[day])
            rec.pop("_series", None)
            out.append(rec)
        else:
            out.append(dict(by_y[day]))
    return out


def yahoo_nse_history(symbol: str) -> list[dict]:
    """Daily OHLCV from Yahoo .NS — used for return / ADTV / VWAP when NSE history is down."""
    symbol = (symbol or "").strip().upper()
    if not symbol:
        return []
    url = (
        "https://query1.finance.yahoo.com/v8/finance/chart/"
        f"{urllib.parse.quote(symbol, safe='-.')}.NS?interval=1d&range=3mo"
    )
    r = requests.get(
        url,
        headers={"User-Agent": UA, "Accept": "application/json"},
        timeout=20,
    )
    r.raise_for_status()
    result = ((r.json().get("chart") or {}).get("result") or [None])[0] or {}
    stamps = result.get("timestamp") or []
    bars = ((result.get("indicators") or {}).get("quote") or [{}])[0]
    closes = bars.get("close") or []
    volumes = bars.get("volume") or []
    out = []
    for ts, close, vol in zip(stamps, closes, volumes):
        px = to_num(close)
        qty = to_num(vol)
        if not ts or not px or px <= 0 or not qty or qty <= 0:
            continue
        try:
            day = datetime.fromtimestamp(int(ts), timezone.utc).astimezone(_IST).date()
        except (TypeError, ValueError, OSError):
            continue
        out.append(
            {
                "day": day,
                "close": px,
                "quantity": qty,
                "value": px * qty,
                "delivery_qty": None,
            }
        )
    out.sort(key=lambda x: x["day"])
    return out


def market_data(nse: NseLive, bse: BseLive, nse_symbol: str, bse_code: str) -> dict:
    quote_box: dict = {}
    yahoo_box: dict = {}
    nse_box: dict = {}

    def load_quote():
        try:
            quote_box["value"] = yahoo_nse_quote(nse_symbol)
        except Exception as e:
            quote_box["error"] = str(e)

    def load_yahoo():
        try:
            yahoo_box["value"] = yahoo_nse_history(nse_symbol)
        except Exception as e:
            yahoo_box["error"] = str(e)

    def load_nse():
        try:
            nse_box["value"] = nse_archives_history(nse_symbol)
        except Exception as e:
            nse_box["error"] = str(e)

    threads = [
        threading.Thread(target=load_quote),
        threading.Thread(target=load_yahoo),
        threading.Thread(target=load_nse),
    ]
    for t in threads:
        t.start()
    threads[0].join(20)
    threads[1].join(20)
    threads[2].join(40)

    quote = quote_box.get("value")
    if not (quote and quote.get("cmp")) and bse_code:
        header = bse.scrip_header(bse_code)
        if header and header.get("cmp"):
            quote = _live_fields(
                header.get("cmp"),
                header.get("open"),
                header.get("previous_close"),
                header.get("quote_time"),
                "BSE",
            )
    if not quote:
        quote = _live_fields(None, None, None)

    result = dict(quote)
    sessions = _merge_market_sessions(yahoo_box.get("value") or [], nse_box.get("value") or [])
    if sessions:
        result.update(_measure(sessions))
    return result


def _event_cutoff_date(ev: dict) -> date | None:
    return parse_date(ev.get("event_date")) or parse_date(ev.get("broadcast"))


def _public_event(ev: dict) -> dict:
    return {k: v for k, v in ev.items() if not k.startswith("_")}


def attach_events(promoters: list[dict], events: list[dict], cutoff: date | None) -> tuple[list[dict], list[dict]]:
    """SHP names are the photo. Diary is filings on or before the photo as-of
    date (quarter-end). Later filings sit in section 2. Filing date is not the split.
    """
    unmatched_history: list[dict] = []
    post_shp: list[dict] = []
    for p in promoters:
        p.setdefault("history", [])
        p.setdefault("later", [])
    for ev in events:
        when = _event_cutoff_date(ev)
        after = bool(cutoff and when and when > cutoff)
        best_i, best = -1, 0.0
        for i, p in enumerate(promoters):
            score = match_score(ev.get("promoter") or "", p["name"])
            if score > best:
                best, best_i = score, i
        matched = promoters[best_i]["name"] if best >= 65 else None
        row = _public_event(ev)
        row["matched_promoter"] = matched
        if after:
            post_shp.append(row)
            if matched:
                promoters[best_i]["later"].append(row)
        elif matched:
            promoters[best_i]["history"].append(row)
        else:
            unmatched_history.append(row)
    for p in promoters:
        p["history"].sort(key=lambda x: x.get("event_date") or x.get("broadcast") or "", reverse=True)
        p["later"].sort(key=lambda x: x.get("event_date") or x.get("broadcast") or "", reverse=True)
    post_shp.sort(key=lambda x: x.get("event_date") or x.get("broadcast") or "", reverse=True)
    return unmatched_history, post_shp


def filter_company_events(
    events: list[dict],
    nse_symbol: str,
    company: str,
    bse_scripcode: str | None = None,
) -> list[dict]:
    sym = (nse_symbol or "").strip().upper()
    scrip = str(bse_scripcode or "").strip()
    target = norm_name(company)
    out = []
    for ev in events:
        if scrip and str(ev.get("bse_scripcode") or "").strip() == scrip:
            out.append(ev)
        elif sym and ev.get("nse_symbol") == sym:
            out.append(ev)
        elif target and norm_name(ev.get("company") or "") == target:
            out.append(ev)
    return out


def _same_filing_name(a: str, b: str) -> bool:
    if match_score(a, b) >= 65:
        return True
    ta, _ = _person_parts(a)
    tb, _ = _person_parts(b)
    return bool(ta and tb and _token_eq(ta[0], tb[0]) and _token_eq(ta[-1], tb[-1]))


def merge_reg31_events(nse_events: list[dict], bse_events: list[dict]) -> list[dict]:
    """Keep NSE rows, add BSE-only creates/releases, collapse the same filing."""
    used = set()
    out = []
    for ev in nse_events:
        row = dict(ev)
        row.setdefault("source", "NSE")
        key = _event_dedupe_key(row)
        mate = None
        for i, bev in enumerate(bse_events):
            if i in used or _event_dedupe_key(bev) != key:
                continue
            if not _same_filing_name(row.get("promoter") or "", bev.get("promoter") or ""):
                continue
            mate = i
            break
        if mate is not None:
            used.add(mate)
            extra = bse_events[mate]
            row["source"] = "NSE+BSE"
            nse_tok = _person_parts(row.get("promoter") or "")[0]
            bse_tok = _person_parts(extra.get("promoter") or "")[0]
            if len(bse_tok) > len(nse_tok) and extra.get("promoter"):
                row["promoter"] = extra["promoter"]
            if not row.get("lender") and extra.get("lender"):
                row["lender"] = extra["lender"]
            if row.get("post_event_encumbered_shares") is None:
                row["post_event_encumbered_shares"] = extra.get("post_event_encumbered_shares")
            if row.get("event_pct_equity") is None:
                row["event_pct_equity"] = extra.get("event_pct_equity")
        out.append(row)
    for i, bev in enumerate(bse_events):
        if i not in used:
            row = dict(bev)
            row.setdefault("source", "BSE")
            out.append(row)
    out.sort(key=lambda x: x.get("_sort") or date.min, reverse=True)
    return out


_BSE_GATE = threading.Semaphore(3)
_SHP_CACHE: dict[tuple[str, int], list[dict]] = {}
_SHP_CACHE_LOCK = threading.Lock()
_lock = threading.Lock()
_nse: NseLive | None = None
_bse: BseLive | None = None


def clients() -> tuple[NseLive, BseLive]:
    global _nse, _bse
    with _lock:
        if _nse is None:
            _nse = NseLive()
        if _bse is None:
            _bse = BseLive()
        return _nse, _bse


def _list_name_key(name: str) -> str:
    """Fold spelling variants so Fertilisers / Fertilizers still match."""
    return norm_name(name).replace("z", "s")


def merge_company_lists(nse_rows: list[dict], bse_rows: list[dict]) -> list[dict]:
    """NSE names first; add BSE-only pledgers and attach BSE scrip codes."""
    by_name: dict[str, dict] = {}
    out: list[dict] = []
    for row in nse_rows:
        item = dict(row)
        item.setdefault("nse_symbol", "")
        item.setdefault("bse_scripcode", "")
        item.setdefault("isin", "")
        item.setdefault("list_exchange", "NSE")
        out.append(item)
        key = _list_name_key(item.get("name") or "")
        if key:
            by_name[key] = item
    extras = []
    for row in bse_rows:
        key = _list_name_key(row.get("name") or "")
        hit = by_name.get(key) if key else None
        if hit:
            if row.get("bse_scripcode"):
                hit["bse_scripcode"] = row["bse_scripcode"]
            if row.get("isin") and not hit.get("isin"):
                hit["isin"] = row["isin"]
            if hit.get("list_exchange") == "NSE":
                hit["list_exchange"] = "NSE+BSE"
            if row.get("list_reason") == "shp":
                hit["list_reason"] = "shp"
                if row.get("shp_pledged_shares"):
                    hit["shp_pledged_shares"] = row["shp_pledged_shares"]
                if row.get("shp_pledged_pct_of_promoter") is not None:
                    hit["shp_pledged_pct_of_promoter"] = row["shp_pledged_pct_of_promoter"]
            bse_val = row.get("pledged_value_cr")
            nse_val = hit.get("pledged_value_cr")
            if bse_val is not None and (nse_val is None or bse_val > nse_val):
                hit["pledged_value_cr"] = bse_val
            continue
        extras.append(dict(row))
    out.extend(extras)
    out.sort(key=lambda x: (0 if x.get("list_reason") == "shp" else 1, x["name"].lower()))
    return out


def _last_close(nse: NseLive, bse: BseLive, row: dict) -> float | None:
    """Last available close, not live CMP."""
    sym = (row.get("nse_symbol") or "").strip().upper()
    if sym:
        try:
            q = yahoo_nse_quote(sym)
            px = (q or {}).get("previous_close") or (q or {}).get("cmp")
            if px:
                return px
        except Exception:
            pass
    code = str(row.get("bse_scripcode") or "").strip()
    if code:
        try:
            h = bse.scrip_header(code)
            px = (h or {}).get("previous_close") or (h or {}).get("cmp")
            if px:
                return px
        except Exception:
            pass
    return None


def fill_post_shp_values(rows: list[dict]) -> None:
    """Value leftover Reg 31 names from event book × last close."""
    nse, bse = clients()
    need = [
        r for r in rows
        if r.get("list_reason") == "post_shp"
        and not r.get("pledged_value_cr")
        and (r.get("event_shares") or 0) > 0
        and (r.get("nse_symbol") or r.get("bse_scripcode"))
    ]
    if not need:
        return

    def one(row: dict) -> None:
        px = _last_close(nse, bse, row)
        if not px:
            return
        row["pledged_value_cr"] = round((row.get("event_shares") or 0) * px / CRORE, 2)

    with ThreadPoolExecutor(max_workers=8) as pool:
        list(pool.map(one, need))


def list_pledged_companies() -> tuple[list[dict], dict]:
    nse, bse = clients()
    nse_box: dict = {}
    bse_box: dict = {}

    def load_nse():
        try:
            nse_box["value"] = nse.pledged_companies()
        except Exception as e:
            nse_box["error"] = str(e)

    def load_bse():
        try:
            bse_box["value"] = bse.pledged_companies()
        except Exception as e:
            bse_box["error"] = str(e)

    t1 = threading.Thread(target=load_nse)
    t2 = threading.Thread(target=load_bse)
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    nse_rows = nse_box.get("value") or []
    bse_rows = bse_box.get("value") or []
    if "error" in nse_box:
        print("NSE company list failed:", nse_box["error"], flush=True)
    if "error" in bse_box:
        print("BSE company list failed:", bse_box["error"], flush=True)
    if "value" not in nse_box and "value" not in bse_box:
        raise RuntimeError(nse_box.get("error") or bse_box.get("error") or "Could not load company lists.")
    merged = [
        r for r in merge_company_lists(nse_rows, bse_rows)
        if (r.get("shp_pledged_shares") or 0) > 0 and r.get("list_reason") != "post_shp"
    ]
    for r in merged:
        if not r.get("nse_symbol"):
            r["nse_symbol"] = nse_symbol_for(r.get("name") or "")
    meta = {
        "nse_ok": "value" in nse_box,
        "bse_ok": "value" in bse_box,
        "nse_source": getattr(nse, "_pledged_source", ""),
        "bse_source": getattr(bse, "_pledged_source", ""),
        "nse_error": nse_box.get("error") or "",
        "bse_error": bse_box.get("error") or "",
        "nse_names": len(nse_rows),
        "bse_names": len(bse_rows),
        "total": len(merged),
        "merged": len(merged),
        "shp": sum(1 for x in merged if x.get("list_reason") != "post_shp"),
        "after": sum(1 for x in merged if x.get("list_reason") == "post_shp"),
        "nse_only": sum(1 for x in merged if x.get("list_exchange") == "NSE"),
        "bse_only": sum(1 for x in merged if x.get("list_exchange") == "BSE"),
        "both": sum(1 for x in merged if x.get("list_exchange") == "NSE+BSE"),
    }
    src = meta["nse_source"]
    asof = getattr(nse, "_pledged_asof", "") or ""
    meta["nse_asof"] = asof
    if src == "empty":
        meta["nse_ok"] = False
        meta["nse_error"] = "NSE pledged-data returned no companies."
    elif src == "cache":
        if asof:
            try:
                d = datetime.strptime(asof, "%Y-%m-%d").date()
                label = f"{d.day} {d.strftime('%b')} {d.year}"
            except ValueError:
                label = asof
            meta["nse_error"] = (
                f"NSE pledged-data is still empty live; using the {label} snapshot."
            )
        else:
            meta["nse_error"] = "NSE pledged-data empty live; using the last saved NSE list."
    bse_src = meta.get("bse_source") or ""
    if bse_src == "empty" or (not bse_rows and "error" in bse_box):
        meta["bse_ok"] = False
        meta["bse_error"] = bse_box.get("error") or "BSE pledge list returned no companies."
    elif bse_src == "cache":
        meta["bse_error"] = "BSE pledge list missed live; using the last saved BSE list."
    return merged, meta


def _promoter_value_cr(company: dict, pledged_shares) -> float | None:
    total = to_num(company.get("shp_pledged_shares")) or 0
    val = to_num(company.get("pledged_value_cr"))
    sh = to_num(pledged_shares) or 0
    if val is None or total <= 0 or sh <= 0:
        return None
    return round(val * sh / total, 2)


def _promoters_one_company(company: dict) -> list[dict]:
    """Latest SHP pledged names only — no walk, no Reg 31, no market fetch."""
    _nse, bse = clients()
    name = (company.get("name") or "").strip()
    symbol = (company.get("nse_symbol") or "").strip()
    scrip = str(company.get("bse_scripcode") or "").strip()
    isin = (company.get("isin") or "").strip()
    quarter = ""
    promoters: list[dict] = []
    try:
        if not scrip:
            hit = bse.search(name, symbol=symbol or None, isin=isin or None)
            if hit and hit.get("scripcode"):
                scrip = str(hit["scripcode"])
        if scrip:
            q = bse.latest_quarter(scrip)
            if q:
                quarter = q.get("qname") or ""
                promoters = bse.pledged_promoters(scrip, q["qid"])
        if not promoters:
            photo = load_nse_shp_photo(name, symbol or None)
            if photo and photo.get("promoters"):
                promoters = photo["promoters"]
                quarter = photo.get("qname") or quarter
                if not scrip and photo.get("scripcode"):
                    scrip = str(photo["scripcode"])
    except Exception:
        return []
    out = []
    for p in promoters:
        sh = p.get("pledged_shares") or 0
        if sh <= 0:
            continue
        out.append(
            {
                "company": name,
                "nse_symbol": symbol,
                "bse_scripcode": scrip,
                "quarter": quarter,
                "promoter": p.get("name"),
                "category": p.get("category") or "",
                "holding_shares": p.get("holding_shares"),
                "holding_pct": p.get("holding_pct"),
                "pledged_shares": sh,
                "pledged_pct_of_holding": p.get("pledged_pct_of_holding"),
                "pledged_value_cr": _promoter_value_cr(company, sh),
            }
        )
    return out


def list_promoters_for_companies(companies: list[dict]) -> list[dict]:
    if not companies:
        return []
    workers = min(8, max(1, len(companies)))
    out: list[dict] = []
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for rows in pool.map(_promoters_one_company, companies):
            out.extend(rows)
    out.sort(
        key=lambda r: (
            (r.get("company") or "").lower(),
            -(r.get("pledged_shares") or 0),
        )
    )
    return out


_INVOKE_PUBLIC = (
    "nse_symbol",
    "company",
    "promoter",
    "event_type",
    "encumbrance_type",
    "lender",
    "event_shares",
    "event_pct_equity",
    "event_date",
    "event_date_label",
    "broadcast",
    "broadcast_label",
    "attachment",
    "pre_event_encumbered_shares",
    "pre_event_encumbered_pct",
    "post_event_encumbered_shares",
    "post_event_encumbered_pct",
    "source",
)


def _public_event(ev: dict) -> dict:
    return {k: ev.get(k) for k in _INVOKE_PUBLIC}


def _invoke_dedupe_key(ev: dict) -> tuple:
    shares = ev.get("event_shares")
    qty = int(round(shares)) if shares is not None else 0
    return (
        (ev.get("nse_symbol") or "").upper(),
        norm_name(ev.get("promoter") or ""),
        ev.get("event_date") or "",
        qty,
        (ev.get("lender") or "").strip().lower(),
    )


def _save_invoke_cache(rows: list[dict]) -> None:
    try:
        _NSE_INVOKE_CACHE.write_text(json.dumps(rows), encoding="utf-8")
    except OSError:
        pass


def _load_invoke_cache() -> list[dict]:
    try:
        if not _NSE_INVOKE_CACHE.exists():
            return []
        data = json.loads(_NSE_INVOKE_CACHE.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else []
    except (OSError, ValueError):
        return []


def _filter_invocations(rows: list[dict]) -> list[dict]:
    cutoff = date.today() - timedelta(days=EVENT_LOOKBACK_DAYS)
    out = []
    seen: set[tuple] = set()
    for ev in rows:
        if _norm_event_type(ev.get("event_type")) != "Invocation":
            continue
        when = parse_date(ev.get("event_date")) or parse_date(ev.get("broadcast"))
        if when and when < cutoff:
            continue
        if not str(ev.get("company") or "").strip():
            continue
        key = _invoke_dedupe_key(ev)
        if key in seen:
            continue
        seen.add(key)
        out.append(_public_event(ev))
    return out


def list_invoke_events() -> tuple[list[dict], dict]:
    """NSE Regulation 31 invocation filings. Newest first.

    This is the event tape, not the SHP pledged list: a name can appear here
    after the pledge has already gone to zero.
    """
    nse, _bse = clients()
    source = ""
    error = ""
    asof = ""
    rows: list[dict] = []
    live_box: dict = {}

    def load_live():
        try:
            got = nse.events()
            if got:
                live_box["value"] = got
                _save_invoke_cache(_filter_invocations(got))
        except Exception as e:
            live_box["error"] = str(e)

    live = threading.Thread(target=load_live)
    live.start()
    live.join(12)
    if live_box.get("value"):
        rows = live_box["value"]
        source = "live"
    else:
        error = live_box.get("error") or ""
        cached = _load_invoke_cache()
        if cached:
            rows = nse._sast_from_payload(cached)
            source = "cache"
        elif _NSE_RAW_DIR.is_dir():
            for path in sorted(_NSE_RAW_DIR.glob("events_*.json"), reverse=True):
                try:
                    data = json.loads(path.read_text(encoding="utf-8"))
                except (OSError, ValueError):
                    continue
                rows = nse._sast_from_payload(data)
                if not rows:
                    continue
                source = "snapshot"
                m = re.search(r"events_(\d{4}-\d{2}-\d{2})", path.name)
                asof = m.group(1) if m else ""
                break
    if not rows:
        if live.is_alive():
            live.join(20)
        if live_box.get("value"):
            rows = live_box["value"]
            source = "live"
    if not rows:
        raise RuntimeError(error or "Could not load Regulation 31 invocations.")
    invokes = _filter_invocations(rows)
    if source == "live":
        _save_invoke_cache(invokes)
    meta = {
        "source": source,
        "error": error,
        "lookback_days": EVENT_LOOKBACK_DAYS,
        "asof": asof,
        "count": len(invokes),
    }
    if source == "snapshot" and asof:
        try:
            d = datetime.strptime(asof, "%Y-%m-%d").date()
            label = f"{d.day} {d.strftime('%b')} {d.year}"
        except ValueError:
            label = asof
        meta["note"] = f"NSE Regulation 31 missed live; using the {label} snapshot."
    elif source == "cache":
        meta["note"] = "NSE Regulation 31 missed live; using the last saved invoke list."
    elif source == "live":
        meta["note"] = "NSE Regulation 31 invocation filings, last 3 years."
    return invokes, meta


def _xbrl_pct(val) -> float | None:
    n = to_num(val)
    if n is None:
        return None
    if 0 <= n <= 1:
        return round(n * 100, 2)
    return round(n, 2)


def _xbrl_local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def parse_shp_xbrl(xml_text: str) -> dict | None:
    """Named promoter rows from a BSE SHP XBRL instance (NSE archives copy)."""
    try:
        root = ET.fromstring(xml_text)
    except ET.ParseError:
        return None
    facts: dict[str, dict[str, str]] = {}
    company = ""
    scripcode = ""
    period_end = None
    for el in root:
        local = _xbrl_local(el.tag)
        if local == "context":
            ident = ""
            instant = None
            for child in el.iter():
                cl = _xbrl_local(child.tag)
                if cl == "identifier" and (child.text or "").strip().isdigit():
                    ident = (child.text or "").strip()
                elif cl == "instant":
                    instant = parse_date(child.text)
            if ident and not scripcode:
                scripcode = ident
            if el.attrib.get("id") == "MainI" and instant:
                period_end = instant
            continue
        if local in {"unit", "schemaRef"}:
            continue
        ctx = el.attrib.get("contextRef") or ""
        key = ctx[2:] if ctx.startswith("D_") else ctx
        bucket = facts.setdefault(key, {})
        bucket[local] = (el.text or "").strip()
        if local == "NameOfTheCompany" and el.text:
            company = el.text.strip()
    promoters = []
    for d in facts.values():
        holder = _clean_filing_name(d.get("NameOfTheShareholder") or "")
        if not holder:
            continue
        pledged_shares = to_num(d.get("NumberOfSharesEncumberedUnderPledged")) or 0.0
        pledged_pct = _xbrl_pct(d.get("EncumberedShareUnderPledgedAsPercentageOfTotalNumberOfShares"))
        holding_shares = to_num(d.get("NumberOfFullyPaidUpEquityShares") or d.get("NumberOfShares"))
        holding_pct = _xbrl_pct(d.get("ShareholdingAsAPercentageOfTotalNumberOfShares"))
        if pledged_shares <= 0 and (pledged_pct is None or pledged_pct <= 0):
            continue
        if pledged_pct is None and holding_shares and holding_shares > 0:
            pledged_pct = round(pledged_shares / holding_shares * 100, 2)
        promoters.append(
            {
                "name": holder,
                "holding_shares": holding_shares,
                "holding_pct": holding_pct,
                "pledged_shares": pledged_shares,
                "pledged_pct_of_holding": pledged_pct,
                "ndu_shares": to_num(d.get("NumberOfSharesEncumberedUnderNonDisposalUndertaking")),
                "other_encumbered_shares": None,
                "history": [],
                "later": [],
                "shp_walk": [],
                "shp_walk_note": None,
            }
        )
    promoters.sort(key=lambda x: -(x["pledged_shares"] or 0))
    if not period_end:
        return None
    if period_end.month in _Q_MONTHS:
        month, year = period_end.month, period_end.year
    else:
        month = ((period_end.month - 1) // 3) * 3
        year = period_end.year
        if month == 0:
            month, year = 12, period_end.year - 1
    return {
        "qid": shp_qid_for(period_end),
        "qname": quarter_label(month, year),
        "filed": None,
        "company": company,
        "scripcode": scripcode,
        "promoters": promoters,
        "period_end": period_end,
    }


_SHP_SYMBOLS: dict[str, str] | None = None


def _shp_symbol_map() -> dict[str, str]:
    """name → NSE ticker from the latest SHP master dump (live tape has no symbol)."""
    global _SHP_SYMBOLS
    if _SHP_SYMBOLS is not None:
        return _SHP_SYMBOLS
    out: dict[str, str] = {}
    files = sorted(_NSE_RAW_DIR.glob("shp_*.json"), reverse=True)
    if files:
        try:
            data = json.loads(files[0].read_text(encoding="utf-8"))
        except (OSError, ValueError):
            data = []
        for rec in data if isinstance(data, list) else []:
            sym = str(rec.get("symbol") or "").strip().upper()
            key = norm_name(rec.get("name") or "")
            if sym and key:
                out[key] = sym
    for path in sorted(_NSE_RAW_DIR.glob("equity_l_*.csv"), reverse=True):
        try:
            text = path.read_text(encoding="utf-8-sig")
        except OSError:
            continue
        for rec in csv.DictReader(StringIO(text)):
            sym = str(_csv_col(rec, "symbol") or rec.get("SYMBOL") or "").strip().upper()
            key = norm_name(_csv_col(rec, "name") or rec.get("NAME OF COMPANY") or "")
            if sym and key and key not in out:
                out[key] = sym
        break
    _SHP_SYMBOLS = out
    return out


def nse_symbol_for(name: str, symbol: str | None = None) -> str:
    sym = (symbol or "").strip().upper()
    if sym:
        return sym
    return _shp_symbol_map().get(norm_name(name), "")


def load_nse_shp_photo(name: str, symbol: str | None = None) -> dict | None:
    """Last SHP photo from NSE archives XBRL (same BSE taxonomy, not api.bseindia.com)."""
    target = norm_name(name)
    sym = (symbol or "").strip().upper()
    files = sorted(_NSE_RAW_DIR.glob("shp_*.json"), reverse=True)
    rows: list[dict] = []
    if files:
        try:
            data = json.loads(files[0].read_text(encoding="utf-8"))
            rows = data if isinstance(data, list) else []
        except (OSError, ValueError):
            rows = []
    row = None
    for rec in rows:
        rec_sym = str(rec.get("symbol") or "").strip().upper()
        if sym and rec_sym == sym:
            row = rec
            break
        if norm_name(rec.get("name") or "") == target:
            row = rec
            break
    url = str((row or {}).get("xbrl") or "").strip()
    if not url:
        return None
    try:
        r = requests.get(url, headers={"User-Agent": UA}, timeout=20)
        r.raise_for_status()
        parsed = parse_shp_xbrl(r.text)
    except Exception:
        return None
    if not parsed:
        return None
    parsed["xbrl_url"] = url
    parsed["nse_symbol"] = str((row or {}).get("symbol") or "").strip().upper()
    parsed["shp_date"] = (row or {}).get("date")
    return parsed


def load_company(
    name: str,
    symbol: str | None = None,
    scripcode: str | None = None,
    isin: str | None = None,
) -> dict:
    name = (name or "").strip()
    if not name:
        raise ValueError("Choose a company.")
    nse, bse = clients()

    events_box: dict = {}

    def load_events():
        try:
            events_box["value"] = nse.events()
        except Exception as e:
            events_box["error"] = str(e)

    ev_thread = threading.Thread(target=load_events)
    ev_thread.start()

    snap = nse.pledged_snapshot(name) or {}
    symbol = nse_symbol_for(name, symbol or snap.get("nse_symbol"))
    scripcode = str(scripcode or "").strip()
    isin = (isin or snap.get("isin") or "").strip().upper()
    photo = load_nse_shp_photo(name, symbol)
    if photo:
        symbol = symbol or photo.get("nse_symbol") or ""
        if not scripcode and photo.get("scripcode"):
            scripcode = str(photo["scripcode"])
    hit = bse.search(name, symbol=symbol, isin=isin or None, scripcode=scripcode or None)
    if (not hit or not hit.get("scripcode")) and scripcode:
        hit = {
            "scripcode": scripcode,
            "bse_ticker": symbol,
            "name": name,
            "isin": isin,
        }
    if not hit or not hit.get("scripcode"):
        ev_thread.join(5)
        raise RuntimeError(f"No BSE equity match for '{name}'.")
    scripcode = hit["scripcode"]
    bse_ev_box: dict = {}

    def load_bse_events():
        try:
            bse_ev_box["value"] = bse.sast_events(scripcode)
        except Exception as e:
            bse_ev_box["error"] = str(e)

    bse_ev_thread = threading.Thread(target=load_bse_events)
    bse_ev_thread.start()
    mcap = None
    try:
        mcap = bse.market_cap_cr(scripcode)
    except Exception:
        mcap = None
    used_xbrl = False
    promoters: list[dict] = []
    if photo:
        used_xbrl = True
        quarter = {
            "qid": photo["qid"],
            "qname": photo["qname"],
            "filed": parse_date(photo.get("shp_date")),
            "company": photo.get("company") or name,
        }
        promoters = photo.get("promoters") or []
    else:
        shp_hint = parse_date(snap.get("shp_period"))
        quarter = bse.latest_quarter(scripcode, hint=shp_hint)
        if not quarter:
            ev_thread.join(5)
            bse_ev_thread.join(5)
            raise RuntimeError(
                f"Could not load BSE shareholding pattern for {hit['name'] or name} "
                f"(scrip {scripcode}). NSE still shows a pledged %. Try Open again."
            )
        promoters = bse.pledged_promoters(scripcode, quarter["qid"])

    prom_url, pub_url = bse.statement_urls(scripcode, quarter["qid"], quarter["qname"])
    if used_xbrl and photo.get("xbrl_url"):
        prom_url = photo["xbrl_url"]

    walk_box: dict = {}

    def load_walk():
        try:
            bse.shp_walk(scripcode, quarter, promoters)
        except Exception as e:
            walk_box["error"] = str(e)

    walk_thread = threading.Thread(target=load_walk)
    walk_thread.start()

    nse_symbol = symbol or hit["bse_ticker"]
    ev_thread.join(8 if used_xbrl else 12)
    bse_ev_thread.join(5 if used_xbrl else 12)
    nse_company = filter_company_events(
        events_box.get("value") or [], nse_symbol, hit["name"] or name, scripcode
    )
    company_events = merge_reg31_events(nse_company, bse_ev_box.get("value") or [])

    photo_as_of = quarter_end(quarter["qname"]) or quarter.get("filed")
    unmatched, post_shp = attach_events(promoters, company_events, photo_as_of)

    market = market_data(nse, bse, nse_symbol, scripcode)
    walk_thread.join(75)
    if mcap is None:
        try:
            mcap = bse.market_cap_cr(scripcode)
        except Exception:
            mcap = None
    if mcap is None:
        mcap = _mcap_from_holdings(promoters, market.get("cmp"))
    if not snap.get("shp_pledged_shares"):
        snap = nse.pledged_snapshot(hit["name"] or "") or snap
    if snap.get("promoter_holding_pct") is None or not snap.get("shp_pledged_shares"):
        bse_snap = bse.shp_company_totals(scripcode, quarter["qid"])
        for key, val in bse_snap.items():
            if snap.get(key) is None and val is not None:
                snap[key] = val

    cmp = market.get("cmp")
    if cmp:
        for p in promoters:
            if p.get("pledged_shares"):
                p["pledged_value_cr"] = round(p["pledged_shares"] * cmp / CRORE, 2)
            if p.get("holding_shares"):
                p["holding_value_cr"] = round(p["holding_shares"] * cmp / CRORE, 2)

    return {
        "company": quarter.get("company") or hit["name"] or name,
        "bse_ticker": hit["bse_ticker"],
        "bse_code": scripcode,
        "nse_ticker": nse_symbol,
        "isin": hit.get("isin") or None,
        "market_cap_cr": mcap,
        "quarter": quarter["qname"],
        "quarter_end": iso(quarter_end(quarter["qname"])),
        "quarter_end_label": fmt_date(quarter_end(quarter["qname"])),
        "shp_filed": iso(quarter.get("filed")),
        "shp_filed_label": fmt_date(quarter.get("filed")),
        "promoter_shp_url": prom_url,
        "public_shp_url": pub_url,
        "promoter_holding_pct": snap.get("promoter_holding_pct"),
        "shp_pledged_shares": snap.get("shp_pledged_shares"),
        "shp_pledged_pct_of_promoter": snap.get("shp_pledged_pct_of_promoter"),
        "promoters": promoters,
        "unmatched_history": unmatched,
        "post_shp_events": post_shp,
        "market": market,
        "fetched_at": datetime.now(_IST).strftime("%d %b %Y %H:%M IST"),
    }
