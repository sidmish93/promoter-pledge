"""
Live promoter-pledge screen.

Run:
    python app.py

Then open http://127.0.0.1:5000
"""
from __future__ import annotations

import os
import traceback

from flask import Flask, jsonify, make_response, render_template, request

from fetchers import fmt_date, last_quarter_end, list_pledged_companies, load_company

app = Flask(__name__)
app.config["TEMPLATES_AUTO_RELOAD"] = True
app.jinja_env.auto_reload = True


@app.route("/")
def index():
    resp = make_response(render_template("index.html"))
    resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate"
    resp.headers["Pragma"] = "no-cache"
    return resp


@app.route("/api/companies", methods=["POST"])
def companies():
    try:
        rows, meta = list_pledged_companies()
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 502
    return jsonify({
        "companies": rows,
        "count": len(rows),
        "shp_cutoff_label": fmt_date(last_quarter_end()),
        "list_meta": meta,
    })


@app.errorhandler(500)
def _server_error(_e):
    return jsonify({"error": "Server error while opening this company."}), 500


@app.route("/api/company", methods=["POST"])
def company():
    try:
        data = request.get_json(force=True) or {}
        name = (data.get("name") or "").strip()
        symbol = (data.get("symbol") or "").strip()
        scripcode = (data.get("scripcode") or "").strip()
        isin = (data.get("isin") or "").strip()
        if not name:
            return jsonify({"error": "Choose a company from the list."}), 400
        result = load_company(
            name,
            symbol=symbol or None,
            scripcode=scripcode or None,
            isin=isin or None,
        )
        return jsonify(result)
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 502


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "5000"))
    print(f"Promoter pledges -> http://0.0.0.0:{port}")
    app.run(host="0.0.0.0", port=port, threaded=True, debug=False)
