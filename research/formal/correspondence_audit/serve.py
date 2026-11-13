#!/usr/bin/env python3
"""Local server for the paper <-> Lean correspondence audit.

  python3 research/formal/correspondence_audit/serve.py [--port 8765]

then open http://127.0.0.1:8765/ . Serves the UI, the built audit data,
and read-only copies of the paper PDF and the Lean sources; appends every
UI event to logs/events.jsonl. Binds to 127.0.0.1 only. Standard library only.
"""
from __future__ import annotations

import argparse
import json
import mimetypes
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlparse

AUDIT = Path(__file__).resolve().parent
REPO = AUDIT.parents[2]
sys.path.insert(0, str(AUDIT / "tools"))
import auditlog  # noqa: E402

LEAN_ROOT = REPO / "research/formal/shiftsym/Shiftsym"
REPO_ALLOW = [
    (REPO / "shift_symmetry_d_dimensions.pdf", None),
    (REPO / "shift_symmetry_d_dimensions.tex", None),
    (LEAN_ROOT, ".lean"),
]


def allowed_repo_path(rel: str) -> Path | None:
    p = (REPO / rel).resolve()
    for base, suffix in REPO_ALLOW:
        if suffix is None and p == base:
            return p
        if suffix and p.suffix == suffix and base in p.parents:
            return p
    return None


class Handler(BaseHTTPRequestHandler):
    server_version = "CorrAudit/1"

    def log_message(self, fmt, *args):
        if "/api/" in self.path and self.command == "POST":
            return
        sys.stderr.write("%s %s\n" % (self.command, self.path))

    def send(self, code: int, body: bytes, ctype: str, extra: dict | None = None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, code=200):
        self.send(code, json.dumps(obj, ensure_ascii=False).encode(), "application/json; charset=utf-8")

    def send_file(self, p: Path):
        if not p.is_file():
            return self.send(404, b"not found", "text/plain")
        ctype = mimetypes.guess_type(p.name)[0] or "application/octet-stream"
        if p.suffix in (".lean", ".tex", ".md"):
            ctype = "text/plain; charset=utf-8"
        if p.suffix == ".mjs":
            ctype = "text/javascript"
        self.send(200, p.read_bytes(), ctype)

    def do_GET(self):
        path = unquote(urlparse(self.path).path)
        if path in ("/", "/index.html"):
            return self.send_file(AUDIT / "app" / "index.html")
        if path.startswith("/app/"):
            p = (AUDIT / path.lstrip("/")).resolve()
            if (AUDIT / "app") in p.parents:
                return self.send_file(p)
        if path.startswith("/data/"):
            p = (AUDIT / path.lstrip("/")).resolve()
            if (AUDIT / "data") in p.parents and p.suffix == ".json":
                return self.send_file(p)
        if path.startswith("/repo/"):
            p = allowed_repo_path(path[len("/repo/"):])
            if p:
                return self.send_file(p)
            return self.send(403, b"forbidden", "text/plain")
        if path == "/api/state":
            return self.send_json(auditlog.replay(auditlog.read_events()))
        return self.send(404, b"not found", "text/plain")

    def do_POST(self):
        path = urlparse(self.path).path
        n = int(self.headers.get("Content-Length", "0") or 0)
        raw = self.rfile.read(n) if n else b""
        try:
            body = json.loads(raw or b"null")
        except json.JSONDecodeError:
            return self.send_json({"error": "bad json"}, 400)
        if path == "/api/events":
            events = body if isinstance(body, list) else [body]
            events = [e for e in events if isinstance(e, dict) and e.get("type")]
            k = auditlog.append(events, {})
            return self.send_json({"ok": True, "n": k})
        if path == "/api/finish":
            auditlog.append([dict(body or {}, type="finish")], {})
            m, j, md = auditlog.report()
            return self.send_json({"ok": True, "markdown": md,
                                   "md_path": str(m), "json_path": str(j), "events_path": str(auditlog.EVENTS)})
        return self.send_json({"error": "unknown endpoint"}, 404)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--log-dir", type=Path, help="write events/reports here instead of logs/ (e.g. for a dry run)")
    args = ap.parse_args()
    if args.log_dir:
        auditlog.set_log_dir(args.log_dir.resolve())
    if not (AUDIT / "data" / "audit_data.json").exists():
        sys.exit("data/audit_data.json missing — run tools/build.py first")
    srv = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"correspondence audit: http://127.0.0.1:{args.port}/   (events -> {auditlog.EVENTS})", flush=True)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
