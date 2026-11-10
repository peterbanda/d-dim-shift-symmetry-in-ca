#!/usr/bin/env python3
"""Glyph boxes of the official PDF, for fitting highlight rectangles.

  uv run --no-project --with pymupdf python -I pdf_chars.py <paper.pdf> <out.json>

Output: {"pdf_sha256": ..., "pages": [[[x0, y0, x1, y1], ...], ...]} in PDF
points with the origin at the top-left corner of the page.
"""
import hashlib
import json
import sys

import pymupdf

pdf, out = sys.argv[1], sys.argv[2]
pymupdf.TOOLS.set_small_glyph_heights(True)
doc = pymupdf.open(pdf)
pages = []
for page in doc:
    boxes = []
    raw = page.get_text("rawdict")
    for block in raw["blocks"]:
        for line in block.get("lines", []):
            for span in line["spans"]:
                for ch in span["chars"]:
                    if ch["c"].strip():
                        x0, y0, x1, y1 = ch["bbox"]
                        boxes.append([round(x0, 2), round(y0, 2), round(x1, 2), round(y1, 2)])
    pages.append(boxes)
sha = hashlib.sha256(open(pdf, "rb").read()).hexdigest()
json.dump({"pdf_sha256": sha, "pages": pages}, open(out, "w"))
print(f"{len(pages)} pages, {sum(map(len, pages))} glyph boxes")
