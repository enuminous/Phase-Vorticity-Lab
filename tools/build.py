#!/usr/bin/env python3
"""Make a single-file offline index; no package install or network required."""
from pathlib import Path
root = Path(__file__).resolve().parents[1]
text = (root/'src/shell.html').read_text()
for marker, name in [('CSS','style.css'),('CORE','core.js'),('APP','app.js')]:
    text=text.replace('/*__'+marker+'__*/',(root/'src'/name).read_text())
(root/'index.html').write_text(text)
(root/'dist').mkdir(exist_ok=True)
(root/'dist/index.html').write_text(text)
print('Built index.html:', len(text.encode()), 'bytes')
