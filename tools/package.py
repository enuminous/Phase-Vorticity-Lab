#!/usr/bin/env python3
"""Create a flat, reproducible Git-ready ZIP and SHA256SUMS."""
from pathlib import Path
import hashlib
import sys
import zipfile

root = Path(__file__).resolve().parents[1]
output = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root.parent / 'Monolithic-Phase-Vorticity-Lab-v0.1.0-flat-git.zip'
excluded = {'.git', '.openai', 'dist', 'node_modules', '__pycache__', '.lake', 'local-formal', '.DS_Store'}
files = sorted(p for p in root.rglob('*') if p.is_file() and not any(part in excluded for part in p.relative_to(root).parts) and p.name != 'SHA256SUMS' and p.suffix not in {'.zip', '.pyc'})
manifest = ''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(root).as_posix() + '\n' for p in files)
(root / 'SHA256SUMS').write_text(manifest, encoding='utf-8')
files.append(root / 'SHA256SUMS')
with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in sorted(files):
        info = zipfile.ZipInfo(path.relative_to(root).as_posix(), (2026, 10, 30, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.create_system = 3
        info.external_attr = (0o100755 if path.suffix == '.sh' else 0o100644) << 16
        archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
with zipfile.ZipFile(output) as archive:
    assert archive.testzip() is None
    assert 'index.html' in archive.namelist()
    for row in archive.read('SHA256SUMS').decode().splitlines():
        digest, name = row.split('  ', 1)
        assert hashlib.sha256(archive.read(name)).hexdigest() == digest, name
print(f'{output}\n{len(files)} files; {output.stat().st_size:,} bytes; all hashes verified')
