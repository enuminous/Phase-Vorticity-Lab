#!/usr/bin/env python3
"""Verify vendored Git blob identities without network access."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'evidence/provenance.json').read_text())
for f in manifest['files']:
    b=(root/f['local_path']).read_bytes()
    sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    if sha!=f['git_blob_sha']:
        raise SystemExit('FAIL: source changed: '+f['local_path'])
assert (root/'formal/upstream-analysis/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.28.0'
assert manifest['mathlib'] in (root/'formal/upstream-analysis/lake-manifest.json').read_text()
print('PASS:',len(manifest['files']),'pinned source snapshots; toolchain and Mathlib pin present.')
