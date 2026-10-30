#!/usr/bin/env bash
set -Eeuo pipefail
cd "$(dirname "$0")/.."
python3 tools/verify_snapshots.py
root="$PWD"
mkdir -p evidence/local-formal
cd formal/upstream-analysis
if ! command -v lake >/dev/null 2>&1; then
  echo 'Lean/Lake is not installed. Install elan and the pinned Lean 4.28.0 toolchain; no formal verification was performed.' >&2
  exit 2
fi
lake --version | tee "$root/evidence/local-formal/environment.txt"
lake exe cache get 2>&1 | tee "$root/evidence/local-formal/dependency-cache.log"
lake build 2>&1 | tee "$root/evidence/local-formal/build.log"
lake env lean -DwarningAsError=true Audit.lean 2>&1 | tee "$root/evidence/local-formal/axiom-audit.log"
python3 scripts/test_axiom_audit.py 2>&1 | tee "$root/evidence/local-formal/rejection-controls.log"
lake env lean -DwarningAsError=true SourceBridge.lean 2>&1 | tee "$root/evidence/local-formal/source-bridge.log"
cd "$root"
python3 tools/verify_snapshots.py
echo 'Completed source build, upstream axiom audit, negative controls and source bridge. JavaScript correctness is a separate obligation.'
