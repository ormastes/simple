# Bootstrap SCV rejects literal tracked brace filenames

GitHub: https://github.com/ormastes/simple/issues/3340 — OPEN.

Canonical BootstrapProductScv::source_path rejects literal braces in valid tracked source filenames, aborting the mandatory generator SCV post-verification.

Actual retained generator diagnosis: `normal-generator-launcher-e644/owned/generator-e6447d0d10f2-6e979e69cbff-attempt02/bounded-source-diagnosis.json` reports the canonical tool-root validator lines85–88 rejects authenticated auxiliary source-inventory rows33785 and39572:

- test/03_system/stress/stress_{2..25}_system_spec.spl
- test/system/stress_{2..25}_system_spec.spl

Both are literal Git-tracked names; no brace expansion is intended. Frozen payload inventory had0 unsafe members. Current local4a806aaddc250177c21da54b0f38959dd2b86906 and fetched remote retain the brace-excluding alphabet. Do not delete/skip these files or waive SCV verification.

Narrow proposal adds literal escaped `{`/`}` bytes to the existing src/test alphabet and retains exact traversal/empty-component/NUL/backslash/colon/framing restrictions, digest checks and symlink/unbound auxiliary rejection. Same expanded host fixture fails old validator with unsafe SCV source identity; proposed external validator passes24 authenticated auxiliary checks once, including exact brace paths, traversal/NUL, linked source/auxiliary directory and unknown members.

Status OPEN: external source/host-control proof only. No new native allocation, compiler build, actual generator retry, runtime/callback/link/Phase3 success, source-tree edits or gate waiver. A newly sealed canonical tool bundle and actual post-verification must still qualify the retained generator product. Old scope/runtime qualification remains HOLD.
