# Task: JIT builtin-method dispatch audit (2026-07-29)

## Raw Request
Find every remaining builtin METHOD that fails silently on the Cranelift JIT
(prints `Function '<X>' not found` or a garbage value, exits 0) after this
session's earlier fixes (`index_of`, `first`/`last`/`pop`, `to_upper`,
`strip`, `enumerate`, `lines`, `parse_int`, dict integer keys/values,
array-to-string, `Dict.insert`, `Dict.get_or`). AUDIT ONLY — no source
changes.

## Task Type
audit / bug-discovery (no fix)

## Status
DONE — report delivered, no source modified.

## Result
- Built fresh `src/compiler_rust/target/release/simple` (mtime 2026-07-29
  03:24 UTC) via `cargo build -p simple-driver --release`.
- Probed 142 methods (51 array, 21 dict, 68 text, 2 special 2-D array cases)
  one-per-file against `SIMPLE_EXECUTION_MODE=interpret` vs
  `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_TRACE_ADDR=1`.
- Counts: OK 46, SILENT-FAIL dispatch-gap ("not found") 63, SILENT-FAIL
  wrong/garbage value 16, ORDER-DIFF (dict.keys/values) 2, DEMOTED
  (lambda-guard class) 15, CRASH 0.
- Full table + prioritised fix list: see
  `doc/08_tracking/bug/jit_method_dispatch_audit_2026-07-29.md`.
- Raw probe scripts/CSV/output pairs live at `/tmp/jitaudit/` on the audit
  host (not committed — scratch).

## Next Step (not done here — audit only)
Land the fixes in priority order from the doc: high-usage dispatch-arm gaps
first (`Array.insert`, `Dict.merge`, `Array.copy`/`Dict.clone`, `str.count`,
`str.repeat`, `Array.max`/`min`, `Dict.entries`, `Array.take`/`skip`,
`Array.zip`, `Array.sum`, `Array.fill`), then the remaining 47 low-usage
dispatch gaps, then the wrong-value class (`text.to_float` tag-boxed float
bug, `text.parse_int`/`parse_float` Option-unwrap bug, `dict.set`/`insert`/
`remove`/`clear`, `array.join`/`remove`, `array.enumerate` nested-tuple
print), then the `dict.keys`/`values` sort-order contract, then the
lambda-demotion class (separate, larger effort).
