# error_path scenario 27 (`Some(nil).?`) is RED in all 100 error_path specs

Status: open, spec kept RED deliberately
**Found:** 2026-10-31 (relfix-errpath lane)

## Symptom
Every `test/03_system/core/error_path/error_path_<N>_system_spec.spl` (N=1..100) fails exactly one of 30 examples: "error path 27 - option chain breaks" (`val opt = Some(nil); verify(opt.?)` -> "expected false to equal true"). The other 29 pass on the Rust seed. Before: 0/100 specs green; after: unchanged (no fix applied).

## Cause
Not a spec staleness. The spec header declares scenario 27 RED by contract: `Some(nil).?` is falsy on the runtime. Seed repro: `val a = Some(nil); print "{a.?}"` prints `nil` (`Some(1).?` prints `1`, `Some(false).?` prints `false`), i.e. `.?` returns the payload per the ratified `T?` contract (see exists_check_on_optional_i64_returns_payload_2026-08-01.md), so a nil payload is indistinguishable from absence.

## Why not fixed here
Fixing needs a semantic decision (presence vs payload for `.?` on a wrapped Some) in the interpreter, which lives in src/compiler_rust (off limits). Weakening or removing the scenario is forbidden. Resolve by either changing `.?` semantics for `Some(nil)` or ratifying the contract and rewriting the oracle in all 100 specs (owner decision).
