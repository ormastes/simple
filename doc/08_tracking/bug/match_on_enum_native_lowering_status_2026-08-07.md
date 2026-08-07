# `match` on enum — per-engine status verified 2026-08-07 (partial fix, not fully stale)

- **ID:** BUG-2026-08-07-enum-match-native-lowering-status
- **Date:** 2026-08-07
- **Status:** payload-free enum match FIXED on `--native`; payload-bearing enum
  match still REFUSED (fail-closed) on `--native`. JIT (cranelift, default
  `bin/simple run`) and interpreter (`SIMPLE_EXECUTION_MODE=interpret`) both
  execute BOTH forms correctly.
- **Severity:** medium — `--native` (LLVM AOT, `simple compile --native`) is a
  narrower codegen gap than the default execution path; does not affect
  `bin/simple run` or `bin/simple test`.
- **Supersedes/refines:** `reference_match_on_enum_has_no_native_lowering.md`
  (memory, 2026-08-01) — confirms its "Stage 1 permits payload-FREE enum
  matches" note is still accurate today, and narrows the open gap to
  payload-bearing variants specifically.

## What was verified today

Probe: `enum_match_probe.spl` — `Kind` (3 unit variants) matched in
`describe_kind`, `Shape` (Circle(f64), Rect(f64,f64), Point) matched in
`describe_shape`, all arms + wildcard, `print()` per arm.

| Lane | Command | `describe_kind` (unit variants) | `describe_shape` (payload variants) |
|---|---|---|---|
| JIT (default) | `bin/simple run f.spl` | correct: kind-A/B/C | correct: circle:2.5 / rect:3.0x4.0 / point |
| Forced interpreter | `SIMPLE_EXECUTION_MODE=interpret bin/simple run f.spl` | correct | correct |
| Native AOT | `bin/simple compile f.spl --native -o out` | **compiles, runs, correct** (613696-byte ELF, ran kind-A/B/C) | **refused**: `error: semantic: cannot compile to standalone native binary: 1 function(s) contain constructs that require the interpreter:\n  - describe_shape: [PatternMatch]` |

JIT engagement for the default-lane row was confirmed live (not a silent
interpreter fallback): `SIMPLE_LOG=cranelift bin/simple run f.spl` printed real
Cranelift CLIF IR (block structure, `iconst`/`f64const`/`bitcast`/`call fnN`) for
every function, distinct from the interpreter's tree-walk trace. A sabotage
check (renamed one arm's return string to `"kind-B-SABOTAGED"`) reproduced the
sabotaged string in the JIT-lane output, proving genuine per-arm dispatch, not
a cached/hardcoded result.

**Deployment caveat:** the deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`) is still the Rust seed as of
this date (see `deployed_bin_simple_still_seed_2026-08-05.md`), so "JIT" and
"interpreter" above are the seed's Cranelift JIT and the seed's native Rust
tree-walk interpreter (`interpreter_control.rs`), not the pure-Simple
`.spl` interpreter/JIT tree. This does not affect the `--native` (LLVM AOT)
finding, which is a distinct code path in either case.

## Root cause of the remaining `--native` gap

The fail-closed check lives in the Rust seed, not `.spl`:
`src/compiler_rust/compiler/src/pipeline/execution.rs:286` — emits "N
function(s) contain constructs that require the interpreter" whenever a
function closure contains a `[PatternMatch]` construct the LLVM native
backend can't yet lower. Per the memory doc, Stage 1 (`3b9eb0a`, 2026-08-01)
narrowed this to exclude payload-free enum matches; payload-bearing matches
(tuple/struct-payload variant patterns) still trip it. This is Rust-seed
codegen (LLVM emitter path under `src/compiler_rust/compiler/src/codegen/`),
not `src/compiler/50.mir` — no `.spl`-side fix is available without extending
the LLVM emitter's enum-payload pattern lowering, which is out of scope here
(bootstrap-owned, no-Rust-edit-without-need, no bootstrap rebuild per session
constraints).

## Verdict

The blanket claim "match on enum has no native lowering, only works in
interpreter" is **STALE for the JIT and interpreter lanes** (both correct,
today, unit and payload variants alike) and **CURRENT-BUT-NARROWED for
`--native` AOT** (payload-free fixed, payload-bearing still refused). Treat
this doc as the up-to-date status; do not re-open the unqualified "no native
lowering" framing without re-checking `--native` specifically, since JIT ≠
`--native` AOT in this codebase.

## Spec coverage

`test/01_unit/language/enum_match_dispatch_spec.spl` — unit + payload variant
match, all arms + wildcard, run under default engine and
`SIMPLE_EXECUTION_MODE=interpret`; documents the interpreter-lane caveat and
does not attempt `--native` (out of scope for the in-process spec harness;
covered by the manual probe above instead).
