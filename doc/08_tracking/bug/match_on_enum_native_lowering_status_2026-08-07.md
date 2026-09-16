# `match` on enum — per-engine status verified 2026-08-07 (partial fix, not fully stale)

- **ID:** BUG-2026-08-07-enum-match-native-lowering-status
- **Date:** 2026-08-07
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

## Re-verified 2026-08-09 — status UNCHANGED

Re-ran the exact probe from this doc against `origin/main` HEAD
`43be088053b2ae22f8f5d900bbd1322927840ea7`:

- `bin/simple compile enum_match_probe.spl --native -o out` (payload-bearing
  `describe_shape`): still refused, byte-identical message: `error: semantic:
  cannot compile to standalone native binary: 1 function(s) contain
  constructs that require the interpreter:\n  - describe_shape:
  [PatternMatch]`.
- Payload-free-only variant (`describe_kind` alone, no `Shape` in the closure):
  still compiles and runs correctly (`kind-A`/`kind-B`/`kind-C`).
- `bin/simple test test/01_unit/language/enum_match_dispatch_spec.spl`:
  `Results: 8 total, 8 passed, 0 failed`, rc=0 — no regression.

Today's session landed an extensive enum/match-lowering chain in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (rt_io
investigation layers 1-6: `f33ed64bddba`, `4b6aa5d24c57`, `51bf67bece57`,
`693750d48caf`, `63ee79be7eee`, plus earlier `663fce69eb35` and
`6414cd6ea0e4` on 2026-08-08). **None of these touch this gap**: they are all
in the pure-Simple `src/compiler/50.mir` MIR-lowering path that feeds the
self-hosted `native-build` pipeline, whereas the refusal reproduced above is
raised by the Rust seed's LLVM AOT pipeline
(`src/compiler_rust/compiler/src/pipeline/execution.rs:286`), a separate
code path entirely (confirmed unchanged since `cfe0506e336b`, 2026-08-05, by
`git log` on that file). The "Root cause" section below remains accurate
verbatim. Treat this doc as still current; the payload-bearing `--native`
gap remains open and out of `.spl`-only scope.

## Re-verified 2026-08-17 (worker s3_rust_other) — LIVE, exactly as documented

`src/compiler_rust/compiler/src/compilability.rs:379-383` (statement
`Node::Match`) and `:620-624` (`Expr::Match`) both add
`FallbackReason::PatternMatch` unless `mode == AotNative &&
is_native_payload_free_enum_match(arms)`. So payload-free enum match is
exempted (fixed) and payload-bearing still carries the fallback reason, which
`pipeline/execution.rs:286`/`:1067` turns into "function(s) contain constructs
that require the interpreter". The doc status is accurate; no change made.
Note: `compiler/src/codegen/**` and `compiler/src/mir/**` are owned by other
workers in this pass, so no fix was attempted here.
