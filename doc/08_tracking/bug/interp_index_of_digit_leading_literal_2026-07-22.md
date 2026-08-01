# Bug: flat `i64?` optional lane collides with tagged-value scheme (seed JIT) — payload 3 reads as nil

Status: OPEN — root-caused 2026-07-22; architectural fix required
Observed: 2026-07-22 (as "index_of digit-leading literal" — that was a red herring, twice)
Severity: P1 — silently wrong values in production tooling paths (JIT `run` on
seed-engine binaries, which includes the currently deployed bin/release binary)

## True root cause (isolated, no strings involved)
The seed JIT's **flat (non-boxed) `i64?` lane** does not apply the runtime's
tagged-value scheme (`(v<<3)|tag`), but its values flow into consumers that
dispatch on tag bits. Nil is `rt_core_nil()` = bit pattern **3**
(src/runtime/runtime_native.c ~2402-2422 — the sentinel was moved 0→3 to fix
`native_i64opt_some0_collapses_to_nil`, which only relocated the collision).

Decisive isolation (`fn make_opt(v: i64) -> i64?: return v`, seed JIT):

```
make_opt(0) → some:0          (ok — 0 coincidentally reads as tagged int 0)
make_opt(1) → some:nil        (payload 1 misread via tag bits)
make_opt(2) → some:0.0        (payload 2 misread as float tag)
make_opt(3) → NIL             (payload 3 == nil sentinel — value LOST)
make_opt(4) → some:<value:0x4> (raw repr fallback)
make_opt(11) ?? -99 → prints "true" (11&7=3 tag misread downstream)
```

`SIMPLE_EXECUTION_MODE=interpreter` is CLEAN (real Rust Value enum, no packing).

## Surface symptoms (how it was found)
`text.index_of(needle)` "returns nil for any match at position 3" — because the
found index 3 IS the payload-3 collision. All string-search implementations
(spl_str_index_of, rt_string_find, SIMD family) verified CORRECT. Earlier
"digit-leading literal" and "position 3 search miss" characterizations were
both artifacts of this. Every `i64?`-returning API (find/rfind/index_of/
last_index_of/dict lookups/...) mis-nils on payload 3 and misprints small
payloads.

## Affected engines / binaries
- Seed JIT (`run` default): AFFECTED — confirmed. Note the wt_e2ebootstrap
  "full" binary delegates run to a sibling `simple_seed`; the deployed
  bin/release/x86_64-unknown-linux-gnu/simple is ALSO seed-engine (banner) and
  reproduces — consistent with the known "self-hosted not deployed" blocker.
- Interpreter: NOT affected — confirmed.
- Seed native/LLVM codegen: untested, likely affected (same dispatch tables,
  codegen/llvm/functions.rs:2190/2527, llvm/emitter.rs:169/191) — prediction,
  not verified.

## Blast radius (grep evidence)
- 45 sites compare find/index_of results raw (`>=0`/`==-1`).
- 429–1609 sites coalesce via `??` — silently take the nil branch when the true
  answer is 3 (production compiler .spl code incl. linker/backend).

## Representation finding (2026-07-22, MIR-dump-proven)
`T?` for primitives is NOT a union/enum: it lowers as `HirType::Pointer{inner:T}`
— a nullable-pointer optimization where the "pointer" IS the raw primitive and
nil is the fake pointer 3 (`hir/lower/expr/control.rs:554` documents this). The
lane is internally CONSISTENT raw: arithmetic, `??` (rt_unwrap_or_self
passthrough), if-val (direct Store copy — a separate HIR pattern path from
`??`), and function passing all agree on raw. The two defects are:
1. payload 3 == nil sentinel — UNSOUND BY CONSTRUCTION for full-range i64
   (no in-band sentinel can be sound; 3 is just badly placed).
2. generic print consumers assume TAGGED values — raw payloads misread as tag
   bits (the 1→"nil", 2→"0.0", 11→"true" garbage). Display defect only.

## Resolution (senior decision 2026-07-22)
- Defect 2 (print): FIX LANDED/IN FLIGHT — print lowering
  (mir/lower/lowering_expr_builtin.rs print special-case) routes
  Pointer{inner:primitive} args through nil-aware raw formatters
  (rt_opt_i64_to_string / rt_opt_bool_to_string), mirroring the existing
  rt_raw_i64_to_string 61-bit bypass.
- Defect 1 (payload-3 collision): DOCUMENTED LIMITATION, fix deferred. Full
  end-to-end tagging was designed and rejected for now: 7 site-groups across
  6+ files on the hottest lowering paths (Return needs new declared-type
  context threading; if-val and `??` are two independent paths; call-arg,
  Let/Assign, struct-field coercion sites all need wiring), it inherits the
  documented 61-bit BoxInt truncation, and the seed is bootstrap-only by repo
  policy. An earlier boundary-boxing spot-patch was PROVEN WRONG (`??` does
  not unshift). If/when fixed properly: retire the flat Pointer representation
  for primitive optionals in favor of the tagged scheme, using the make_opt
  matrix + arithmetic-after-unwrap + optional-chain + double-tag probes in the
  session record as the regression gate.
- Practical guidance until then: on seed-engine binaries, any `i64?` API can
  return nil when the true answer is exactly 3 (e.g. index_of match at
  position 3). Prefer `>= 0` sentinel-style APIs or add +1 offsets in critical
  paths; the self-hosted engine must be checked for the same representation
  before the same trust is extended (verification pending).

## Related prior filings (same family)
- native_i64opt_some0_collapses_to_nil (the 0-sentinel ancestor)
- seed BoxInt <<3 enum heap-handle mangling (stage4 wall)
- interpreter quirk ".? on 0-i64 → false" — likely the same lane, old sentinel
