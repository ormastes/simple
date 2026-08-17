# interp: AOT source-compile pipeline stubbed / non-functional under seed interpreter

- **id**: interp_aot_source_pipeline_stubbed_non_functional_2026-06-25
- Status: **OPEN (P2) — defect #2 (HIR) is FIXED, defect #3 (MIR) is STILL LIVE**
- Re-verified 2026-08-17 (wave_01 lane B) against current source. The "Chain of
  defects" list below is now partly stale; corrections in this section win.

## 2026-08-17 re-verification — the two stubs have diverged

The two stubs described below are no longer symmetric. Read this before acting on
the chain list.

### Defect #2 (HIR lowering stubbed) — **FIXED, doc was stale**

The code moved out of `driver.spl` into
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`. At line **472** the gate is
now **default-ON**:

```
val unstub_hir = (rt_env_get("SIMPLE_STUB_HIR") ?? "") != "1"
```

i.e. real HIR lowering runs for every source unless someone explicitly sets
`SIMPLE_STUB_HIR=1`. The empty-`HirModule` literal at `:510` survives only as that
opt-in escape hatch, plus a fallback for evicted phase-2 modules. Non-bootstrap
sources DO get real HIR today.

### Defect #3 (MIR lowering stubbed) — **STILL LIVE, and now the sole blocker**

`src/compiler/80.driver/driver_pipeline_lowering.spl:219` (the gate) and
**`:231-238`** (the stub literal):

```
var mir_direct = if native_entry_closure_mir or _driver_is_bootstrap_entry_source(src_direct.path, name_direct) or (rt_env_get("SIMPLE_UNSTUB_HIR") ?? "") == "1":
    ... real MirLowering ...
else:
    MirModule(name: name_direct, functions: {}, statics: {}, constants: {}, types: {})
```

For a plain `-c <file>` AOT compile none of the three disjuncts holds:

- `native_entry_closure_mir` is `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE == "1"` — unset;
- `SIMPLE_UNSTUB_HIR` — unset;
- `_driver_is_bootstrap_entry_source` (`driver_source_loading.spl:47-63`) returns true
  only for a caller-supplied `SIMPLE_NATIVE_BUILD_ENTRY`, or for
  `app/cli/bootstrap_main.spl`. A user's `-c` file is **neither**.

So **every** module, including the user's own entry, takes the `else` branch and is
lowered to `functions: {}`.

**This is the silent-wrong-result shape, and the HIR fix made it worse, not better:**
HIR now holds the real functions, MIR then discards them, and the backend is handed a
structurally valid but empty module. Nothing errors; the driver proceeds.

### Two further defects found while reading, worth fixing with #3

1. **The MIR gate reads an HIR-named variable.** MIR's opt-in is spelled
   `SIMPLE_UNSTUB_HIR`, while HIR's escape hatch is `SIMPLE_STUB_HIR` — different name,
   *inverted* polarity, and there is no `SIMPLE_*_MIR` knob at all. `SIMPLE_STUB_HIR=1`
   therefore stubs HIR but leaves MIR's behaviour unchanged, and `SIMPLE_UNSTUB_HIR=1`
   un-stubs MIR but not HIR. Any operator reading either name gets the opposite of what
   they expect on one of the two passes.
2. **Dead code after a `return`.** In the same function, `lower_to_mir()`, the trailing
   `for src3 in self.ctx.sources:` block (immediately after
   `return not self.ctx.has_errors()` at `:275`, so the block at `:276-289`) is
   unreachable. It is a third,
   forgotten copy of the empty-MirModule stub and should be deleted rather than left to
   be mistaken for live behaviour.

### Not fixed this pass, deliberately

Per this lane's reproduce-first contract a fix needs a quoted RED `Results:` line, and
per host etiquette a stage-3 self-host bootstrap owned the box at ~98% CPU for the whole
session. A `bin/simple run src/compiler/80.driver/main.spl -c tiny.spl --target wasm32`
repro was started and had not reached MIR after ~25 min (it plateaus in a fixed
~1518-line stdlib prefix — see
`entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08.md`), so no RED
line was obtained and **no code was changed**.

Flipping the `:219` default to match HIR's is the obvious repair, but it is NOT safe to
do blind: the `SIMPLE_BOOTSTRAP_STAGE4=1` path falls through to this same loop, so a
default change lands directly on the running bootstrap. Whoever takes this should gate
the change behind a stage4 check and land it when the box is quiet.
- **severity**: P2 (feature gap, not a crash on its own)
- **date**: 2026-06-25

## Summary

`bin/simple run src/compiler/80.driver/main.spl -c <file> --target wasm32 -o out.wat`
(the pure-Simple compiler driver under the Rust seed interpreter) cannot emit a
real module for non-bootstrap sources. The wasm backend itself is proven
(`wasm_compile_spec` 37/37); the blockage is upstream in the driver's HIR/MIR
lowering, which is stubbed for all non-bootstrap sources.

## Chain of defects

1. **parse_full_frontend nil-return** — `parse_full_frontend(...) -> Module`
   (`src/compiler/10.frontend/frontend.spl`) had no return statement; the last
   expression was `desugar_collections(...)` (returns nil). Every non-bootstrap
   `ctx.modules[*]` was nil → "accessing field 'functions' on nil".
   **FIXED**: added trailing `module` return (this change landed).

2. **HIR lowering stubbed** — `lower_and_check_impl()` in
   `src/compiler/80.driver/driver.spl` (the `sources.len() > 0` branch) gives only
   the bootstrap entry real HIR lowering; every other source gets an empty
   `HirModule(functions: {})`. NOT fixed (un-stub reverted, see below).

3. **MIR lowering stubbed** — `lower_to_mir()` in
   `src/compiler/80.driver/driver_pipeline.spl` (`sources.len() > 0` branch)
   stubs non-bootstrap sources to empty `MirModule(functions: {})`. NOT fixed.

## Why the un-stubs were reverted

Un-stubbing HIR+MIR (fresh lowering per source) is the correct direction, but it
immediately exposes an unbounded chain of interpreted-compiler bugs:

- **4a — Option.map on a present value**: interpreter represents `Some(x)` as the
  bare value `x`; it has no Some-fallback for Option methods, so
  `fn_.return_type.map(...)` (hir_lowering/_Items/declaration_lowering.spl:150) errors
  "method 'map' not found on type 'Type'". (Already worked around at the callsite
  with an explicit `.?` check; other callsites remain exposed.)
- **4b — resolve.spl method orphaning**: `class MethodResolver`
  (`src/compiler/35.semantics/resolve.spl`) has two indent-0 free functions
  (`create_trait_solver_for_resolution`, `create_method_resolver`) between the
  class fields and its `me` methods; the dedent closes the class, so methods
  177+ get absorbed into `create_method_resolver`'s body → `resolve_module`
  fails on nil. Pre-existing structural bug.
- **typed-optional nil field-access SIGSEGV** — see
  `interp_typed_optional_nil_field_access_sigsegv_2026-06-25.md`.

## Decision (cautious consolidation)

Per the "go with caution — it is made crash" directive, keep only the
contract-correct parse fix (#1) and document #2/#3/#4 as concrete bugs. The
HIR/MIR un-stubs and the seed Some-fallback prototype were reverted/stashed to
keep the seed at baseline (zero seed risk). `--check` exits 0 clean with the
parse fix alone.

## Repro

```bash
SEED=src/compiler_rust/target/bootstrap/simple
$SEED run src/compiler/80.driver/main.spl -c /tmp/hello.spl --target wasm32 -o /tmp/w.wat
# before parse fix: "accessing field 'functions' on nil"
# after parse fix:  reaches HIR/MIR stub -> empty module
```
