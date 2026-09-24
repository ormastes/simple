# OPEN: native-build dies after `aop_weave` — a 1-argument call binds to `log.spl`'s 2-argument `(scope, msg)` helper

- **Status:** OPEN — observed 2026-09-13, not diagnosed beyond the binding site.
- **Found while** fixing
  `native_build_noop_invocation_frames_raw_i64_mcdc_mode_2026-09-13.md`; this is
  the NEXT blocker uncovered once that one is removed, not the same defect.

## Reproducer

At `origin/main` + the `mcdc_mode` fix, with the two known earlier blockers
worked around:

```
SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_SCV_FREEZE_FALLBACK=1 \
  <seed> native-build --mode=dynload hello.spl
```

where `hello.spl` is:

```
fn main():
    println("hello")
```

The build proceeds through `load_sources`, `mir`, and `aop_weave` (all
`state=complete`), then:

```
error: semantic: function expects argument for parameter 'msg', but none was provided
```

## What is established

`SIMPLE_DEBUG_ARG_BINDING=1` names the binding exactly:

```
[DEBUG arg_binding TMP] missing param 'msg'; full param list=["scope", "msg"]; args given=1
```

`["scope", "msg"]` is the signature of the logging helpers in `src/lib/log.spl`
(`fatal`/`error`/`warn`/`info`/`debug`/`verbose` at lines 720-739; the same
shape repeats in `src/lib/nogc_sync_mut/log.spl:266`). So a call site passing a
**single** argument is resolving to a **two**-argument logger.

This is consistent with the `compiler_cross_module_private_symbol_collision`
class that the same build already reports in bulk — the run emits dozens of
warnings of the form "public function `X` has N co-compiled definitions with
differing signatures ... falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one", naming
`error`-adjacent generic names among others. A one-argument `error("...")` or
`warn("...")` in the weave/backend path colliding with `log.error(scope, msg)`
would produce exactly this.

## What is NOT established

- The specific call site was not located. The diagnostic carries no source
  location, and unlike the `method not found` class there is no
  `SIMPLE_INTERP_OOB_DEBUG` equivalent that prints the `.spl` frame chain for an
  arity mismatch. **Adding one would be worth more than fixing this instance** —
  see the localization notes in the sibling record.
- Whether the offending call is in `aop_weave` itself or in the phase
  immediately after it (the failure prints after `aop_weave state=complete`).
- Whether this is a genuine collision or a plain one-argument call to a
  two-argument function that was never exercised.

## Why it matters

Together with
`stage3_step_omits_package_index_cold_init_scv_authority_missing_2026-09-13.md`,
this is what still stands between the tree and a `native-build` of a three-line
hello world. Until both are closed, no "hello native-builds" gate can be added
as a green row to any harness default sample.
