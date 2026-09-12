# `SIMPLE_BOOTSTRAP=1` is treated as "this compile IS the bootstrap CLI" at several sites

- Status: OPEN (2026-09-13) — two of the sites fixed, at least one more remains
- Found: bootstrap lane BOOT-4, `work/bootstrap-full-2-2026-09-12`
- Severity: blocks Stage-2 admission. Only reachable once the zero-work
  request-identity defect (`request-invalid`) is fixed — before that, the
  bootstrap-mode probe pass never ran at all
  (`frontend_smoke_bootstrap1_ran=false`).

## Shape

`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` runs its
four probes TWICE: once with `SIMPLE_BOOTSTRAP=0` and once with
`SIMPLE_BOOTSTRAP=1`. In the second pass the compiler builds
`hello_world.spl` — a program that has nothing to do with the bootstrap CLI —
while `SIMPLE_BOOTSTRAP=1`. Several code paths read that variable as if it
meant "the module being compiled is `app.cli.bootstrap_main`".

Only the POSITIONAL probe is affected. A positional source routes through
`lower_to_mir()` (`allow_bootstrap_shortcuts = true`); an `--entry` build routes
through `lower_to_mir_for_explicit_target()` (false). The other three probes are
`--entry` based and pass in the same pass with the same environment, so the run's
own status receipt is the control.

## Sites fixed in this lane

1. `src/compiler/80.driver/driver_pipeline_lowering.spl` — the fixed-entry MIR
   branch. Symptom: `MIR lowering missing HIR module for app.cli.bootstrap_main
   during bootstrap`.
2. `src/compiler/80.driver/driver_aot_pipeline.spl` — AOT dispatch into
   `bootstrap_compile_context_to_native_local`, which emits exactly one object
   hardcoded as `<output>.app.cli.bootstrap_main.o` and links only that.
   Symptom: `Bootstrap LLVM link failed ... ld.lld: error: undefined symbol:
   __simple_main`.

Both now additionally require `app.cli.bootstrap_main` to be among
`ctx.sources`. Neither relaxes the guard it sits next to.

## Site still open

After both fixes the same probe fails one phase later:

    [native-compile-failed] scripts.check.cert.redeploy_gate.fixtures.hello_world:
      AOT compile error in ...hello_world: MIR module has no functions
    error: in-process native-build: build failed: 1 failed ... of 1 unit(s)

Evidence: `build/stage2-resume.imOiO8/stage3/aarch64-unknown-linux-gnu/
stage2-sanity.env.frontend-bootstrap-1.log.hello-world-positional`.

Measured discriminator sweep against the run-3 Stage-2 binary
(`build/stage2-resume.imOiO8/stage2/aarch64-unknown-linux-gnu/simple.rejected`,
which carries both fixes above), identical command and scrubbed environment,
one variable added per row (`scratchpad/boot4/discriminate.sh`):

| variables | raw_status | first diagnostic |
|---|---|---|
| `SIMPLE_BOOTSTRAP=0` | **0** | (none — succeeds) |
| `SIMPLE_BOOTSTRAP=1` | 1 | `MIR module has no functions` |
| `SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` | 1 | `MIR module has no functions` |
| `SIMPLE_BOOTSTRAP=1 SIMPLE_UNSTUB_HIR=1` | 1 | `MIR module has no functions` |

**This REFUTES the obvious lead.** `driver_pipeline_lowering.spl:361` substitutes
an empty `MirModule` unless

    native_entry_closure_mir
      or _driver_is_bootstrap_entry_source(src.path, name)
      or SIMPLE_UNSTUB_HIR == "1"

and "MIR module has no functions" is exactly what an empty `MirModule` produces —
but forcing TWO of those three disjuncts true from the environment changes
nothing. So the empty module is not being produced there, or not only there.
The next lane should look upstream of MIR instead: HIR itself may already be
empty in bootstrap mode. `driver_hir_cache.spl:95` keys the HIR cache on
`SIMPLE_BOOTSTRAP` alongside `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE`,
`SIMPLE_BOOTSTRAP_STAGE4`, `SIMPLE_STUB_HIR` and
`SIMPLE_STAGE3_STREAMING_SURFACES`, and `SIMPLE_STUB_HIR` is the one knob in
that list this sweep did NOT vary. Vary it, and check whether the HIR module for
`scripts.check.cert.redeploy_gate.fixtures.hello_world` has functions before
blaming MIR — the probe log shows HIR reporting `succeeded=1`, which is not the
same as non-empty.

## Reproduction (about 60 seconds, no bootstrap needed)

Against any Stage-2 binary the lane produces, replay the scrubbed sanity
environment and flip one variable:

    scratchpad/boot4/discriminate.sh   # all four rows of the table above

The probe environment additionally needs `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`
(`candidate_frontend_admission.shs:285`), or the build dies earlier with
`scv-authority-missing`.

## Note on scope

An alternative reading is that the admission harness should not run the
positional probe under `SIMPLE_BOOTSTRAP=1` at all. That was rejected: the
harness deliberately re-runs the whole probe set in bootstrap mode, three of the
four probes already work there, and the positional probe exists precisely
because `--entry` and positional diverge
(`stage2_admitted_while_hello_world_native_build_segv_2026-08-25.md`). Narrowing
the harness would retire the coverage instead of the defect.
