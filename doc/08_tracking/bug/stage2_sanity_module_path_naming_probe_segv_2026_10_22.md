# Stage-2 sanity: stage2_module_path_naming probe SIGSEGVs the worker (2026-10-22)

Status: OPEN — blocks the full stage2 sanity battery; p2_add (the compile/run
admission probe) PASSES. Phase 3 + phase-2 validation proceed provisionally
from the hello-world gate per the parallel collection policy (descendants
unadmitted until this closes).

## Symptom

`candidate_frontend_smoke` p2_add, scv_prime and the mir-retention probe pass;
the `stage2_module_path_naming.spl` probe (and then hello-world-positional)
kills the native-build worker with SIGSEGV during the HIR phase:

```
[build] phase=hir ... current=compiler.bootstrap_admission.stage2_module_path_naming
[hir-cache] disabled reason=no-compiler-scope
[WARN] any-escape pass: 0 diagnostic(s)
/usr/bin/timeout: the monitored command dumped core
Segmentation fault
error: stage2 failed the positional pure-Simple Stage-3 route (status 139)
```

Reproduces with the stage2 candidate under the sanity-like env
(`SIMPLE_BOOTSTRAP` unset, `--runtime-bundle core-c-bootstrap
--entry-closure --entry src/compiler/bootstrap_admission/stage2_module_path_naming.spl`).

## Context

The fixture's own header documents a KNOWN unresolved lane defect it
exercises: cross-module plain calls do not link in the per-module one-binary
lane (bare vs qualified symbol spelling; fix NOT landed as of 2026-10-17).
The previous failure mode of this lane was a clean link error; on the current
release_phase3 tree the worker SEGSEGVs instead.

A sibling defect in the same area was fixed today and may share a root cause:
`state = self.live_aliases(state, ...)` in the NLL solver corrupted the array
argument in transit (deterministic garbage header at callee entry);
moving the callee to module scope as a free function
(`nll_live_aliases`, e10fbb8f766 / 4f41ac876d8) fixed that instance. The
method-call argument-passing miscompile family (see cce1cddae19, mir receiver
writeback) likely has more instances reachable through this fixture's shape.

## Next steps

1. Replay the failing probe's worker under gdb (extract argv via strace on
   the coordinator, run `simple run src/app/cli/native_build_worker.spl ...`
   directly) and symbolize — the binary carries function symbols.
2. Audit the HIR-phase call path the fixture exercises for the same
   `self.method(array_arg, ...)` shape and convert to module-scope free
   functions as a targeted workaround.
3. Land the actual codegen fix for the argument-corruption family.
