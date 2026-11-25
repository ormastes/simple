# Stage-2 bootstrap binary binds the K1 stub in native-build workers (PLUG-E-TABLE)

- **ID:** stage2_bootstrap_worker_k1_composition_unbound_2026-11-25
- **Severity:** P1 (blocks every Phase-3 self-build from a fresh stage-2 producer)
- **Status:** open
- **Found:** 2026-11-25, phase-3 warning-count validation lane (p3warn)

## Symptom

A stage-2 binary built from release/1.0.0 tip (`d8e3c1ca310`) by the
attr-capable Rust seed (`cargo build --release --bin simple` from #11521
source, cranelift backend via `p3b_build.shs ... cranelift p3stage2_ll`)
compiles and passes `--version`, and its COORDINATOR binds the LLVM
composition (a `--backend llvm` build reaches HIR/MIR). But every MIR
worker it spawns — and the interpreter child used by
`SIMPLE_MIR_SHARD_INPROCESS_FALLBACK=1` — fails immediately with:

```
error: PLUG-E-TABLE: native-build worker backend composition refused: stub: no K1 composition bound
  interpreter: c:/dev/p3diag/p3stage2_ll/simple.exe (exit code 1)
```

With cranelift the coordinator itself refuses earlier:
`PLUG-E-NOTFOUND: backend 'cranelift' not linked in the essential composition (K1 policy 'unselected')`.

So the producer can parse/HIR but cannot run MIR for any native build:
`native-build` of even a 20-line hello-class probe fails, and the full
Phase-3 build (`p3warn_ll`) dies at `owner=0/24@0 status=BLOCKED
claimed=0`. `SIMPLE_MIR_SHARD_INPROCESS_FALLBACK=1` does not help — the
fallback child is refused identically.

## Repro

```sh
# producer (67 min, rc=0, --version OK):
WTMO=0 THREADS=1 MIRSHARDS=24 P3SRC=<tree at d8e3c1ca310> \
  sh /c/dev/p3diag/p3b_build.shs <attr-capable-seed>/simple.exe cranelift p3stage2_ll
# any native build with it fails:
<canonical p3hello2.shs env> p3stage2_ll/simple.exe native-build \
  --entry-closure --runtime-bundle core-c-bootstrap \
  --target x86_64-pc-windows-gnu --backend llvm \
  --source build/probe --entry build/probe/split_probe.spl -o out.exe
# -> PLUG-E-TABLE in the MIR worker; BLOCKED owner=0/N@0
```

Full logs: `C:\dev\p3diag\p3warn_ll\build.log`,
`C:\dev\wt-bug-split\build\probe\out\build.log`.

## Notes toward root cause

- The baseline producer `p3fix2_ll/simple.exe` (built 2026-11-24 by an
  older stage binary, llvm backend) does NOT have this defect — its
  workers bind fine on the Nov-24 tree. Two variables changed: the
  builder (Rust seed vs stage binary) and the build backend (cranelift
  vs llvm). Either the seed-driven build does not commit the K1
  composition into the product, or the cranelift-built product loses the
  worker-side composition table. `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` was
  set for both, so the whole-program shortcut is not the differentiator.
- The worker estimate/admission knobs (`SIMPLE_MIR_SHARD_WORKER_KB`,
  `SIMPLE_MIR_SHARD_COUNT`) only move the failure from the memory
  admission to the composition refusal; they are not the cause.
- Secondary defect observed on the same lane: the Nov-24 producer cannot
  compile the current tree at all —
  `stage3_selfbuild_raw_text_strict_extern_2026-11-18` defect 2 fires in
  `_driver_collect_explicit_compiler_source`
  (`[explicit-source] rejected non-spl path=RTS\x02` ×152 → entry closure
  empty → `visibility-manifest-source-binding-invalid`). That binary is
  therefore not a fallback producer for current tips.
- A third admission trap on this lane: untracked `.simple/` state left in
  a source tree by earlier builds fails the next build with
  `SCV-E-ADMISSION: inventory-generation-invalid`; `git clean -fdx
  .simple/` in the tree is required before reusing it.

## Impact and workaround

Blocks the phase-3 zero-warning confirmation build for the E-MC-REP-001
burndown (all source fixes are landed and lint-verified; only the native
build count is missing). No workaround found on Windows: both spawned
workers and the in-process fallback child are refused. Next steps: build
the producer with an llvm-feature seed, or diagnose the K1 composition
commit path for seed-built products (`bootstrap backend composition
admission`, `PLUG-E-K1-POLICY`/`PLUG-E-TABLE` owners).
