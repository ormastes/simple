# `Dict.len()` returns -1 on a struct-keyed `Dict` in a Stage-2 native compiler, while `.keys().len()` is correct

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-5, `work/bootstrap-full-3-2026-09-12`
- Severity: currently only corrupts a diagnostic, but it is the symptom
  `.claude/rules/code-style.md` records as **RESOLVED on 2026-08-01 / re-verified
  2026-08-09**. Either that fix regressed, or it never covered this path.
  Nothing in the build gates on the value, so no build outcome is wrong today —
  which is exactly why it could sit here unnoticed.

## Measured

Binary: `scratchpad/boot5/pin/simple.stage2.rejected` (a Stage-2 native
compiler), sha256 `79139f420ee07450...`. Environment scrubbed, plus
`SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_INTERP_TRACE=1`; building
`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`.

`driver_pipeline_lowering.spl` logs the freshly lowered module as
`functions={lowered_entry.functions.len()}` on `MirModule.functions`, declared
`Dict<SymbolId, MirFunction>` (`mir_instruction_graph.spl:434`). Both runs print:

    [BOOTSTRAP-PHASE] aot:lower_to_mir:module:done idx=0
      module=scripts.check.cert.redeploy_gate.fixtures.hello_world functions=-1

The `SIMPLE_BOOTSTRAP=0` run is the control: it goes on to compile and LINK the
program successfully (`raw_status=0`), and its own trace shows the one function
being lowered (`[mir-lower] lower_function:start main` …
`lower_function:body-done main`). So the module demonstrably held one function
while `.len()` answered `-1`.

The sibling count in the same file is right: `lower_module` logs
`functions={module.functions.keys().len()}` and printed `functions=1` for the
HIR module. `.keys().len()` and `.len()` disagree on struct-keyed dicts here.

## Possibly-shared root cause (NOT established)

`hir_module_function_miss_returns_extern_placeholder_2026-09-13.md` records a
second struct-keyed-`Dict` anomaly measured in the SAME run: a `SymbolId` taken
from `HirModule.functions.keys()` matched no value's `symbol.id` when scanning
`.values()` of that same dict. Both involve `Dict<SymbolId, …>` on a native
Stage-2 binary. They may share a root cause in struct-keyed `Dict` lowering;
that is a hypothesis, not a finding, and neither has been root-caused.

## Reproduction (about 30 seconds, no bootstrap needed)

    sh scratchpad/boot5/disc5.sh bs0_trace
    grep 'lower_to_mir:module:done' scratchpad/boot5/d_bs0_trace.log
    # -> ... functions=-1, on a build that then succeeds (raw_status=0)

## Scope note

Not fixed here. This lane's change is a driver routing gate; the `Dict`
lowering is outside it, and `src/compiler/50.mir/_MirLowering/module_lowering.spl`
is fenced for this lane in any case. The interpreter lane is unaffected — the
`-1` is a property of the native Stage-2 binary.
