# Native static method receiver identity

Status: focused native criteria PASS across the two recorded producers; authored SSpec and general-host checks remain UNRUN.

## Observed behavior

The source-matched pure compiler `85663ff65685b35a7d5a3389701ae3df41974fc0e8135e4fc0f85ca00f6fcfe2` compiled two small packages on 2026-10-16. Both separated nominal declarations, implementations, and a façade. One façade exported implementations; the other also explicitly exported the types. Each package had two different owners defining `new` and `incremented`, preventing a unique method-name fallback from masking missing ownership.

Both builds completed 16-module parsing/HIR and failed in the entry module during MIR lowering: `Counter` and `Other` were treated as undefined runtime variables, followed by unresolved constructors and instance-call cascades. Each case reported six fatal messages and one failed MIR module. Neither binary ran. The baseline completed in about 37 seconds at 534080 KiB peak under an 8 GiB owner, with confirmed process cleanup and matching runtime binding before and after.

Evidence is retained in `.simple/storage/build/mir-semantic-rootcause-20261016/`: `result.json` (SHA256 `486591526c2263f7b94ad19e473ce08a1813dee4925c5e40fa41b9386c2ef809`) and `baseline-analysis.json` (SHA256 `3c3f5597c1dd1259f798343ce837a995a17f9882d6371e9bd9caa91b7cedb765`). These are bootstrap-parent native diagnostics, not general test-host qualification.

## Cause and repair

The expression dispatcher supplies empty static-receiver hints. The unresolved method lowering path did not recover a type-valued receiver from its actual symbol-table entry before attempting to lower the receiver as a runtime value.

The proposed repair reads the detached receiver expression and accepts only `Var` or `NamedVar` entries whose actual declaration kind is `Struct`, `Class`, or `Enum`. It passes the recovered symbol and canonical owner identity into the existing owner-specific static-method lookup. A parameter or local variable remains an instance even when its declared type is nominal. The existing unique-name fallback is unchanged; this repair does not claim to remove it.

Acceptance requires both façade programs to compile and run with exact output `counter=42 other=17`, preserving ordinary instance calls and distinguishing the two constructors. Negative regression must reject borrowing another owner's method and must keep local values out of static receiver recovery. Authored SSpec execution and full compiler/core/MCP checks remain pending an admitted full test host.

## Separate findings

The explicit façade's phase-profile errors correctly identify its own module, but its final formatted source spans refer to the prior content-identical implicit fixture. The frontend parse cache is content-keyed. This establishes stale diagnostic paths; semantic cache contamination is not established and is not part of this repair.

An independent imported-generic extern control compiled, linked, and ran correctly, while the Any census warned about its declared `T` parameter and an explicit `Any` control. The extern flat converter drops type-parameter metadata. A parser-only correction is not integration-ready: monomorphization must preserve the raw foreign ABI without creating mangled executable bodies. That separate advisory defect remains open; no Any-policy exemption is included here.

## First changed-producer verification

The new pure compiler `209d55d9b603a0c2b3efdee34eed870991bdda2b429e84a1e152e2ee09788505` compiled, linked, and ran both façade programs successfully, each with exact `counter=42 other=17` output and empty stderr. The missing-owner case refused compilation and produced no executable, but emitted two fatal diagnostics: an incorrect undefined `Counter` error followed by the correct unresolved `only_other` error. The exact negative oracle therefore failed.

The recovered nominal receiver still entered runtime-value lowering after its owner-specific method lookup failed. The follow-up repair terminates that path through the existing unresolved-method error/panic emitter immediately; ordinary runtime-instance handling and successful static lookup remain unchanged. The negative SSpec requires exactly one error. This correction remains pending native verification.

Evidence: `.simple/storage/build/phase3-mir-owner-scratch-cycle1-20261016/nominal-result.json` (SHA256 `99f7d5eaecd3a9f9d169140866bf830718c27233ec0668417101a802483d4933`), with the matching supervisor receipt and `missing-owner-repair/actual-small-result.json`. The run took 55.9 seconds, peaked at 530856 KiB, and ended quiescent; both runtime-binding checks passed. The combined scratch/token probe was held because the small negative gate failed. No full-host, SSpec, or RSS-improvement claim follows from these positive cases.

## Corrected missing-owner result

Compiler `bd86d7aceeb0e0de2dfb55b0bf3fdafc837c05b2bbea5c101e9ea14c8024e0f3` now refuses the missing method with exactly one `unresolved method call: only_other` diagnostic, no undefined `Counter` message, and no executable. The expected compile refusal is the negative PASS; there is no runtime execution for this case. Result `.simple/storage/build/phase3-mir-owner-scratch-cycle2-20261016/nominal-result.json` has SHA256 `b499ddcad4ede84d6c4afe9e48d8c4e4b1be05e17bcf463f75f1b38bde9c0092`. Both runtime bindings passed; the owner ended quiescent at 110676 KiB in 8.86 seconds. Earlier positive cases retain their `209d55d9` results and were not replayed.

The subsequent larger scratch/token native compilation exceeded its memory cap before executable output. This leaves those separate assertions and full-host qualification unrun; it does not invalidate or broaden these small native owner-resolution results.
