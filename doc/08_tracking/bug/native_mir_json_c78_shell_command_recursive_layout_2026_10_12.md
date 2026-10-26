# Committed ShellCommand direct self-reference blocks native MIR qualification

Date: 2026-10-12. Status: OPEN pending native regression/qualification; narrow existing upstream repair selectively backported as812442947d9cfc8448809c00a562c9468a17d103. Bug DB reconciliation pending; no qualified DB mutation performed. This report does not close the broader MIR JSON allocation defect.

Producer: `a6b18fd84c5f88a48afa0beaf61434f39678155fb0f0ed01127db25a28cf5078`. Frozen source: `c78cfd47a59902bbe814c85cbe8e4fe3cc964eaf` plus private MIR JSON three-join candidate. Request SHA256: `132a684a36e0d5d80057d0f158eb025eec118e8741ae87a4b60f53da399ad0d8`. Controller SHA256: `9ca659842b0a2d3ed3fc5f2a8905be1620b8642e41e83ade4b7499c88798f947`. Result SHA256: `d628c8835679a370ba4c8f2bdf45a5082693d3991caa858f9be579bff4725d6d`. Log SHA256: `12c547ae0f815ba8fd2920079b5016b67a4646dbeb9d252a89405eedd1434c84`. Receipt SHA256: `a8f1e5fc1e494b9dca37094e8bea57dcce6b85f4e9cde9e3a0afc584aedca5ab`.

Evidence directory: `build/native_probe/mir-json-perf-review-20261012-astra/native-criterion-attempt1/`. Exact terminal summary is `TERMINAL_REVIEW.json`; raw output and Windows Job closure are `compile/child.log` and `compile/receipt.env`. One compile exited1 in36.619s, peak239148KiB; all children closed and pinned inputs unchanged. Ordinary-zero, ordinary-small and nul-small runtime cases are UNEXECUTED. No parity or performance claim follows from HIR completion.


## Actual failure and cause

Native source resolution selected56 modules and HIR completed56/56. Post-HIR validation emitted exactly one fatal cycle: `ShellCommand.pipe_to -> ShellCommand` in `src/compiler/15.blocks/blocks/value.spl`. Frozen c78 declares `has_pipe_to: bool` and `pipe_to: ShellCommand`; the latter is direct by-value recursion, not an optional type. A boolean discriminator does not make its physical storage indirect. The failure is legitimate; do not weaken layout checking or mark this an Optional mislowering.

The retained producer's admitted source already uses `[ShellCommand]` with zero/one cardinality and a matching generated array encoder. Both owners authenticate against its source snapshot. Upstream9fa97fdd63332d52b96961ea9505be9b4ac6e04e contains the same scoped repair. Root selectively backported only these owners as812442947d9cfc8448809c00a562c9468a17d103; unrelated loader/generated-header changes are excluded. A duplicate fix PR is unnecessary.

## Required repair and caller review

The narrow repair makes `pipe_to` a dynamic array and changes only `ast_semantic_encode_shell_command` to hash its length and children. Updating storage alone leaves the old scalar encoder caller incorrect. Owned compiler/app/lib source search found no constructor or read of this compiler ShellCommand outside its declaration and generated encoder; the LLM Caret ShellCommand type is unrelated. The actual generated reader checks `has_pipe_to`, iterates storage and has no unchecked index. No free, ownership transfer, or shared mutation is added. Zero/one is a representation invariant, not enforced by a public constructor; this limitation must remain explicit.

`layout-cache-followup/CLOSURE_CYCLE_SCREEN.json` records the scoped preflight: ShellCommand is the only direct-self lexical candidate in the58 captured owners; TypeInfo is absent. This screen does not establish symbol-resolved indirect-cycle absence. Prior native validation, rather than lexical inspection, is the evidence for the one diagnosed cycle.

## TDD evidence and remaining gates

The actual attempt1 failure is RED. Unexecuted regressions are under `build/native_probe/mir-json-perf-review-20261012-astra/layout-cache-followup/tests/`: real-owner storage tests cover empty/single pipelines,32 repeated vector appends preserving earlier values,8-link extension and bounded traversal; real generated encoder tests cover stable hashes and child sensitivity. Direct and mutual by-value negative cases must stay rejected. Optional recursive storage is separately authored as characterization; it must not be silently treated as the failing direct-self case.

A native retry requires a separately reviewed attempt2 request against the new commit and explicit private frontend/HIR roots. Maximum3 criterion attempts; attempt1 is consumed. No unchanged retry or broad closed-cohort replay is authorized by this report.
