# ARM64 ABI and native values review — 2026-11-03

Source: `/tmp/simple-arm64-macos-bug-db-20261103`, release commit `a41511004a0`. Read-only bug detail queries used canonical `bug-claim.shs show --intent not_for_fixing`. Initial historical review was read-only; the independent direct-native gap now has the scoped candidate below. No native build, interpreter substitute, or status closure is claimed.

## Scoped registered rows

| Bug | Source findings | Recommended status | Required evidence |
|---|---|---|---|
| arm64_framebuffer_color_struct_return_abi_2026-08-21 | `src/os/drivers/framebuffer/fb_driver.spl:50` declares `FbColor`; `rgb` returns `FbColor`. Current tracking doc records historical native small-struct controls and PR #5982 rename. Generic ABI failure is not established by the old Color collision. | Keep fix-implemented-verification-pending | Same admitted ARM64 compiler passes exact color/adjacent aggregate fixtures, then fresh attested real-firmware QEMU reaches desktop-ready with nonblank device-origin capture and retained serial/QMP. |
| stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05 | Current fn-parameter regression covers indirect-call diamond; `method_calls_literals.spl:3291,3384` selects `rt_dict_len`; `:2274` emits fatal unresolved-method diagnostic. Historical map/closure/native results have no fresh producer-matched proof here. | Keep open | Five distinct historical probes, compiled and executed with current admitted compiler; missing `Dict.size` must reject with relevant diagnostic. |
| stage2_native_f64_arithmetic_lowered_as_integer_ops_aarch64_2026-09-05 | `expr_dispatch.spl:6059`/`:6074` lower floating literals; `mir_lowering_stmts.spl:542` detects float locals and `:1527` retains initializer owner; `expr_dispatch.spl:5316` selects float binop result. These source paths contradict a justified blind repatch of the old missing-local-type hypothesis, but do not prove native correctness. | Keep open | Historical typed/inferred/literal/function-return arithmetic and signed compare probes on recorded actual default/LLVM backend, target and runtime. |

## Independent current direct-native gap

`src/compiler/70.backend/backend/native/isel_aarch64.spl:50` (`a64_lower_const`) falls through float constants to MOVZ zero. `:562` (`a64_isel_binop`) selects integer ADD/SUB/MUL/SDIV without operand types. `a64_isel_function` passes arguments in integer x registers. `native/mod.spl:96` exposes this through `compile_native_aarch64`; there is no module float admission check. This is direct-native backend source evidence, not proof that the historical Stage2 default-backend failure has the same cause.

Proposed new P2 ID: `native_aarch64_scalar_float_silent_integer_lowering_2026_11_03`. Minimal honest repair is explicit unsupported-scalar-float rejection before emission, covering function signatures/locals and inline float constants. Full support needs FP ABI, register allocation and encoding and should not be invented as a narrow change. Proposed repair awaits canonical DB registration/claim coordination.

## Probe package

`/tmp/parallel-three-tracks-20261103/bugs/arm64-native-probes/` contains six standalone fixtures and README with exact acceptance: indirect parameter, array map, captured closure, dict length, missing dict size (negative compile), f64 arithmetic. All are UNEXECUTED; no build token granted. Positive probes use numeric failure exits and exact PASS markers. A missing provider, timeout or unrelated error cannot count as negative acceptance.

## Additional test debt

`test/01_unit/compiler/mir/local_float_type_source_spec.spl` still reads `expr_dispatch.spl` and expects the float helper there; actual helper lives in `mir_lowering_stmts.spl` with split F32/F64 arms. This source-string-only test is stale. No string-test churn was made; behavior-focused probes above are the appropriate acceptance basis.

## Direct-native repair candidate

Canonical bug ownership acquired by parent: `native_aarch64_scalar_float_silent_integer_lowering_2026_11_03`, session `arm64-native-float-20261103`, 2026-11-03T09:55:13Z.

Candidate commit `f93c5e7dca4` in `/tmp/simple-aarch64-native-float-reject-20261103` adds an `E-BACKEND-A64-FLOAT` rejection before function selection for scalar float signature/local types and before constant selection for lexical/decoded floats, including erased constant types. Structural arrays/slices/tuples/unions/results and callback signature params/declared params are traversed. Pointer/reference transport and named Struct/Enum field metadata are explicitly outside this scalar guard. The change does not implement FP instructions or affect LLVM.

Six behavioral unit cases exercise the actual admission predicates and positive integer selector. Two standalone negative fixtures invoke the actual function/constant selectors and require the exact diagnostic with nonzero termination. All new `.spl` tests remain UNEXECUTED pending an admitted pure-Simple runner; full compiler/lib/MCP checks are also pending. Only `git diff --check`, both direct-env guards, and executable-spec doc-layout count (zero) passed. Local checkpoint commit was created with hooks disabled; it is not a verification admission or merged change. Astra review requested from `/root/astra_feature_bug_review`. Do not close or promote the bug on these source-only results.

## Execution hold

Root confirmed no admitted runtime is currently available and explicitly prohibited landing the untested production candidate. Candidate remains committed and unlanded. Rebuilt P2 sanity may permit compiler-focused fixtures; general SSpec requires an admitted full CLI. Astra source review may proceed but cannot substitute for runtime checks. Bound OR-patterns used by the new validator match current HIR source idioms (`hir_lowering/statements.spl:882`, `pattern_enum_substitution.spl:21/47`); no syntax workaround was introduced.
