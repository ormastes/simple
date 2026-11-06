# BUG-X86-EVEX-STATIC-ARRAY-INFERENCE-20261017

Date: 2026-10-17. Status: open compiler inference bug; source workaround drafted.
Authoritative DB reconciliation pending; no qualified DB tool is available.

Immutable producer: 0015c3fe0dfd28c22e55cbe488636f30e5baa869d1608cad4847685b9c553429.
Original source: 15f7ca45871b1250abf44c91efb6004625035035.
Recovery reference: actual tiny-source commit c6e8c8a43b64670c96d244aab7a14ad7c8661131.

Focused cycle two admitted a genuine co-located source snapshot, then MIR
reported unresolved module-static initializer types at
`src/compiler/70.backend/backend/native/_X8664Avx512/evex_encoding.spl:82:27`
and `:110:25`. The arrays are X86_ZMM_ALLOCATABLE (register IDs 48..79) and
X86_K_ALLOCATABLE (81..87). Their constants are integral register IDs and
downstream helpers use i64 register operands. Explicit `[i64]` array annotations
retain every element and its order and avoid the producer's inference failure.

Both temporary annotations have immediately preceding canonical workaround
tags. The intended recovery is removal of annotations only after the inference
owner accepts the original unannotated declarations under the same focused
regression. These annotations do not fix the compiler inference owner.
Actual diagnostic workaround commit:
07f13d853d0f917593aff3673ae27712a3240ed1 in the genuine owned co-located probe
repository. The separately reviewed production source change remains a draft.

Evidence: co-located-cycle2/compile.log and resource-guard.receipt in the parent
evidence directory. MIR: 64 modules, 62 succeeded, two failed modules (this
module plus the independent parse_i32 defect). Exit 1; objects 0; no executable.
Background owner: compiler MIR module-static type inference.

Focused cycle three passed MIR65/65 and emitted54 new AMD64 COFF objects,
clearing the original inference failures with both annotations present.
Compiler exit was1 during runtime discovery because the tiny source checkout
has no src/runtime; --runtime-path supplies runtime artifacts, not C sources.
Strict completion then linked those54 new objects with the canonical entry
and38 independently hash-verified C1 runtime objects. The sole native run
exited0 and emitted the exact expected PASS line (80 stdout bytes, empty
stderr), exercising both complete register arrays, original imm64 cases and
fourteen signed-i32 parser cases. Executable pre/post SHA256:
724f23e723bbc4ab8f9f77d57284f6d10f156c225f120d14a95ea884a81024bf.
Production workaround commit: 1c972e8e689. Broad compiler/lib/MCP qualification
and the dedicated BDD runner remain unrun. The inference owner is still open.

## Triage 2026-11-04 (opus-n88b)

Workaround: typed [i64] literal over val constants kept at evex_encoding.spl:82.
Fixture: test/04_smoke/static_val_array_infer_native.spl (interpreter lane passes).
Stage3 repro: `bin/simple native-build --entry test/04_smoke/static_val_array_infer_native.spl --output build/static_arr && build/static_arr` -> 4 / STATIC_ARRAY_OK.
Status: open. workaround in place; native repro fixture added; real producer fix still needed.

## Fix 2026-11-06 (work/x86-simd-bugs)

Real repro (unannotated, not the workaround form):
`test/04_smoke/static_val_array_infer_unannotated_native.spl` — stage3
`s3_fable46.exe` (copy) native-build fails MIR with
"cannot derive module static type from unresolved initializer" (reproduced).
Root cause: `lower_static`'s Infer branch never consulted
`infer_unfolded_static_expr_type`, which had no `ArrayLit` arm, so an array
visited before its element constants (production `lower_module` order) had no
type evidence. Fix: `src/compiler/50.mir/_MirLowering/module_lowering.spl`
adds an `ArrayLit` arm (declared const type first, then initializer; all
elements must agree exactly — no width/sign/kind coercion) and uses it in the
Infer branch. Spec `test/01_unit/compiler/mir/unannotated_module_array_static_type_spec.spl`
red 2/6 before, 6/6 after (seed interpreter); siblings
`unfolded_module_binary_static_type_spec` 6/6 and
`unannotated_module_global_static_type_spec` 12/12 unchanged.
Not run: native green, needs a stage3 rebuilt with this fix. The `[i64]`
annotations in `evex_encoding.spl` stay until that redeploy (removing them now
would break building with the current stage3). AVX-512 execution: not run
(host Xeon E5-2673 v4 has AVX2, no AVX-512F) — this bug is compile-time only.
