# Direct native AArch64 silently lowers scalar floats as integers

Priority: P2. Status: fixing; source diagnosis, native post-fix validation pending.

The direct native AArch64 backend `a64_isel_binop` emits integer ADD/SUB/MUL/SDIV without float dispatch; `a64_lower_const` emits zero for float constants. The direct `compile_native_aarch64` route can therefore silently produce wrong scalar floating-point behavior. This is distinct from the September 5 default Stage-2 f64 report: equivalence of its producer/backend has not been established.

Repair scope: reject unsupported floating-point functions/constants with an explicit diagnostic until floating-point registers, ABI and instruction encoding are supported. This prevents silent corruption; it does not implement scalar floating-point support and does not change LLVM lowering. The source owner must bound nested aggregate/signature behavior and keep supported integer compilation working.

Acceptance: behavioral checks reject float signatures, local types and constants with the diagnostic; integer controls remain accepted; native negative fixture fails explicitly through the direct backend. Record exact producer/source/backend. No native pass or historical bug closure is claimed by registration.

Repair owner: arm64-native-float-20261103. Independent source review: `/tmp/parallel-three-tracks-20261103/bugs/arm64-native.md` (session artifact).

## Landed repair — 2026-11-05

PR #6835 (merged into release/1.0.0, commit 0755bf39cf5) implements the
accepted rejection scope:

- `a64_module_float_rejections` scans each function's return type, parameter
  types, local types and const instructions for F32/F64/Float/FloatLexeme.
- `isel_module_aarch64` panics with the first diagnostic before lowering;
  `a64_lower_const` panics on operand-carried float constants (defense in
  depth) instead of emitting MOVZ #0.
- Integer-only programs are unaffected.

Evidence: `test/01_unit/compiler/backend/native/aarch64_float_rejection_spec.spl`
(5 scenarios) PASS under the Rust seed interpreter on an aarch64 Linux host;
manual at `doc/06_spec/01_unit/compiler/backend/native/aarch64_float_rejection_spec.md`.
Neighbor specs re-run unchanged (isel_aarch64 5/5, emission_order_determinism
2/2, global_addr contract 12/4 = pre-change baseline). Full `check
src/compiler` remains pending on an admitted self-hosted binary; native
post-fix validation is still not claimed — scalar FP support itself is not
implemented, per the repair scope.
