# Direct native AArch64 silently lowers scalar floats as integers

Priority: P2. Status: fixing; source diagnosis, native post-fix validation pending.

The direct native AArch64 backend `a64_isel_binop` emits integer ADD/SUB/MUL/SDIV without float dispatch; `a64_lower_const` emits zero for float constants. The direct `compile_native_aarch64` route can therefore silently produce wrong scalar floating-point behavior. This is distinct from the September 5 default Stage-2 f64 report: equivalence of its producer/backend has not been established.

Repair scope: reject unsupported floating-point functions/constants with an explicit diagnostic until floating-point registers, ABI and instruction encoding are supported. This prevents silent corruption; it does not implement scalar floating-point support and does not change LLVM lowering. The source owner must bound nested aggregate/signature behavior and keep supported integer compilation working.

Acceptance: behavioral checks reject float signatures, local types and constants with the diagnostic; integer controls remain accepted; native negative fixture fails explicitly through the direct backend. Record exact producer/source/backend. No native pass or historical bug closure is claimed by registration.

Repair owner: arm64-native-float-20261103. Independent source review: `/tmp/parallel-three-tracks-20261103/bugs/arm64-native.md` (session artifact).
