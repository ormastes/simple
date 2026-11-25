# Cranelift rejected runtime-initialized float globals

- **Status:** FIXED (source/unit/cross-target contracts; fresh execution pending)

**Verification 2026-11-25 (work/p2w1-af-20261125, release/1.0.0):** verified by
code inspection. `cranelift_static_init_supported`
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:450`) now has an
explicit `case F32 | F64:` arm (:454) that accepts nil-backed
(`not static_.init.?`), `Zero`, `Float(_)`, and `FloatLexeme(_)` initializers
and fails closed on anything else — the "Cranelift rejects F32/F64 statics"
defect this record describes no longer exists in the tree. Fresh Cranelift
execution remains pending: no Cranelift native-build producer is available on
this Windows host (cargo/rust builds are off-limits in this lane), so the
execution half of the evidence could not be re-run here.
- **Severity:** high
- **Backend:** Cranelift

## Reproducer

```simple
fn init_ratio() -> f64: 3.5
val ratio: f64 = init_ratio()
fn main() -> i64:
    if ratio * 2.0 == 7.0:
        return 0
    1
```

LLVM emitted zero-backed storage and a runtime store. Cranelift rejected the
same MIR static before code generation.

## Root cause and fix

`cranelift_static_init_supported` excluded F32/F64 even though the shared MIR,
Cranelift type mapping, global declaration runtime, and LoadGlobal/StoreGlobal
paths already support them. The scalar storage gate now accepts both float
types only when their initializer is nil/zero-backed. Float, integer, and bool
literal payloads still fail closed instead of being reinterpreted as raw float
bits.

## Evidence

- Focused unit coverage accepts nil-backed F32/F64 and rejects float or integer
  literal payloads for F64 storage.
- The shared cross-target fixture initializes F32/F64 through calls and checks
  exact binary values `3.5` and `7.0`.
- Existing hosted, FreeBSD, AArch64/RV64 execution and
  ARM32/RV32/Windows-ARM64 object schedulers inherit the fixture.
