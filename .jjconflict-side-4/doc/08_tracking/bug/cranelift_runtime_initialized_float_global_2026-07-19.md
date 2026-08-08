# Cranelift rejected runtime-initialized float globals

- **Status:** FIXED (source/unit/cross-target contracts; fresh execution pending)
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
