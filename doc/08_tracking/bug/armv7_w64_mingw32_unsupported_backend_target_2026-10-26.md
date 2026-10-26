# armv7-w64-mingw32 Unsupported Backend Target (2026-10-26)

**Issue:** `armv7-w64-mingw32` target rejected as unsupported by the backend plugin system.

**Location:** `src/compiler/70.backend/backend_plugin/builtin_adapter.spl:130-143`

The `builtin_backend_target` function enumerates supported targets for the built-in LLVM and Cranelift backends. Currently supported:
- host, native
- x86_64, aarch64, riscv64, riscv32
- x86, arm

**Decision:** FILED, not added for 1.0.0

**Rationale:**
- Windows-on-ARM32 (armv7) is deprecated by Microsoft
- No llvm-mingw armv7 lane exists in CI
- Phase-4 target matrix should mark as expected-unsupported or drop entirely

**No action taken:** Target remains unsupported. Phase-4 target matrix definition will address deprecated/unsupported tiers.
