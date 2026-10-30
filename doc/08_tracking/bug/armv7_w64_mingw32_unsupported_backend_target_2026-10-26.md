# armv7-w64-mingw32 Unsupported Backend Target (2026-10-26)

**Issue:** `native-build --target armv7-w64-mingw32` (arm32 Windows, llvm-mingw ABI) fails. 32-bit `arm` itself is a supported architecture; the unsupported piece is the arm32 `w64-mingw32` Windows ABI/triple.

## Reproduction

```
# hello.spl: fn main(): print "hi"
C:/dev/simple/bin/simple.exe native-build hello.spl --target armv7-w64-mingw32 -o hello_out
```

Result (2026-10-26, Rust seed `bin/simple.exe`, default Cranelift backend), exit 1:

```
codegen init: Unsupported target architecture: Cranelift native builds do not support hosted armv7 yet; use --backend llvm for this lane
```

Retrying with `--backend llvm`:

```
error: native backend 'llvm' is not available in this build; rebuild the Rust driver with --features llvm or use --backend cranelift
```

The LLVM lane could not be exercised with the available seed, so whether LLVM would accept `armv7-w64-mingw32` is NOT verified.

## Where it is rejected

- Seed (what the repro hits): `src/compiler_rust/compiler/src/codegen/common_backend.rs:1195-1200` (`create_isa_from_settings` rejects `TargetArch::Arm | Riscv32` for Cranelift).
- Pure-Simple plugin path (not reached by the seed repro): `builtin_backend_target` in `src/compiler/70.backend/backend_plugin/builtin_adapter.spl:130-143` matches ARCH names (`x86_64`, `aarch64`, `riscv64`, `x86`, `arm`, `riscv32`, `host`, `native`), not triples, so `arm` passes there. Unsupported names yield `BackendPluginError.TargetUnsupported` (`BACKEND_PLUGIN_TARGET`, `src/compiler/00.common/backend_plugin/receipt.spl:37`); a backend lacking the target does the same at `builtin_adapter.spl:194`. I did not reproduce that code path.
- Toolchain mapping: `src/compiler/70.backend/backend/llvm_cross_target.spl:307-313` (`toolchain_armv7`) maps Windows to `armv7-pc-windows-msvc`; there is no `armv7-w64-mingw32` mapping.

## Decision

FILED, not added for 1.0.0.

- Windows-on-ARM32 (armv7) is deprecated by Microsoft.
- No llvm-mingw armv7 lane exists in CI.

No action taken; the target remains unsupported. No plan document currently defines a target matrix tier for it (none found under `doc/03_plan`).
