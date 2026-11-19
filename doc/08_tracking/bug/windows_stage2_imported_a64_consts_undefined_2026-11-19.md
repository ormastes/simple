# Windows Stage 2 link: imported `A64_*` constants are undefined under the `bootstrap_main` prefix

- **Found:** 2026-11-19, during the DHR phase-3 build (`doc/03_plan/app/debug/dhr_debug_spy_replay_recovery_plan_2026-11-17.md`)
- **Tree:** `release/1.0.0` @ `b7214ff88aa`
- **Host:** Windows 11, x86_64-pc-windows-gnu, pinned llvm-mingw 20260922
- **Status:** open

## Command

```bash
SIMPLE_USER_STORAGE_ROOT=/d/dev/simple-user-storage SIMPLE_TOOLCHAINS_ROOT=/d/dev/simple-toolchains \
TMPDIR=/d/dev/tmp TMP=/d/dev/tmp TEMP=/d/dev/tmp \
bash scripts/bootstrap/bootstrap-windows.sh --full-bootstrap --stop-after-stage2 \
  --mode=dynload --jobs=half --backend=cranelift
```

The Rust seed and Stage 1 built cleanly. The Stage 2 native build of `bootstrap_main.spl` failed at link:

```
Build failed: link failed: 20 undefined symbol(s) with SIMPLE_NO_STUB_FALLBACK=1:
app__cli__bootstrap_main__A64_BRANCH26_MAX_BACKWARD_BYTES_V1, ..._A64_BRANCH26_MAX_FORWARD_BYTES_V1,
..._A64_OP_ADD, _ADD_IMM, _ADRP, _AND, _ASR, _B, _BEQ, _BGE, _BGT, _BL, _BLE, _BLT, _BNE, _BRK,
_CBNZ, _CBZ, _CLZ, _CMP
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

`ld.lld` stops at its default limit of 20 errors. The list is alphabetical and stops at `A64_OP_CMP`, so the remaining imported `A64_OP_*` constants are very likely undefined too.

## What the symbols are

These are ordinary `pub const`s imported by brace list into other modules:

- `A64_OP_*` are defined in `compiler.backend.native.mach_inst`. They are imported by `backend/native/encode_aarch64.spl:17` and `isel_aarch64.spl:24`.
- `A64_BRANCH26_MAX_*_BYTES_V1` are defined in `src/lib/common/isa/a64_encode_v1.spl:12`. They are imported by `src/lib/common/trace/observer_native_map_v1.spl:8`. That module came in with `767555ceeb9` (refactor(xray): shared common ELF/ISA/LE modules).

At link time each reference is named with the **entry module's** prefix (`app__cli__bootstrap_main__`) rather than the defining module's. No object defines that name. The constant reference is being mangled into the importer's or entry's namespace instead of resolving to the defining module's global, or being inlined.

## Not caused by

The DHR changes merged before this build (#10357 through #10379) touch only `src/lib/**`, `src/os/**`, specs, scripts, and docs. None of them is in the compiler or the AArch64 backend. DHR-OFF-01 also measures 0 DHR provider modules in the compiler-kernel closure.

## Next step

Reproduce with a two-module fixture: module A has `pub const K = 1`, module B imports `{K}` and uses it in an expression, and the entry imports B. Build it with the Stage 1 compiler's `native-build` on Windows gnu/cranelift. Then compare the emitted symbol name for `K` against the Linux lane before changing the mangler.
