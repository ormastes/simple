# C Runtime Exclusion Analysis

**Date:** 2026-05-18
**Context:** Pure Simple conversion project — which C files can be removed

## Removed (zero callers)

| C File | Symbols | Action |
|--------|---------|--------|
| `runtime_ctype.c` | `__is_alnum/alpha/digit/xdigit/space/lower/upper` | Deleted. Rust shim had zero pub fns. Removed from tools.rs. |
| `runtime_audio_effects.c` | `rt_audio_set_pitch` + 6 stubs | Deleted. Not in tools.rs. Zero .rs/.spl callers. |

## Cannot Remove (active Rust/codegen callers)

| C File | Symbols | .rs Callers | .spl Callers | Why It Stays |
|--------|---------|-------------|-------------|-------------|
| `runtime_math.c` | 27 (`rt_math_*`) | interpreter, sffi shim | 12 files | Interpreter calls C via Rust FFI; transcendentals need libm |
| `runtime_random.c` | 8 (`rt_random_*`) | interpreter, sffi shim | 10 files | Interpreter + crypto/session callers |
| `runtime_contracts.c` | 2 (`simple_contract_check*`) | codegen emits direct calls | 3 files | Core compiler infrastructure — codegen hardcodes symbol |
| `runtime_error.c` | 2 (`rt_function/method_not_found`) | ~10 codegen files | 2 files | Core codegen — every unresolved call falls through here |
| `runtime_time.c` | 18 (`rt_time_*`, `rt_timestamp_*`) | 8+ files | **199 files** | Most used runtime module; syscall wrappers |

## Path to C Removal for Remaining Modules

For math/random: replace Rust shim's C FFI with native Rust calls (e.g.,
`c_sffi::rt_math_pow(base, exp)` → `base.powf(exp)`). Then the C file is dead.

For contracts/error: these are codegen-emitted symbols. Removal requires the
native-build linker to resolve them from Simple-compiled objects instead of the
C archive. Blocked by the cross-module ABI bug.

For time: syscall wrappers (`clock_gettime`, `gettimeofday`). Must stay native.
The pure Simple `time_utils.spl` provides civil-date arithmetic on top.

## Pure Simple Replacements (coexist with C)

These serve Simple code via `use std.common.X`. They do NOT replace the C
symbols — they provide equivalent functionality at the stdlib layer.

| Module | File | Tests |
|--------|------|-------|
| ctype | `src/lib/common/ctype.spl` | 9/9 |
| math | `src/lib/common/math/math.spl` | 13/13 |
| error | `src/lib/common/error/error.spl` | 4/4 |
| contracts | `src/lib/common/contracts/contracts.spl` | 8/8 |
| random | `src/lib/common/random_pure.spl` | 21/21 |
| time_utils | `src/lib/common/time_utils.spl` | 53/53 |
| audio_effects | `src/lib/common/audio_effects.spl` | 7/7 |
