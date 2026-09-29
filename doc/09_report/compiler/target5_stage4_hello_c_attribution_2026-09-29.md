# Target 5 Stage4 hello C attribution (Linux ARM64, 2026-09-29)

Status: diagnostic only. This comparison does not satisfy the BS7 matched C
size gate, because the exact runtime archive and link manifest used by the
saved Simple hello were not retained with that output. The saved Simple binary
also comes from worktree revision `9959372d9582804c0185e9fa0e28da2be3805954`,
not a fresh build of this branch.

All three binaries run and print `Hello World`. The C programs used Clang and
lld 23.1.0, `-Os -fPIE -ffunction-sections -fdata-sections`,
`-Wl,--gc-sections -Wl,-z,now -pie`, and `llvm-strip --strip-all`.
The Simple output is the previously recorded exact Stage4 diagnostic at
`simple-target5-native-fix/build/mini_builds/target5_composed_stage4/hello_owner_substr_stripped`.

| Program | Stripped bytes | Difference from Simple | Ratio, Simple / C |
| --- | ---: | ---: | ---: |
| Stage4 Simple hello | 13,544 | — | — |
| Plain C `puts` hello | 4,808 | 8,736 | 2.82 |
| C with the Simple entry calls and available core-C archive | 7,744 | 5,800 | 1.75 |

The closer C source is in
`doc/09_report/compiler/evidence/target5_hello_same_entry_c_20260929.c`.
It calls `spl_init_args`, the weak startup-aspect hook, runtime init and
shutdown, and `rt_println_str` from `__simple_main`. Its linked archive was
`native-objects-goZCXm/core_c_runtime/libsimple_runtime.a`, SHA-256
`9daa6142839e612169ffca2780868fa123e28e8883abd9a40b9ff188b77f1d2e`.
This is an available archive from the older worktree, not an exact retained
input receipt for the saved Simple hello. The C binary names `libm.so.6` and
`libc.so.6`; the Simple binary names `libc.so.6` and the ELF loader. They are
therefore not a matched link pair.

The unstripped Simple binary attributes 4,240 bytes to `.text` versus 1,528
bytes in the closer C binary. It has 32 undefined dynamic function imports
versus 18 in that C binary. Its retained code includes
`spl_init_args` -> `rt_install_crash_handler`, the startup-aspect loader,
SIMD text initialization, and profiler setup. `dlopen`/`dlsym` are dynamic
imports even for this no-import hello. Those facts identify runtime and
startup closure work; they do not prove that an optional provider loaded.

Next: retain the exact Stage4 hello linker arguments, entry shim, runtime
archive hashes, map, and provider/NoGC trace. Build the C comparator from
those same inputs and check the 1.05 ratio. Then cut retained startup/runtime
roots only under a verified feature-closure policy and run paired startup/RSS
samples. The earlier 30-pair Simple/Python result is separate evidence and
does not qualify this size comparison.
