# LLVM/clang Toolchain Port Layer Expert

## Role

Own layer-specific process knowledge for the **`x86_64-unknown-simpleos` LLVM
toolchain port**: the `ormastes/llvm-project` fork, the three-stage cross build,
the CMake toolchain file that decides whether outputs are guest-runnable, the
SimpleOS sysroot (crt0, libc/libm/libc++ archives, headers, linker script), and
the C runtime archives the Simple payload links against.

This layer's public contract is **the guest-runnable ELF**: `Type=EXEC`, entry
`0x40000000`, **zero INTERP segments**, static.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Layer Links

- **Cross CMake toolchain file (the load-bearing one):**
  [src/os/toolchain/llvm/simpleos_cross_toolchain.cmake](../../../../src/os/toolchain/llvm/simpleos_cross_toolchain.cmake)
- Build driver: [src/os/port/llvm/build.spl](../../../../src/os/port/llvm/build.spl)
  (`LLVM_REPO` :70, `LLVM_REVISION` pin :71) and
  `src/os/port/llvm/build.shs` (stages `host-tools` / `cross` / `compiler-rt`;
  it does **not** checkout the pin — it uses `$LLVM_SRC`).
- Sysroot generator: `src/os/port/llvm/sysroot.shs`
  (`:266` rewrites `libm.a`; also builds `libsimple_runtime_native.a`).
- compiler-rt: `src/os/port/llvm/compiler_rt_cmake.cmake`
- Fork patch docs: `src/os/port/llvm/patches/00NN-*.patch.md`
- **DEPRECATED:** `src/os/port/llvm/clang_static.shs` — a static relink of the
  stage-2 objects, kept only as a legacy fallback. Its outputs
  (`build/os/clang_static/bin/clang_static`, `build/os/.bake_include_toolchain`)
  are genuinely absent and are no longer needed for a guest-runnable image.
- libc / crt0 (owned jointly with
  [os_kernel_exec](../os_kernel_exec/skill.md)): `src/os/libc/` —
  `simpleos_crt0.S`, `simpleos_libc.c`, `simpleos_cli_args.c`,
  `simpleos_fs.c`, `simpleos_process.c`, `simpleos_libc.h`, `Makefile`
  (`C_SRCS`), `libsimpleos_c.a`.
- Runtime source ported into the sysroot: `src/runtime/runtime_native.c`.
- Sysroot layout: `build/os/sysroot/{lib,include,share/simpleos}` —
  `crt0.o`, `libsimpleos_c.a`, `libm.a`, `libc++.a`,
  `libsimple_runtime_native.a`, ~35 headers,
  `share/simpleos/simpleos.ld` (ENTRY `_start` @ `0x40000000`, static-only).
- Downstream feature expert:
  [simpleos_toolchain_selfhost](../../feature_expert/simpleos_toolchain_selfhost/skill.md).

## Public Contract Facts (2026-08-06)

1. **Guest-runnable is produced by two flags in the CMake toolchain file:**
   `-static` **plus** `-Wl,-T,<sysroot>/share/simpleos/simpleos.ld`. Without
   them the host clang driver **defers the link to gcc** and emits a
   Linux-dynamic ELF with an INTERP segment that the SimpleOS FS-exec loader
   cannot run. If a build regresses to dynamic output, check these flags before
   anything else — and do **not** reach for the deprecated `clang_static.shs`.
2. **Current artifacts (AC-2 DONE):**
   `build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20` — 127,572,072 B,
   sha256 `8554035d57523bbf8a62aedd…`; `bin/lld` — 64,526,504 B, sha256
   `bf1da1aece19814a0df3a381…`. Both EXEC / `0x40000000` / 0 INTERP.
   compiler-rt builtins installed to
   `build/os/sysroot/lib/clang/20/lib/x86_64-unknown-simpleos/`.
3. **Fork:** `github.com/ormastes/llvm-project`, branch `simpleos`, Clang 20,
   local checkout `/home/ormastes/llvm-project`. Tip and pin are both
   `596122063` (`59612206386553df81efc06ec0421acf646d49ef`), verified with
   `git ls-remote`. Note: `toolchain_selfhost_bootstrap_plan.md` §4 lane F1 still
   says "bump to `92fa40246`" — that line is **stale**; the plan's own §0
   ground-truth row and the guide both agree on `596122063`, matching disk.
4. **A stage-2 ninja exit is not a done toolchain.** Stage 3 (`compiler-rt`) is
   required to stage target builtins. And the stage-2 `bin/clang-20` used to link
   as a Linux dynamic ELF — see fact 1.
5. **`libsimple_runtime_native.a` is 8 objects, one `.o` per source, never
   `ld -r`** (`runtime_native, runtime_simd_utf8, runtime_contracts,
   runtime_memory, runtime_time, runtime_timestamp, runtime_pool,
   runtime_memtrack`). Archive-member granularity is how layering is enforced
   here; merging objects re-creates the leak class below.
6. **The seed linker accepts exactly three inputs** — `crt0.o`,
   `lib/libsimple_runtime.a`, `lib/libsimpleos_c.a` —
   hardcoded at `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:207`.
   There is no fourth slot, which is why the native runtime archive is merged in
   with `ar r` (`scripts/os/simpleos-native-build.shs:129` overwrites
   `build/os/sysroot/lib/libsimple_runtime.a`).

## Traps Owned by This Layer

- **A CMake `check_*_compiles` FATAL_ERROR names the PROBE, not the cause.**
  Observed: `libstdc++ version must be at least 7.4.` and `Host compiler appears
  to require libatomic` — both false; the real error
  (`ld.lld: error: undefined symbol: rt_array_len`) appeared only in
  `CMakeFiles/CMakeConfigureLog.yaml`. Always read that file and replay the probe
  link by hand.
- **Derived archive copies reproduce a fixed error.** `libm.a` is a `cp` of
  `libsimpleos_c.a` (`sysroot.shs:266`) and `-lm` precedes
  `-Wl,--start-group -lc++ -lsimpleos_c -lm`. A stale copy made a correct fix
  look like no fix. `cmp` the two and compare mtimes when a fix "doesn't take".
- **Concurrency hazard:** the cross build links against `build/os/sysroot/lib/`
  while `sysroot.shs` rewrites `libm.a`. **Never regenerate the sysroot while a
  cross build is linking.** Stage to a scratch sysroot and swap, or wait for
  ninja to exit.
- **Archive members link per-OBJECT.** A bridge sharing a TU with core libc makes
  its dependency mandatory for every consumer. Localise with `nm -u` per member
  (`nm -u simpleos_libc.o` vs `nm -u simpleos_cli_args.o`), not per archive.
- **Defensive definitions must be `.weak`, never `.globl`** — the `environ`
  duplicate-symbol failure (`crt0.o:(.bss+0x0)` vs
  `simpleos_process.o:(.data+0x0)`) killed the lld link after 2,247 of 2,944
  targets. But note the symmetric hazard the `.globl` was originally fixing: a
  weak ref with **no** definition resolves to 0 and faults at `_start`.
- **`file(1)` says "dynamically linked" for a `--export-dynamic` static binary.**
  Use `readelf -l <bin> | grep -c INTERP` (must be 0) + `readelf -h` for
  `Type: EXEC` / entry `0x40000000`.
- **`struct SplArray` (`runtime.h:126`) is a decoy** — the real array layout is
  `RtCoreArray { kind; flags; reserved; transient_scope_id; len; cap; data }`.
  And `rt_clear` is **not** an alias for `rt_array_clear` (the latter returns `1`,
  decoding as `RT_VALUE_TAG_HEAP | 0` → NULL heap pointer).
- **`struct __simpleos_FILE` ODR mismatch** — two incompatible definitions (4 B
  in `simpleos_libc.c:362`, 16 B in `simpleos_fs.c:116`). `FILE` is opaque, so
  the compiler cannot diagnose it and `fread`/`fwrite`/`fclose` overwrite up to
  12 bytes past the standard-stream statics. Its bug doc still reads **OPEN**,
  but as of 2026-08-06 the fix appears applied in-tree (single definition hoisted
  into the untracked `src/os/libc/simpleos_file_internal.h`). Guard, and the
  check to confirm before acting:
  `grep -c 'struct __simpleos_FILE {' src/os/libc/*.c src/os/libc/*.h` must total
  exactly 1, in the header.

## Verification Commands

## POSIX and startup boundary

When porting LLVM/Clang-hosted tools or changing the SimpleOS sysroot/runtime,
use `doc/07_guide/app/llm/simpleos_posix_host_interface_index.md` as the
cross-layer index. The existing pure-Simple POSIX compatibility layer starts at
`src/os/posix/mod.spl`; startup policy and argv normalization start at
`src/app/startup/launch_metadata.spl`; host file mapping and SimpleOS VFS
prewarm are separate owners. Do not claim that Clang consumes the POSIX facade
or that SimpleOS has complete file-backed mmap until a dedicated-host provider
and positive tests establish those facts. Keep the C sysroot/crt0/libc path in
this skill separate from the Simple-language POSIX facade.

```sh
LLVM_SRC=/home/ormastes/llvm-project sh src/os/port/llvm/build.shs   # or: … host-tools|cross|compiler-rt
bin/simple run src/os/port/llvm/build.spl
bin/simple run src/os/port/deploy_toolchains.spl -- --status

# guest-runnable contract (the only acceptable proof)
readelf -h <bin>                       # Type: EXEC, Entry: 0x40000000
readelf -l <bin> | grep -c INTERP      # must be 0

# end-to-end host-side sanity through the sysroot
$BIN/clang-20 --target=x86_64-unknown-simpleos --sysroot=$SR -c /tmp/hello.c -o /tmp/hello.o
$BIN/ld.lld -T $SR/share/simpleos/simpleos.ld $SR/lib/crt0.o /tmp/hello.o \
    -L $SR/lib -lsimpleos_c -o /tmp/hello.elf
```

The cross build is **multi-hour** — run it detached with a log, never inside a
foreground timeout.

## Update Rule

When this layer's public contract (the guest-runnable ELF shape), source
ownership, sysroot layout, fork pin, or verification requirements change, update
this skill with the new links and handoff notes. If the fork pin moves, update
both the value here and the `git ls-remote` verification note — a pin that
merely *looks* current has drifted before.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
## Restart12 guest-linker status (2026-08-14)

Any “AC-2 DONE” or current-artifact statement below refers to historical build
output, not restart12 acceptance. The current worktree lacks both
`build/os/clang_static/bin/lld_static` and the cross-tree `bin/ld.lld`.
B-GUEST-LLD requires a genuine validated static x86_64 SimpleOS ELF plus
compiler, dependency, readelf and hash receipts; a host executable is not
equivalent. Use
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md` and
`doc/08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md`.

## Guest-userland linker separation (2026-08-22)

The SimpleOS guest linker now has explicit AArch64 and RV64 userland branches
using the configured installed CRT, Simple runtime, libc, and user linker
script; both return before existing kernel/freestanding routes. Entry objects
are compiled with explicit `/usr/bin/clang --target`, freestanding/no-stdlib
flags, and RV64 `-march=rv64gc -mabi=lp64d`. Preserve this separation: kernel
entry injection (`boot_main`, privileged status setup, `wfi`) is never valid in
a filesystem-launched user ELF. Static machine/ABI inspection does not replace
fresh guest compile/link/run evidence.
