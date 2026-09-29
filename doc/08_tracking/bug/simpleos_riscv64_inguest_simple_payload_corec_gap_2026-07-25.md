# Bug: riscv64 in-guest `simple` toolchain payload blocked on simple-core runtime gap

- **Filed:** 2026-07-25
- **Area:** SimpleOS / cross-target userland payload / `simple-core` runtime bundle
- **Severity:** medium (blocks in-guest self-host lane; does NOT block fs-exec ls+launch)
- **Status:** open

## 2026-09-22 implementation update

The original seven-symbol census was stale. `rt_get_args`,
`rt_string_new_literal`, and `sigpending` had already gained target owners. The
remaining four pure-Simple owners are now implemented in this lane:

- `core_env.spl`: `rt_env_get_i64`
- `core_array.spl`: `rt_bytes_to_text`
- `core_string.spl`: `rt_text_cmp_any` (and the duplicate, weaker
  `rt_native_cmp` definition was removed)
- `core_values.spl`: `rt_value_as_float`, guarded by an open-addressed owner
  registry before any heap-tagged pointer dereference

`simpleos_math.c` now supplies the freestanding, bit-preserving
`spl_bits_to_f64` primitive required for exact finite, negative-zero, infinity,
and NaN reconstruction. The RV64 archive and payload scripts pass
`--threads 12` by default, configurable through
`SIMPLE_NATIVE_BUILD_THREADS`.

The executable probe also passes as a lightweight hosted semantic oracle:

```text
simple run test/02_integration/compiler/simple_core_payload_runtime_probe.spl --mode=interpreter
SIMPLE_CORE_PAYLOAD_RUNTIME_OK
elapsed=0.05s max_rss=23,412 KiB
```

This does not claim target-provider admission; it checks the externally visible
conversion, ordering, invalid-handle, and registry-growth behavior without a
cross-compile or guest boot.

Focused RV64 Cranelift archive compilation succeeded for all four changed
parts. The complete simple-core archive built 20/20 parts in 4.91 seconds with
196,164 KiB maximum RSS, and `llvm-nm` found each new strong owner. The final
sysroot/payload link remains unverified: the third and final verification cycle
stopped while cross-compiling the pre-existing `runtime_native.c` supplement
because the SimpleOS libc surface lacks `MADV_*`, `madvise`, and `glob.h`.
Under the repository three-cycle rule this lane did not retry. The guest probe
`test/02_integration/compiler/simple_core_payload_runtime_probe.spl` remains the
required executable closure evidence; keep this bug OPEN until the sysroot
blocker is fixed and that probe plus the real payload run in an RV64 guest.

## TODO: deferred RV64 admission

When the RV64 sysroot/phase environment is ready, build the payload with
`SIMPLE_NATIVE_BUILD_THREADS=12`, boot it in the canonical SimpleOS RV64 QEMU
guest, and run `simple_core_payload_runtime_probe.spl` through the emitted
`simple-core` provider. Record the payload hash, QEMU command, exit status,
elapsed build/probe time, and maximum RSS. Compare archive construction only
against the last identical archive baseline (4.91 seconds, 196,164 KiB maximum
RSS); establish a separate payload-build baseline using the same sources,
compiler, cache state, and thread count. For runtime memory, execute at least
1,000 begin/allocate/pause/promote/end scope cycles in one guest process and
record steady-state RSS before and after the loop. Investigate rather than
admit any unexplained slowdown above 10%, build-RSS growth above 10%, or
positive steady-state RSS trend across completed unpromoted scopes. Remove
this TODO and close the bug only after the guest prints
`SIMPLE_CORE_PAYLOAD_RUNTIME_OK`.

## Summary
Cross-building the in-guest Simple toolchain payload
`bin/release/riscv64-unknown-simpleos/simple`
(`scripts/os/simpleos-native-build-riscv64.shs`, entry
`src/app/simpleos_tool/main.spl`, `--runtime-bundle simple-core`) fails at the
final `ld.lld` link with a small, fixed set of **undefined C-runtime symbols**
that the pure-Simple `simple-core` bundle does not provide:

```
rt_get_args
rt_env_get_i64
rt_bytes_to_text
rt_text_cmp_any
rt_value_as_float
rt_string_new_literal
sigpending            (freestanding libc gap)
```

These 6 `rt_*` functions are defined **only** in the host C runtime
(`src/runtime/runtime_native.c` / `runtime.c`), not in
`src/runtime/simple_core/*.spl`. The seed's codegen for the full compiler
closure emits calls to them, so any `simpleos` userland payload built from the
compiler closure needs them.

This is **arch-independent**: `bin/release/x86_64-unknown-simpleos/simple` and
`bin/release/aarch64-unknown-simpleos/simple` do not currently exist for the
same reason (the generic `scripts/os/simpleos-native-build.shs` uses the same
`--runtime-bundle simple-core`).

The C wrappers are thin (see `runtime_native.c`): they delegate to
`rt_string_new`, `rt_core_as_array`, `rt_core_as_float`, `rt_cli_get_args`,
`rt_interp_cstr`, `rt_core_text_arg_to_cstr`, plus libc `getenv/strtoll/strcmp`.
Of those delegate helpers, `rt_string_new` and `rt_cli_get_args` ARE in
simple-core, but `rt_core_as_array`, `rt_core_as_float`, `rt_interp_cstr`,
`rt_core_text_arg_to_cstr` are NOT — so a pure C shim linked into
`libsimpleos_all.a` cannot fully delegate without also exporting those helpers.

## Fix options (pick one)
1. Add pure-Simple implementations of the 6 `rt_*` to the appropriate
   `src/runtime/simple_core/*.spl` parts (preferred — "fix .spl not C"), plus a
   freestanding `sigpending` libc stub in `src/os/libc`.
2. Export the missing internal helpers (`rt_core_as_array`, `rt_core_as_float`,
   `rt_interp_cstr`, `rt_core_text_arg_to_cstr`) from simple-core and add a small
   freestanding C `rt_extras` compiled into `libsimpleos_all.a` by the sysroot
   scripts, delegating to them (mirrors runtime_native.c one-liners).

## Build-order note (already correct after this session)
`scripts/os/simpleos-sysroot-riscv64.shs` bundles the simple-core objects into
the libgcc-slot archive `libsimpleos_all.a` ONLY if
`build/os/simple-core-simpleos-riscv64/parts/objects` already exists. The
documented prereq order (sysroot, then core-archive) is therefore wrong — run
`simpleos-core-archive.shs` FIRST, then `simpleos-sysroot-riscv64.shs`, else the
libgcc-slot archive is libc-only and every `rt_enum_*`/`rt_string_*` link
undefined. Consider swapping the prereq order in the script header / auto-running
the core archive from the sysroot script.

## Impact on fs-exec (why this is NOT a boot blocker)
The `qemu` `riscv64-virtio-fat32-smf` fs-exec lane (spec
`test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl`) does **not** need
this payload. Its acceptance markers (`FS_MOUNT_OK`, `SMF_DISCOVERY_OK`,
`ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, ...) are produced by the kernel's SMF probes
(`rt_riscv_smf_cli_load` in `.../arch/riscv64/boot/baremetal_stubs.c` loading
`/sys/apps/hello_world.smf`), not by the in-guest `/usr/bin/simple`. The rv32
fs-exec lane has no payload gate at all. `scripts/os/make_os_disk.shs` was
updated this session to make the riscv64 payload OPTIONAL (stage-if-present),
restoring rv64/rv32 parity; the full in-guest self-host payload remains tracked
here.
