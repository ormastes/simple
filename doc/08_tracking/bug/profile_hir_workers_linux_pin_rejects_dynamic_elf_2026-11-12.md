# Profile HIR workers on Linux: the owned executable pin rejected every dynamically linked compiler

- Status: fix-implemented (verification pending a runtime-authority + Stage 2 rebuild)
- Severity: P1. On Linux, every HIR shard pool (the coordinator and the Stage 3 capsule) still ran serially after #8639 and #8663.
- Found: 2026-11-12, by the Phase 3 lane on aarch64 Linux; recorded 2026-11-13
- Component: `src/runtime/runtime_process_owned.c` (Linux pin since 2026-11-13, beside the Darwin pin; was `runtime_process.c`, which the Rust runtime crate never compiles) and `src/compiler_rust/runtime/src/value/sffi/env_process.rs` (Rust stubs)
- Previous gate: `profile_hir_workers_darwin_only_linux_lacks_process_group_retire_2026-11-12.md`

## Observation
With a Stage 2 built against #8663, the 3-file pre-flight fails at the next gate:

```
[hir-shard] owner=0/2@0 reason: owned executable pin was rejected
```

`worker_hir_owner_start_v1` (`src/app/cli/worker_hir_owner_v1.spl:208`) calls
`OwnedExecutablePin.pin(binary)` → `rt_process_pin_executable_owned_value` →
`rt_process_pin_executable`. That pin copies the image into a sealed memfd and
admitted only a static ELF: `rt_hal_static_elf_fd` refused any `PT_INTERP` or
`PT_DYNAMIC` program header (since 98215e0f708, "MC/DC RT HAL hardening",
2026-08-25; its comment deferred the dynamic case to "a separate pinned
manifest").

The Stage 2 and Stage 3 compilers are dynamically linked. Measured on the run-16
Stage 2 (`stage2/aarch64-unknown-linux-gnu/simple`, 45,881,576 bytes):
`ET_EXEC`, `PT_INTERP /lib/ld-linux-aarch64.so.1`, `DT_NEEDED` libm.so.6,
libstdc++.so.6, libgcc_s.so.1, libc.so.6, no `DT_RUNPATH`/`DT_RPATH`.

The MIR shard pool of the same build is not affected because it never pins:
`native_build_main.spl:1213` spawns MIR shards with `process_spawn_async(simple_bin, …)`,
a plain path spawn with no image verification at all. Only the HIR lane goes
through the owned, pinned launch.

## Decision: admit the system-loader dynamic class (Darwin parity), fail closed, visibly

Three options were read before choosing.

1. **Link the bootstrap compilers statically.** Blocked by more than a link flag:
   `DT_NEEDED` carries `libstdc++` and `libgcc_s` (GCC artifacts; a static build
   means a libc++/compiler-rt/libunwind switch under the clang+lld rule), the
   runtime calls `dlopen` (`runtime_dynload.c`, `runtime_backend_plugin.c`,
   `runtime_glfw.c`, `runtime_renderdoc.c`, `runtime_alloc_observer.c`,
   `counterpart_*`), glibc static has the NSS caveat, and the seed linker
   (`linker.rs`) passes `-static` only in the freestanding-runtime lane. It is a
   toolchain project, not a gate fix. Left as the strict lane.
2. **Admit dynamic images as-is.** Too weak as stated: an image with
   `DT_RUNPATH`/`DT_RPATH`, an absolute-path `DT_NEEDED`, or a user-owned
   `PT_INTERP` would load code the pin never saw, from paths the image chooses.
3. **A pinned manifest of loader + `DT_NEEDED` closure, verified at launch.**
   The kernel resolves `PT_INTERP` by path at exec and the loader resolves each
   soname by its own search, so a hash-and-verify manifest does not bind what
   actually loads; binding it means exec through a pinned ld.so with a pinned
   private library directory (a mini-sysroot). Recorded as the follow-up the
   original comment anticipated.
   TODO (follow-up): also refuse `GLIBC_TUNABLES` in `pov4_environment_steers_loader`.
   It tunes loader behaviour without adding a search path and the HIR worker
   allowlist already refuses it by name, so this is defense in depth, not a gap.

**Chosen: a bounded form of (2) that is exactly what the Darwin pin already
gives.** `owned_darwin_pin_is_macho` admits any Mach-O main image; dyld and
every dylib load unpinned; the pin's guarantee is "the main image bytes are the
admitted producer's bytes" (`pov4_darwin_snapshot_matches` + main-image vnode
identity). The Linux pin now gives the same guarantee for a dynamic image, and
refuses every way the image or the environment could steer library resolution
off the system loader paths.

Admitted classes (`hal_pinnable_elf_fd`, replacing `rt_hal_static_elf_fd` at
its three call sites: pin source, sealed memfd, acquire-at-launch):

- **static** — `ET_EXEC`, no `PT_INTERP`, no `PT_DYNAMIC`. Unchanged. ELFCLASS32 and ELFCLASS64.
- **system-loader dynamic** (new) — ELFCLASS64, `ET_EXEC` or `ET_DYN`, exactly
  one `PT_INTERP` and one `PT_DYNAMIC`, and all of:
  - `PT_INTERP` is NUL-terminated, absolute, and `stat()`s to a regular file
    owned by uid 0 that is not group- or other-writable (measured on this host:
    `/lib/ld-linux-aarch64.so.1` → root 755 regular file);
  - no `DT_RPATH`, no `DT_RUNPATH` (also rules out `$ORIGIN`, which under a
    memfd exec would resolve to `/`);
  - every `DT_NEEDED` is a bare soname (no `/`), read from `DT_STRTAB` mapped
    through the `PT_LOAD` segments; bounded at 64 loads, 4096 dynamic entries,
    256 sonames, 1 MiB string table (Stage 2's `.dynstr` is 0x26c0 bytes).
  - `ET_DYN` is admitted because the one-binary link config the Stage 2
    `native-build` reaches defaults to `pie: true`
    (`driver_aot_native_output.spl:1923/1950/3321/3360`; the `pie: false`
    configs in `driver_bootstrap.spl:552/619` are reached only from
    `p3_groups/group_6.spl`, the full CLI, not from `native_build_main`). A
    Stage 3 built by Stage 2 is therefore a PIE unless that default is
    overridden, and without `ET_DYN` the phase3→phase3 self-compile would hit
    this gate again. Stated plainly: `ET_DYN` + `PT_INTERP` admits any
    loader-launched image of the shape above (an executable `libc.so.6` with
    the x bit passes the shape rules). What ties the pin to the compiler is
    the owner's `producer_digest` comparison, not the pin.
- **refused** — `PT_DYNAMIC` without `PT_INTERP` (static PIE and shared objects,
  unchanged), `PT_INTERP` without `PT_DYNAMIC`, ELFCLASS32 dynamic images, and
  anything failing the rules above.

Fail closed at the launch boundary too, on both paths that `fexecve` a pin
(`runtime_process_owned.c`): the Linux branch of `pov4_start_exact` refuses a
request environment containing any `LD_*` variable
(`pov4_environment_steers_loader`) before a slot or child exists, returning
`POV4_START_NO_CHILD` with `EPERM`; `owned_process_start` applies the same
predicate pre-fork to a v4 config's environment (its v3 pinned launch, the
only live caller with a pin, execs a fixed `LANG/LC_ALL/TZ/PATH` environment
with no `LD_*`). The HIR profile's exact allow-list
(`worker_hir_environment_key_admitted_v1`) never admits an `LD_*` key, so this
is the C-side guarantee of the class, not a behaviour change for the profile.

Visible: each dynamic admission prints one line on stderr from the pin:
`[rt-pin] dynamic ELF admitted (system-loader class, Darwin parity): main image sealed and digest-bound; loader <interp> and its DT_NEEDED libraries are not pinned: <path>`.

What is still unpinned, stated rather than implied: the loader file itself and
the shared libraries it resolves. Their trust is root ownership of system
paths, the same trust the Darwin pin places in dyld and the shared cache. No
new exported `rt_*` symbol.

## Evidence (T0, cheapest tier)
- `src/runtime/test/runtime_process_pin_dynamic_elf_linux_selfcheck.c` — includes
  `runtime_process.c`; compiled WITHOUT `-static` so the test binary is the
  dynamic image (PIE, `PT_INTERP /lib/ld-linux-aarch64.so.1`, `DT_NEEDED libc.so.6`).
  It pins its own resolved path (the pin opens `O_NOFOLLOW`, so `/proc/self/exe`
  itself is not pinnable — same as the HIR owner passing the canonical path),
  checks the sealed memfd, checks the owned digest equals the SHA-256 of the
  file bytes (the `producer_digest` the owner compares against), `fexecve`s the
  acquired memfd and reads back the child's `/proc/self/exe`
  (`/memfd:simple-rthal (deleted)`), then refuses byte-patched copies:
  `DT_NEEDED`→`DT_RUNPATH`, `DT_NEEDED`→`DT_RPATH`, `PT_INTERP`→`PT_NULL`
  (static-PIE/shared-object shape), `PT_INTERP` → a user-owned file in
  `/dev/shm`, a missing path, a relative path; plus the unchanged refusals of a
  non-executable file and a directory.
  - Red on origin/release/1.0.0 `d64d7ea8b13` (base `runtime_process.c`
    mirrored into a scratch tree): `FAIL (2 of 20)` — both admission checks.
  - Green with this change: `PASS (28 checks)`, with the two `[rt-pin]` lines.
- `src/runtime/test/runtime_process_owned_loader_env_linux_selfcheck.c` — includes
  `runtime_process_owned.c`; `PASS (7 checks)` (clean, empty and NULL
  environments admitted; `LD_PRELOAD`, `LD_LIBRARY_PATH`, `LD_AUDIT`, and an
  empty-valued `LD_*` refused). Red on base by absence (the predicate did not exist).
- `check-c-runtime-compiles-push.shs`: `FAIL — 20 file(s) failed` — the same 20
  pre-existing vector-provider/Darwin/Windows files as on base; both runtime
  files and both selfchecks compile clean (343 compiled clean).
- `check-runtime-source-list-parity.shs` is pre-existing red (208 offenders, all
  `src/runtime/test/*.c` including the previous gate's selfcheck); the two new
  selfchecks join that advisory class, as the previous one did.

## Run 18 (b26b93aa54d): the C fix was never linked into Stage 2

Run 18 admitted Stage 2, then both Phase 2 tool rows failed the same way:
`[hir-shard] owner=0/2@0 status=CRASH ... reason: owned executable pin was rejected`,
then `error: HIR aggregate failure`. The fix above had landed, but the binary
did not contain it: `grep -a simple-rthal` and `grep -a "dynamic ELF admitted"`
both found 0 matches in `stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`.

Linkage, confirmed with nm:
- Stage 2 links `libsimple_native_all.a`, which is the Rust runtime crate plus
  the C objects that `compiler_rust/runtime/build.rs` compiles. That list has
  `runtime_process_owned.c` on every OS. It has never had `runtime_process.c`.
- So on Linux the only definitions were the `#[cfg(not(target_os = "macos"))]`
  fail-closed stubs in `compiler_rust/runtime/src/value/sffi/env_process.rs`.
  nm on run 18's `stage2-runtime-authority/libsimple_native_all.a` shows
  `rt_process_pin_executable_owned_value`, `_acquire_`, `_sha256_value` and
  `_close_..._owned` as `T` in a `simple_runtime ... rcgu.o`. The archive
  contains no `simple-rthal` string.
- macOS already had the right arrangement: its pin lives in
  `runtime_process_owned.c` and the Rust stubs are cfg'd out there.

Fix (same layout as macOS):
- `runtime_process_owned.c` now holds the Linux pin, in a
  `#if defined(__linux__) && !defined(RT_OWNED_EXTERNAL_PIN)` block next to
  the Darwin pin. Moved in: the ELF admission helpers, the owned handle table,
  raw `rt_process_pin_executable`, the owned pin and its `_value` form,
  acquire, the digest, and both owned closes.
- `runtime_process.c` keeps only the non-Linux fail-closed definitions, plus
  the raw-fd `rt_process_close_pinned_executable` and
  `rt_process_spawn_pinned_piped`.
- No new `rt_*` names were added, and each lane still defines each symbol once.
- The six Rust stubs are now `cfg(not(any(macos, linux)))`. They are kept for
  the other OSes, and the text-based dual ratchet still sees them.
- Second trap, closed: the crate compiles `runtime_process_owned.c` without
  `_GNU_SOURCE`, and glibc gates `F_ADD_SEALS`/`F_SEAL_*` behind `__USE_GNU`.
  The moved `#if !defined(F_ADD_SEALS) ... return -1` branch would therefore
  have compiled the pin to a silent refusal. The block now defines the UAPI
  seal constants when they are missing, and `#error`s without
  `SYS_memfd_create`.
- Third defect, found by the new crate-lane test: the pin's private SHA-256
  copy (`pin_sha_block`) had 63 round constants (`0xc76c51a3` was missing), so
  `rt_process_pinned_executable_sha256_value` was not SHA-256. For
  `/usr/bin/true` it gave `b3e1b10f...` where `sha256sum` gives `a82c1b5f...`.
  The old selfcheck hashed its reference with that same function, so it
  compared the wrong value with itself. The digest now streams through the
  shared `owned_sha256_block`. The selfcheck adds the FIPS 180-2 "abc" vector
  and hashes its reference with the one-shot `owned_sha256`.
- Harnesses that stub the pin and include `runtime_process_owned.c` now define
  `RT_OWNED_EXTERNAL_PIN`, as the Darwin harnesses already did.

Red to green (cheapest tier, `cargo build -p simple-runtime --features runtime-symbol-table`, LTO off):
- nm `libsimple_runtime.a`, before: the six pin symbols were `T` in a Rust
  `rcgu.o` and the archive held 0 `simple-rthal` strings. After: all seven are
  `T` in `runtime_process_owned.o`, none come from an rcgu object, and the
  archive holds 1 `simple-rthal` string.
- `cargo test -p simple-runtime --lib linux_owned_pin`
  (`env_process.rs::linux_owned_pin_tests`) pins `/usr/bin/true` through the
  crate ABI. It checks the handle, that the acquired fd is the `simple-rthal`
  memfd, that the digest equals `sha256sum`, and close. Before: FAIL
  (`returned -1`). After the move, without the SHA fix: FAIL (digest
  mismatch). After both: PASS.
- `runtime_process_pin_dynamic_elf_linux_selfcheck.c`: PASS (29 checks).

## Native confirmation: PENDING, needs a rebuild
`runtime_process.c` and `runtime_process_owned.c` changed, so the deployed
runtime authority and the Stage 2 built against it do not carry this fix. Steps:
1. Phase 1 runtime authority: `cargo -p simple-native-all -p spl_hosted_runtime`
   plus `-p simple-runtime --features runtime-symbol-table`, LTO off. Before
   Stage 2, gate on the archive: `nm` must show `rt_process_pin_executable_owned_value`
   defined by `runtime_process_owned.o` (no `rcgu.o`), and `grep -a -c simple-rthal`
   on `libsimple_native_all.a` must be >= 1. Run 18 skipped this check and shipped the stubs.
2. Stage 2 (`--full-bootstrap --stop-after-stage2 --backend=cranelift`, lane
   `SIMPLE_CACHE_SCOPE` pinned), then the 3-file pre-flight: expect
   `completed_workers=2` and two `[rt-pin] dynamic ELF admitted` lines in the
   coordinator's stderr, then the Stage 3-shape probe.

## Gates visible past this one (read-through of `worker_hir_owner_start_v1`)
- `executable.digest()` must equal `profile.closure.binding.producer_digest` —
  `file_hash_sha256(producer)` over the same path (`native_build_parse_closure_owner.spl:127`);
  the memfd is a byte-exact copy, proven equal by the selfcheck.
- `OwnedCwdPinV4.pin(source_root)` — has a Linux body (`runtime_process_owned_cwd_private.h`).
- The worker's `/proc/self/exe` is the memfd. `check_self_contained` returns
  false (no file at that path). `_current_exe_path_for_guard` returns the memfd
  string, so `is_same_binary_path(resolved_bin, current_exe)` is false inside a
  pinned worker: the self-delegation guard then relies on the
  `SIMPLE_COMPILE_DELEGATED` marker alone. Not a refusal; a reduced guard,
  worth a follow-up if a worker is ever allowed to delegate.
- 64 MiB cap on pin/acquire/digest: Stage 2 is 45.9 MB; a Phase 4 full CLI may
  exceed it and would be refused with the same `pin was rejected` reason.
- Stdlib root discovery is not exe-relative: no reader of `SIMPLE_LIB` exists
  outside the profile allow-list, and the module resolver has no exe-dir use
  (`/proc/self/exe` readers are `cli_helpers.spl`, `driver_public_shared.spl`,
  `resource_scope.spl`, `runtime_simd_utf8.c`, `runtime_process.c`). The MIR
  shards already run the same binary with the same cwd. Not a gate.
- The `[rt-pin]` line is on the coordinator's stderr, once per worker start.
  If a matrix row or receipt asserts an empty stderr, that is the first thing
  the native run will show.
- Pre-existing, not changed here: `runtime_process_owned_pinned_integration_selfcheck.c`
  pins `"/proc/self/exe"` while the pin opens `O_NOFOLLOW`, so that test cannot
  pass as written (the selfcheck here pins the resolved path instead).
- Specs that pin a path were read for rejection assertions: none asserts that
  a dynamic image is refused. `parser_external_inspection_process_v1_spec.spl`
  pins `/usr/bin/false` and unwraps — it could only pass on Darwin before and
  now passes on Linux too.

## Verification note (2026-11-13 ~03:55, s3j/J lane)

The J lane pinned 7d2a96d5a31 (03:11) -- it had the dynamic-ELF admission fix
bef1d69a6c2 but NOT 34886d22cc2 ("link the real C executable pin into the Rust
runtime crate on Linux", landed 03:26 via #8705). Its stage2 compiler tests
reproduced exactly this gate: compiler_cli_build FAIL 465s with
`[hir-shard] owner=0/2@0 reason: owned executable pin was rejected` (also
test_runner_build FAIL). Confirms the diagnosis end-to-end: the Rust runtime
crate linked the stub pin; without the crate-link fix the admission fix cannot
execute. J2 lane re-pinned at 3a0aac3773a (includes 34886d22cc2) to verify the
fixed pin under the full test matrix.
