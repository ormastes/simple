# Stage 2 binary: C-runtime string literals resolve to address -1 (SEGV in rt_secure_temp_dir_make)

- Status: OPEN
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu, seed native link with mold
- Blocks: Stage 2 compiler sanity (`frontend_status=139`, `p2_add-build
  failed (raw rc=139)`) on `origin/release_phase3` >= 821bf1e553c (runs r9,
  r10), so no Stage 2 is admitted.

## Observation

Diagnostic relink of the r10 Stage 2 from its own native cache
(`compiled=2 reused=1383`, 31.6 s, sha256 `907ddf57...0fd4`), then the
sanity probe under gdb (`SIMPLE_BOOTSTRAP=0 ... native-build --entry
src/compiler/bootstrap_admission/p2_add.spl`):

```text
SIGSEGV strchrnul <- __printf_buffer(format=0xffffffffffffffff)
  <- snprintf <- rt_secure_temp_dir_make
  <- lib.scv.compile_snapshot.scv_compile_snapshot_acquire_v1
  <- app.compiler_entrypoint.source_authority.compiler_source_authority_acquire_v1
  <- app.cli.native_build_main.run_native_build_worker
```

`rt_secure_temp_dir_make+100`: `adrp x2, 0xfffffffffffff000; add x2, x2,
#0xfff` -- the `"%s"` literal of `runtime_native.c:15509` was relocated to
-1 (the tombstone for a reference into a discarded section). The whole
binary has 16 such references, all in `runtime_native.c` functions:
`rt_sdr_mount_location_v1` (10), `rt_sdr_create_private_v1` (3),
`rt_sdr_root_open_mode_v1`, `rt_secure_temp_dir_core`,
`rt_secure_temp_dir_make` (1 each). The r8 Stage 2 (base 630f773bdc7,
sha256 `552150e7...15d8`) already has 14 of them but never executed those
functions; cycle-170 (c3a8618fd9b, 669c50c11be) routed SCV snapshot staging
through `rt_secure_temp_dir_make`, so every Stage 2 sanity build now
dereferences one.

## Not yet established

Which link input supplies these functions (the cycle-170 "bootstrap mutex
core-C capsule" is the likely one) and why its string-literal section is
discarded while its text is kept.
