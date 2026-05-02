# Bug: TLS unit kernel link broken on main with 38 unresolved symbols

**Date:** 2026-04-29 (UTC)
**Severity:** blocker — `SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl` cannot reach the live gate; kernel link fails before QEMU boots.
**Discovered by:** `/dev` continuation pass, post-Agent-1/Agent-2 verification (TLS green via interpreter; live gate blocked here).

## Symptom

```
[build][x86_64] phase=native-build FAILED exit=1 elapsed_ms=4541
Build failed: freestanding link has unexpected unresolved symbol(s):
  arm_fs_exec_print_success_marker
  kernel__arch__x86_64__interrupt__spl_x86_dispatch_installed_syscall_abi
  log_info
  os__kernel__log__klog_api__rt_log_target_device_write_bytes
  os__kernel__log__klog_api__rt_log_target_semihost_write_bytes
  os__kernel__log__klog_api__rt_simpleos_log_emit
  os__kernel__log__klog_api__rt_simpleos_log_init
  os__kernel__log__klog_api__rt_simpleos_log_is_enabled
  os__kernel__log__klog_api__rt_simpleos_log_set_device
  os__tls13__key_schedule__Transcript
  rt_arm_array_append_bytes
  rt_arm_array_get_u16_le
  rt_arm_array_get_u32_le
  rt_arm_virtio_blk_configure_queue
  rt_arm_virtio_blk_dma_base
  rt_arm_virtio_blk_mmio_read_u32
  rt_arm_virtio_blk_mmio_read_u64
  rt_arm_virtio_blk_mmio_write_u32
  rt_arm_virtio_blk_prepare_read
  rt_arm_virtio_blk_queue_base
  rt_arm_virtio_blk_read_hello_smf
  rt_arm_virtio_blk_read_prefix
  rt_arm_virtio_blk_read_sector_direct
  rt_arm_virtio_blk_sector_bytes
  rt_arm_virtio_blk_status_u8
  rt_arm_virtio_blk_wait_completion
  rt_arm_virtq_base
  rt_arm_virtq_push_avail
  rt_arm_virtq_reset
  rt_arm_virtq_used_idx
  rt_array_get_byte_raw
  rt_dma_bytes_to_array
  rt_tls13_aes128_gcm_encrypt
  serial_putchar
  serial_puts
  simple_os__arch__x86_64__tls_unit_entry__RecordKey
  simple_os__arch__x86_64__tls_unit_entry__Tls13Secrets
  simple_os__arch__x86_64__tls_unit_entry__TrafficKeys
  simple_os__arch__x86_64__tls_unit_entry__Transcript
```

## Verified facts

- `rt_tls13_aes128_gcm_encrypt` IS defined in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c:10980` — the C extern body exists. So the link error is *not* a missing source file; it's a build pipeline regression where `baremetal_stubs.o` (and likely several other artifacts) are not being included in the kernel link set.
- The class-type symbols (`os__tls13__key_schedule__Transcript`, etc.) are *imported into* `tls_unit_entry.spl` from `os/tls13/*.spl`. They are *not* defined in `tls_unit_entry.spl` — the linker reports the entry file's mangling because that's the link-unit name.
- The `rt_arm_*` symbols and `arm_fs_exec_print_success_marker` should *not* appear in an `x86_64-unknown-none` build at all. Their presence suggests an x86 build is incorrectly pulling in ARM-only HIR/MIR or codegen passes.
- The link-checker is at `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:151`. Its filter chain runs `is_system_symbol` / `is_compiler_rt_builtin_symbol` / `is_linker_provided_symbol`, none of which match these symbols.
- `SIMPLE_ALLOW_FREESTANDING_STUBS=1` would bypass the error and auto-stub all 38 symbols (returning 0 from each weak stub). This would let the build succeed but the kernel would crash at runtime when any of these symbols is invoked.

## Investigation log (2026-04-29 ~00:30 UTC)

Files examined for changes between `kwyqvuqnyoxz` (last known-good 36/0 wave checkpoint) and current `main` (`qpxopxtolmqs`):

| File | Diff content | Verdict |
|------|-------------|---------|
| `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` | fcvt-int defensive guard for browser_engine `_apply_opacity` | Innocent — unrelated to symbol resolution |
| `src/compiler_rust/compiler/src/codegen/instr/basic_ops.rs` | 224-line refactor (clippy/refactor wave) | Likely innocent (ALU instruction lowering, no symbol path) |
| `src/compiler_rust/compiler/src/pipeline/mod.rs` `pipeline/execution.rs` | `CompileError::SemanticWithContext { message, context }` → tuple-style with `Box<ContextualError>` (clippy `result_large_err`) | Innocent — diagnostic plumbing only |
| `src/compiler_rust/compiler/src/lib.rs` | Removed 4-line `#![allow(clippy::result_large_err)]` comment | Innocent |
| `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` | clippy `strip_prefix` rewrite of leading-underscore strip | Innocent (semantically equivalent) |
| `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` | path-lookup reorder for `libsimple_native_all.a` (release vs bootstrap) | Older change (Apr 24), unlikely cause |
| `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:897-905` | Boot-dir `.c` scan with `SIMPLE_BOOT_MINIMAL` gate | Logic looks correct — would compile `baremetal_stubs.c` |

None of the diffs examined above directly explain the 38-symbol unresolved set. The breaking change is therefore most likely either:

1. **Earlier in the pipeline** — e.g., in `lsrz` (parallel `/dev`'s "fix(clippy): manual fixes for top non-cosmetic warning categories in simple-compiler", ~30 files) or one of the older sync commits — and the file we'd need to inspect wasn't on the suspect list.
2. **In a non-Rust file** — e.g., `Cargo.toml` (qp commit shows a 2-line drop), the linker script, or a workspace `Cargo.lock` shift that changed which `simple_native_all` features are compiled.
3. **A combinatorial regression** between two clippy refactors that individually look fine but together drop a feature flag or a module export.

## Categorization

| Category | Symbols | Most-likely root |
|----------|---------|-----------------|
| Class type symbols | `os__tls13__key_schedule__Transcript`, `simple_os__arch__x86_64__tls_unit_entry__{RecordKey, Tls13Secrets, TrafficKeys, Transcript}` (5) | Kernel link is missing the .o files for `src/os/tls13/*.spl` modules — the compile-mode either skipped them or their .o isn't being added to the link set |
| Logging API | `os__kernel__log__klog_api__rt_*` (5) and `log_info` | Same — `src/os/kernel/log/klog_api.spl` .o not being linked |
| Serial console | `serial_putchar`, `serial_puts` | C extern in `baremetal_stubs.c` not being linked |
| TLS extern | `rt_tls13_aes128_gcm_encrypt` | `baremetal_stubs.c` .o is not being included in the link |
| ARM-only leak | `rt_arm_*`, `arm_fs_exec_print_success_marker` | Compiler is emitting references to ARM-only runtime functions in an x86 build — likely a recent change unconditionalized an ARM dispatch table |
| Misc | `rt_array_get_byte_raw`, `rt_dma_bytes_to_array`, `kernel__arch__x86_64__interrupt__spl_x86_dispatch_installed_syscall_abi` | Mixed — runtime helpers and an interrupt dispatcher; investigate per-symbol |

## Workaround

For consumers blocked on TLS testing:
- **Interpreter mode** (no kernel): `bin/simple test test/system/os_tls_client_auth_spec.spl` (3/3 passing — Agent 2's interpreter fix landed and verified).
- **Host TLS spec compile** (no live boot): `bin/simple test test/system/os_tls_spec.spl` (2/0 passing — host-side spec only; live QEMU gated by env).
- **Live gate (broken):** `SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl` — fails at link.

For the broader build to limp along (NOT recommended for shipping):
```
SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl
```
This auto-stubs all 38 missing symbols. Kernel will boot but every TLS call returns 0 / no-op.

## Recommended fix path

Each category below can be tackled by a separate parallel agent (Sonnet quota resets at 04:00 UTC):

1. **Bisect the breaking commit** (research-only Sonnet agent): try linking the TLS unit kernel at `kwyqvuqnyoxz` (last known good). If it links, walk forward via `jj rebase` or worktree-checkout through `uxzm → sxvt → txvo → lsrz → qp` until link breaks. Identify the exact commit + file.
2. **ARM symbol leak** (compiler-Sonnet agent): grep for `rt_arm_` references in x86 codepaths. The leak is most likely a Cranelift target table that recently became non-conditional. Fix: gate ARM intrinsic registration on `target_arch == "aarch64"` or equivalent.
3. **Linker .o aggregation** (build-pipeline-Sonnet agent): add tracing to `linker.rs:897-905` to confirm `baremetal_stubs.o` is actually emitted and added. If it's emitted but not linked, the bug is downstream in the link command construction.
4. **Module-discovery audit** (compiler-Sonnet agent): for `os__tls13__*` and `os__kernel__log__*` classes to be unresolved, the entry-point pipeline must have skipped compiling those `.spl` files. Check the `--source` discovery logic for regressions.

Bound each agent to a 30-minute investigation budget; if not converging, write findings to this doc and stop.

## What this session salvaged

- **Agent 2's interpreter fix is in tree and verified**: `interpreter_extern/ffi_array.rs` adds `rt_array_new_with_cap_fn` (returns `Value::Array`) + `rt_bytes_u8_at_fn`. `os_tls_client_auth_spec.spl` is 3/3.
- **Agent 1's enum Fix #2 code is in tree** (no `tagged_vregs.insert` for `rt_enum_payload` in `lowering_expr_builtin.rs`), but cannot be exercised through the live gate because the kernel won't link.
- **D4/D9/D10 in `tls_unit_entry.spl` still use the `rt_tls13_record_decrypt_compact` C-extern workaround** — a known-good fallback in case Fix #2 turns out to be incomplete. Removing this workaround is gated on the link regression being fixed first.

## Ownership note

This regression appears to be from the parallel `/dev` session's clippy / refactor wave (the `lsrz` and surrounding clippy commits), not from the TLS bug-fix session. The TLS-fix session's deliverables are functionally complete (interpreter green, enum Fix #2 in code). Whoever owns the clippy wave should fix this; the TLS-fix session is not the right owner.
