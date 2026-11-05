# riscv64 in-guest interpreter kernel link blocked on 35 undefined rt_* symbols

- **Status:** OPEN
- **Filed:** 2026-11-05
- **Severity:** high — the in-guest Simple interpreter kernel lane cannot
  link at all; zero in-guest interpreter evidence can be produced until this
  closes.
- **Supersedes-follows:** `riscv64_in_guest_interpreter_blocked_on_baremetal_runtime_2026-08-31.md`
  (the original 43-symbol blocker, measured FIXED at tip on 2026-11-05,
  PR #6947 / lane `work/riscv-inguest-20261105`).

## Measured evidence (nonce b24836bbd2a91e8f, 2026-11-05)

Real kernel build of the interpreter row:

```
PATH=/usr/lib/llvm-18/bin:$PATH \
SIMPLE_BIN=<rust-seed> \
sh scripts/os/build-simpleos-riscv64-interpreter-kernel.shs
```

compiles 614 modules OK, then the link fails with **35 undefined symbols,
zero overlap with the original 43**. Authoritative replay per the prior
record's method: `ld.lld -T linker.ld --gc-sections --error-limit=0
--allow-multiple-definition -e <mangled spl_start> *.o` over the preserved
`.simple/native-objects-*` dir (the replay additionally reports `spl_start`,
the known vacuous artifact of the entry object living outside that dir).

Toolchain note: the default `/home/yoon/dev/llvm/install/bin/clang` has no
riscv64 target; llvm-18 on PATH does.

## The 35 symbols, by bucket

| bucket | n | symbols |
|---|---|---|
| pure computation (a sibling freestanding reference exists for each) | 8 | `rt_text_eq_any`, `rt_array_data_ptr_text`, `rt_utf8_validate`, `rt_ptr_read_i64`, `rt_atomic_int_load`, `rt_atomic_int_compare_exchange`, `rt_value_as_bool`, `rt_value_truthy` |
| no VFS/process/threads in S-mode (honest resolution = fail closed) | 14 | `rt_io_file_{open,open_read,open_write,open_append,read,seek,close_value}`, `rt_process_run{,_bounded,_tuple,_bounded_tuple}`, `rt_thread_sleep`, `rt_signal_check`, `rt_atexit_check` |
| identity/capability queries | 3 | `rt_is_interpreter_runtime`, `rt_is_jit_runtime`, `spl_thread_cpu_count` |
| adaptive-collection capture-note instrumentation | 6 | `spl_collection_capture_note_{size,lookup,materialization,hash_probe,filter,loop}` |
| session/transient heap (no freestanding sibling anywhere in the tree) | 4 | `rt_session_alloc_{begin,end}`, `rt_transient_heap_adopt`, `rt_transient_array_scope_state_v1` |

Referencing checked-in sources: `bootstrap_mir_store.spl` /
`bootstrap_hir_store.spl` (session heap, from `f1e2edad6c7`
"session-owned bootstrap MIR registries"), `interpreter_run_abi.spl`,
`text_extern_abi.spl`, parser modules (`rt_value_truthy`), and
`src/lib/nogc_sync_mut/sffi/collection_capture.spl`.

Note on `rt_text_eq_any`: PR #6957 ported it to the *embedded simple_os*
runtime (`examples/09_embedded/simple_os/arch/common/riscv_common.h`); this
kernel lane links the `src/os/kernel/arch/riscv64` runtime, a different
translation unit set, so the symbol is still undefined here.

## Required resolution

1. Port the pure-computation bucket to the kernel freestanding runtime
   (`src/os/kernel/arch/riscv64/boot/`), mirroring an existing sibling
   freestanding lane's semantics (see PR #6957's nil-aware,
   content-comparing `rt_text_eq_any` as the quality bar).
2. Session/transient heap: design first. No freestanding sibling exists;
   a drive-by port risks the silent-lie class (heap state silently wrong
   in-guest). The port needs an in-guest OpenSBI boot to verify.
3. io/process/thread and capability-query buckets: if the kernel truly
   cannot provide them in S-mode, the referencing compiler modules must
   fail closed at kernel-build time (explicit `@cfg`-style exclusion or an
   admitted-stub that traps with a named message), not leave the link
   undefined.
4. Capture-note instrumentation: provide no-op-with-note definitions or
   exclude the referencing module from the kernel closure.

## Acceptance

`sh scripts/os/build-simpleos-riscv64-interpreter-kernel.shs` links
successfully, and the resulting kernel boots under OpenSBI in QEMU far
enough to print its first interpreter marker (the lane's existing
run-riscv64 probe harness may be reused).
