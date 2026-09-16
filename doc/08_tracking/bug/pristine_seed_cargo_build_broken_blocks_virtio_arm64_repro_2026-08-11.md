# Pristine seed `cargo build --release` is broken at origin/main HEAD — blocks virtio arm64 defect repro

- Date: 2026-08-11
- SHA tested: `7f967a8ad7029ec5f3e93d239a22cd544a6b82b9` (origin/main, fresh `git fetch` + `git worktree add --detach`)
- Cross-ref: doc/08_tracking/bug/arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md

## What was attempted

Per task: reproduce the reported virtio_common.spl (7 functions) / virtio_gpu.spl (51
functions) codegen defects blocking the arm64 kernel build. Files located at:
- `src/os/drivers/virtio/virtio_common.spl`
- `src/os/drivers/virtio/virtio_gpu.spl`

To reproduce cleanly, built the seed compiler from a fresh pristine worktree
(`/mnt/data/build-virtio`, detached at origin/main) with
`CARGO_TARGET_DIR=/mnt/data/cargo-target-virtio`:

```
cd src/compiler_rust && cargo build --release --bin simple
```

## Actual result: build fails before reaching the driver/compiler crates

`simple-runtime` (lib) fails with 3 errors, unrelated to virtio/SimpleOS:

```
error[E0432]: unresolved imports `value::rt_array_each`, `value::rt_array_map`,
  `value::rt_array_reduce`, `value::rt_map`, `value::rt_value_unbox_int`

error[E0432]: unresolved imports `value::rt_tls_client_connect_address_with_sni_timeout`,
  `value::rt_tls_client_read_timeout`, `value::rt_tls_client_write_timeout`

error[E0599]: no variant or associated item named `WideInt` found for enum
  `HeapObjectType` in the current scope
  --> runtime/src/value/sffi/io_print.rs:478:25
   |
478 |         HeapObjectType::WideInt => v.as_int().to_string(),
   ::: runtime/src/value/heap.rs:8:1
```

`HeapObjectType` (defined `src/compiler_rust/runtime/src/value/heap.rs:8`) has no
`WideInt` variant, but `runtime/src/value/sffi/io_print.rs:478` matches on it — the
two files are out of sync at HEAD. The two `E0432` unresolved-import errors indicate
additional runtime symbols (`rt_array_each`, `rt_array_map`, `rt_array_reduce`,
`rt_map`, `rt_value_unbox_int`, `rt_tls_client_connect_address_with_sni_timeout`,
`rt_tls_client_read_timeout`, `rt_tls_client_write_timeout`) referenced by name but
not exported/defined where expected — consistent with an incomplete or
interrupted refactor of `src/compiler_rust/runtime/src/value/`.

`cargo build` output tail: `error: could not compile \`simple-runtime\` (lib) due
to 3 previous errors`.

## Impact

This is upstream of and blocks everything the task asked for: no fresh seed
binary can be produced from a pristine `origin/main` checkout, so the
virtio_common.spl / virtio_gpu.spl compilability-gate defects could not be
reproduced, enumerated, classified, or fixed in this session. The existing
deployed `bin/simple` in the main working copy was NOT used to substitute,
per the "never touch bin/simple / never build from shared WCs" constraint —
using it would not have been a pristine-build reproduction and its provenance
relative to this exact SHA is unverified.

## Next step (not done here)

Someone with access to the runtime refactor context needs to either finish
wiring `rt_array_each`/`rt_array_map`/`rt_array_reduce`/`rt_map`/
`rt_value_unbox_int`/the three `rt_tls_client_*` symbols in
`src/compiler_rust/runtime/src/value/mod.rs` (or wherever they now live), and
either add a `WideInt` variant to `HeapObjectType` or fix
`runtime/src/value/sffi/io_print.rs:478` to match the current enum — then
re-attempt this task's steps 1-5 from a fresh pristine worktree.

No files under `src/os/drivers/virtio/` or `src/compiler_rust/compilability.rs`
were modified in this session — the blocker is entirely upstream in the Rust
runtime crate. Worktree `/mnt/data/build-virtio` was removed after this
investigation; nothing was pushed (nothing to push — no fix produced).
