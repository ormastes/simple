# Stage 2 link: rt_array_bytes_basis_ptr/len missing from the Rust runtime

- Status: OPEN
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Bug DB: reconciliation pending (`bug-add` on the seed overflows the
  stack in `rename_path`; see
  `stage2_test_runner_imported_enum_owner_text_corrupt_2026_10_19.md`).
- Blocks: Stage 2 of `--full-bootstrap --stop-after-stage2` on
  `origin/release_phase3` at or after `35017232d02`.

## Observation

`35017232d02 fix(sffi): pass file writer buffer pointer and length` makes
`io_file_write` / `io_file_write_all` (`src/lib/nogc_sync_mut/sffi/fs.spl:317-370`)
call `rt_array_bytes_basis_len` and `rt_array_bytes_basis_ptr`. Those exist
only in the C runtime (`src/runtime/runtime_native.c:8628-8641`,
`runtime_packed_span.c`). Stage 2 is linked by the Rust seed against
`libsimple_runtime.a` (Rust), which defines neither, so the link fails:

```text
mold: error: undefined symbol: rt_array_bytes_basis_ptr
>>> referenced by lib__nogc_sync_mut__sffi__fs (mod_1292.o: io_file_write_all)
mold: error: undefined symbol: rt_array_bytes_basis_len
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
VERDICT — ABORTED: stage=stage2 exit=1
```

Run r7 (base `84e13d92794` + this lane's fixes), log
`.simple/storage/build/bootstrap-r7/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`.

## Why no workaround here

The Rust runtime stores array elements as tagged `RuntimeValue` words
(`collections.rs:1180 rt_array_data_ptr`), so there is no byte-packed basis
to return; a twin that reports "not a basis" would make every file write
return -1. Reverting `fs.spl` would reintroduce the C-runtime ABI bug that
commit fixed. The owner must give the Rust runtime a real byte-span twin (or
route the seed-built Stage 2 through a path both runtimes provide).
