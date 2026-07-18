# FS-REQ-001: fsync / dir-fsync runtime primitives

- **Date:** 2026-04-18
- **svllm phase:** A2
- **Triggering code:** `src/lib/gc_async_mut/svllm/nvfs_client/std_fs.spl:sync`,
  `src/app/svllm_pack/main.spl:_do_pack`
- **Need (API or semantic):** expose `rt_file_fsync(handle_or_path) -> int`
  and `rt_dir_fsync(path) -> int` externs so the `StdFsNvfsClient` can make
  the A2 atomic-publish protocol durable across power loss.
- **Current workaround:** `StdFsNvfsClient.sync(...)` returns
  `NvfsError.Unsupported`. `_do_pack` writes + renames without an intervening
  fsync; on a crash between `rename(data-NNN.bin.tmp -> data-NNN.bin)` and
  `rename(manifest.sdn.tmp -> manifest.sdn)` the kernel page cache may
  reorder the rename vs. the data write, leaving readers with a published
  manifest that references stale-on-disk chunk bytes.
- **Measured impact:** no steady-state perf hit (only on publish). Correctness
  hit: an unrecovered crash during publish can violate the R3 fencepost
  contract (manifest is supposed to be the last durable artifact).
- **Proposed mapping:** `fs_sync(obj, SyncScope.MediaDurable)` + a directory
  sync variant; see `doc/05_design/nvfs/svllm_requirements.md` §R4.
- **Priority:** P1 (A2 ships without it; real fleets must have it before A4
  production writes).
- **Status:** open
