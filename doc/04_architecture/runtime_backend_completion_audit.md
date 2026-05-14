# Runtime Backend Completion Audit

Updated: 2026-05-14

## Objective Restatement

Refactor the Simple runtime libraries so compatibility families depend on a no-GC async/no-GC backend where behavior allows it, keep sync/GC variants as facades when they do not need independent behavior, prevent SimpleOS lower layers from depending on POSIX compatibility modules, and document the production backend ownership model.

## Evidence Checklist

| Requirement | Current evidence | Status |
| --- | --- | --- |
| Async/GC exact-copy runtime hooks are not duplicated across families | Scan over `src/lib/gc_async_mut` and `src/lib/nogc_async_mut` reports `exact_duplicate_runtime_hook_count=0` for files that match `nogc_sync_mut` byte-for-byte and declare `extern fn rt_*`. | Closed for exact-copy class |
| GC compatibility surfaces use no-GC async when async behavior must be preserved | `gc_async_mut/io/buffer.spl`, `gc_async_mut/torch/ffi.spl`, and `gc_async_mut/svllm/nvfs_client/*` are facades over `nogc_async_mut` backends. | Partially closed |
| Async compatibility surfaces use shared no-GC backends when behavior is identical or import-drift only | Reviewed facade closures are recorded in `runtime_family_support_matrix.md`; targeted `simple check` passed for each changed facade slice. | Partially closed |
| SimpleOS kernel/services/SOSIX do not depend on POSIX compatibility modules | `rg -n 'use os\.posix|std\.os\.posix|os\.posix\.' src/os/kernel src/os/services src/os/sosix -g '*.spl'` returns no matches. Shared FD/process/pipe/socket ownership lives under `src/os/kernel/`; `src/os/posix/` modules are facades. | Closed for scanned lower layers |
| Production architecture is documented | `runtime_family_support_matrix.md` records current facade closures, SimpleOS POSIX boundary, and remaining runtime-hook review items. | Partially closed |

## Remaining Gaps

| Gap | Evidence | Next action |
| --- | --- | --- |
| No-GC async backend modules still carry behavior-diff runtime hooks with sync counterparts | Current scan reports 5 files / 182 hook declarations: `nogc_async_mut/torch/ffi.spl`, `cuda/ffi.spl`, `cuda/mod.spl`, `gpu/memory.spl`, `io/file.spl`. `nogc_async_mut/io/buffer.spl`, `nogc_sync_mut/io/buffer.spl`, and `nogc_async_mut/http_server/response.spl` now use pure text/byte conversion helpers instead of runtime hooks. | Treat remaining files as backend modules unless review proves they should delegate to another backend. |
| GC async still has GC-only runtime-hook files | Current scan reports 45 GC async hook files / 456 hook declarations; sampled largest files are GPU/vendor/browser-renderer surfaces with no no-GC counterpart. | Review by domain: GPU/vendor backends, browser renderer surfaces, and any portable non-GPU leftovers. |
| Full-family verification has not run | Only targeted `simple check`, scans, and `git diff --check` were run for the changed slices. | Run full `src/lib` and relevant SimpleOS checks once remaining backend ownership decisions settle. |
| Sync-backed-by-async policy is not globally proven | The current architecture still uses `nogc_sync_mut` as the canonical backend for many compatibility facades where async behavior is not required. | Decide whether this is accepted backend policy or migrate selected sync surfaces onto blocking wrappers over `nogc_async_mut`. |
