# SOSIX route manifest v1: positioned file I/O slice

Status: **partial RU-001 census**, source inspected at `a96a46ae0ff` on 2026-09-26. This manifest does not close the global RU-001 gate. It records the first vertical slice and makes unclassified routes visible so another agent can extend the same manifest without inferring implementation from the proposal.

## Route keys and profiles

| Key | Route | Profile |
|---|---|---|
| H | Hosted `SosixHostedFs` ring → provider → typed completion | Hosted, no-GC async-mut capsule; portable provider or Linux `io_uring` provider |
| P | `sosix_posix_*` → SFFI descriptor extern → native runtime / interpreter extern | Hosted POSIX alias; native and seed interpreter differ at their final binding |
| K | SimpleOS trap 134/135 → retained authenticated dispatch owner → registered-buffer VFS backend | SimpleOS kernel; only after explicit owner/backend installation |
| C | Compiler three-payload worker → hosted in-memory provider | Compiler worker with prepared bytes; no physical file access in the worker |

## Classified symbols

Signatures below use the source declaration's parameter and result types; member methods omit the receiver. “Caller” names a verified direct caller or exported consumer, not a claim that every transitive caller was found.

| Symbol and source | Category; signature | Caller → owner → route | Disposition |
|---|---|---|---|
| `SOSIX_FS_READ_AT` / `SOSIX_FS_WRITE_AT`, [`file_operation_v1.spl`](../../../../src/lib/common/contracts/sosix/file_operation_v1.spl) | Service IDs `0x0101` / `0x0102`; `sosix_file_operation_create(SosixOperationId, u32, SosixCapabilityRef, SosixBufferRef, u64, u64, u64, u64) -> SosixFileOperationResult` | Hosted `SosixHostedFs._submit`; common contract owner; H/C | Retain canonical typed operation and validation. |
| `SosixHostedFs.read_at`, [`fs.spl`](../../../../src/lib/nogc_async_mut/sosix/fs.spl) | Async submission; `(SosixCapabilityRef, SosixBufferRef, u64, u64, u64, u64) -> SosixFsSubmit` | `sosix_sync_fs_read_at` and direct callers → hosted ring owner; H/C | Retain ring lease through provider completion and retirement; provider selection remains caller-owned. |
| `sosix_sync_fs_read_at`, [`sync.spl`](../../../../src/lib/nogc_async_mut/sosix/sync.spl) | Sync adapter; `(SosixHostedFs, SosixSyncWaitDriver, SosixCapabilityRef, SosixBufferRef, u64, u64, u64, u64) -> SosixSyncResult` | Hosted file-driver specs and compiler three-payload worker → sync wait owner; H/C | Retain bounded wait over the same ring operation. No independent lifecycle. |
| `SosixHostedFileDriver.service`, [`file_driver.spl`](../../../../src/lib/nogc_async_mut/sosix/file_driver.spl) | Portable provider; `(SosixHostedFs) -> bool` | `SosixSyncWaitDriver.wait_once` → hosted file driver; H | Uses path-based `file_read_text_at` / `file_write_text_at`; maps failures to `-5`. Keep as fallback, track exact errno and descriptor-route migration. |
| `SosixLinuxUringFileDriver.service`, same source | Linux provider; `(SosixHostedFs) -> bool` | `SosixSyncWaitDriver.wait_once` → Linux file driver; H | Uses native driver open/read-or-write/close operations. Exact Linux provider admission and native evidence remain open. |
| `sosix_posix_pread`, [`posix.spl`](../../../../src/lib/nogc_async_mut/sosix/posix.spl) | Raw alias; `(i32, i64, i64, i64) -> i64` | `posix_spec.spl` and capsule export → hosted alias owner; P | Keep exact byte-count/`-errno` contract; native zero-wrapper lowering still needs object-code proof. It is not the current hosted file-driver implementation. |
| `file_pread_fd` / `rt_fd_pread`, [`sffi/fs.spl`](../../../../src/lib/nogc_sync_mut/sffi/fs.spl) | FFI binding; `(i32, i64, i64, i64) -> i64` | `sosix_posix_pread` → SFFI owner → runtime / interpreter; P | Keep raw descriptor binding separate from safe file adapters. Native C implementation is in `src/runtime/runtime_native.c`; seed interpreter binding is in `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`. |
| `_object_broker_read_v1`, [`three_payload_worker_io_v1.spl`](../../../../src/compiler/80.driver/cache/worker/three_payload_worker_io_v1.spl) | Compiler consumer; `(_ThreePayloadObjectBrokerV1, SosixCapabilityRef, i64) -> Result<[u8], ThreePayloadFallbackV1>` | Three-payload worker → in-memory provider → hosted ring; C | Keep prepared-byte boundary. This use of SOSIX is logical worker I/O, not proof that compiler source/cache physical reads use SOSIX. |
| `SOSIX_FS_PREAD_REGISTERED_V1` / `sosix_fs_positioned_syscall_args_v1`, [`positioned_syscall_v1.spl`](../../../../src/os/sosix/fs/positioned_syscall_v1.spl) | Syscall ID 134; `(u64, u64, u64, u64, u64, u64, u64) -> SyscallArgs` | User ABI shim → SimpleOS FS contract; K | Retain pointer-free envelope. Standalone `sosix_fs_handle_positioned_registered_v1` validates then returns `-95`; it is not the installed provider route. |
| `spl_handle_fs_pread_registered_v1`, `src/os/kernel/abi/syscall_shim_positioned.spl` | Trap export; six `u64` args `-> i64` | x86_64 trap → retained shim state → `sosix_fs_kernel_dispatch_positioned_v1`; K | Keep caller identity from scheduler and explicit owner/backend installation. Uninstalled route fails closed. |
| `sosix_fs_dispatch_positioned_with_owner_v1`, [`positioned_dispatch_owner_v1.spl`](../../../../src/os/sosix/fs/positioned_dispatch_owner_v1.spl) | Kernel owner; `(SyscallArgs, bool, u64, SosixFsPositionedDispatchOwnerV1, SosixPositionedVfsBackendV1) -> SosixFsPositionedDispatchStateV1` | Kernel dispatcher → authenticated provider bridge; K | Retain returned owner state and consume request token only for successful syscall result. |
| `sosix_fs_dispatch_positioned_registered_v1`, [`positioned_syscall_provider_v1.spl`](../../../../src/os/sosix/fs/positioned_syscall_provider_v1.spl) | Authenticated provider; `(SyscallArgs, SosixFsPositionedProviderFactsV1, SosixFsServiceRegistryV1, SosixPositionedVfsBackendV1) -> SosixFsPositionedProviderResultV1` | Dispatch owner → service transaction → positioned VFS; K | Retain unique caller-owned capability and buffer registration checks. |
| `SosixPositionedVfsBackendV1.read_at`, [`service_vfs_backend_v1.spl`](../../../../src/os/sosix/fs/service_vfs_backend_v1.spl) | Backend trait; `(u64, u64, u64) -> Result<[u8], text>` | `sosix_fs_service_dispatch_vfs_v1` → installed FAT32/NVFS/DBFS typed backend; K | Retain cursor-independent positioned contract; backend availability is checked before dispatch. |

## Open classification and evidence

1. **RU-001 global census remains open.** Enumerate every service declaration, `rt_*` OS call, native POSIX import, Future implementation, host render call, interpreter dispatch, loader import, and provider owner across the tracked tree. This file covers only positioned file I/O. Each additional family needs its own rows with signature, callers, owner, route, profile, and disposition.
2. **Hosted routes are separate.** The portable file driver does not call `sosix_posix_pread`; the exact descriptor alias is a separate public route. Do not report the alias's native direct call as evidence for the file driver.
3. **SimpleOS admission is conditional.** The trap shim retains a typed default FAT32 backend and can install another typed route, but dispatch rejects until an authenticated registry owner is installed. Native board and QEMU execution evidence must identify the installed owner and backend.
4. **Cross-runtime evidence remains open.** The Rust seed interpreter and native C runtime both implement `rt_fd_pread`; equivalence, direct native lowering, and the self-hosted interpreter route need executable evidence. The existing `posix_spec.spl`, hosted file-driver specs, and SimpleOS positioned specs are test surfaces, not a substitute for that comparison.
5. **Next inventory pass.** Start with interpreter extern registration, pure-Simple compiler driver and loader imports, Future implementations, and host renderer calls; assign a route key to each symbol. Mark ambiguous callers unresolved rather than assuming a migration is complete.

### 2026-09-26 async completion addendum

The companion [async completion route manifest](sosix_async_completion_route_manifest_v1_2026-09-26.md) classifies the legacy, hosted, SOSIX ring, and SimpleOS Future/task surfaces. It closes one family of RU-001 classification, while the global census and RU-021 runtime qualification remain open.

### 2026-09-26 compiler/interpreter/loader addendum

The companion [compiler, interpreter, and SMF loader route manifest](sosix_compiler_interpreter_loader_route_manifest_v1_2026-09-26.md) inventories selected file, environment, process, and executable-memory effects across those owners. RU-001 remains open for all unclassified services and providers.
