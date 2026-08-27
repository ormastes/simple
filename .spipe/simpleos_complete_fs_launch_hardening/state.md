# Feature: SimpleOS Complete Filesystem-Launch Hardening

## Raw Request

`$sp_dev hardne simple os, on x86, arm, riscv. 1. harden simple web server, and simple db server on file system launch. 2. simple interpreter, compiler, loader porting to simple os and launch from file. 3. port llvm/clang and compile helloworl from fs. 4. list primary linux tools imple in simple and launchable through fs. 5. harden file system to support fat32, dbfs, nvfs, with shared interfaces. and run programs on the the fs. 6. harden simple sshd, simple web server to support all protocole it should support. 7. windows manager working check. go with pherallel and make a complete os. fix duplication and perf bug too.`

## Task Type

feature

## Refined Goal

Deliver a bounded, capability-safe, pure-Simple SimpleOS userland on x86, ARM, and RISC-V (32/64 where supported) that launches authenticated server, toolchain, primary utility, and window-manager programs from FAT32, DBFS, and NVFS through shared filesystem and loader owners, with honest protocol support and measured resource behavior.

## Acceptance Criteria

- AC-1: Web and database servers are installed as authenticated filesystem objects and launched through the canonical snapshot, executable-admission, loader, scheduler, and lifecycle owners on every supported ISA; forged, stale, replaced, noexec, over-cap, and post-exit authority is rejected.
- AC-2: The Simple interpreter, compiler, and loader are target-native payloads in the install image at the canonical `/usr/bin`, `/bin`, `/sys/apps`, and `/SYS/SIMPLETOOL.SDN` locations, and each supported QEMU guest proves `simple --version`, compiles filesystem `hello world`, executes it from the mounted filesystem, reaps the exact child, and preserves its exit status without host `bin/simple`, seed, marker-app, or fixed-command substitution.
- AC-3: The LLVM/Clang/LLD port is installed and executed inside SimpleOS from authenticated filesystem snapshots; Clang compiles a filesystem source into an object, LLD links it, and the loader executes the produced hello-world only after task-bound mutation receipts prove the exact output bytes and atomic receipt-to-snapshot promotion.
- AC-4: A canonical manifest lists primary Linux-compatible tools implemented in pure Simple, their installed paths, command owner, supported options, and per-ISA availability; every advertised tool is genuinely present in the image and filesystem-launchable, while missing tools remain explicit TODO rows rather than aliases, host calls, or fabricated PASS entries.
- AC-5: FAT32, DBFS, and NVFS implement one shared VFS contract for lookup/open/read/write/truncate/rename/fsync/close, stable executable snapshots, mutation receipts, mount and namespace generations, bounded handles, and revocation; aliases and backend-specific fast paths cannot bypass the canonical owner or weaken executable identity.
- AC-6: SSH and web production entrypoints expose only fully owned protocols: bounded HTTP/1.1 and HTTP/2, TLS/ALPN and standards-valid WebSocket where implemented, and SSH host-key exchange, authentication, channel lifecycle, command execution, and SFTP; HTTP/3/QUIC/WebTransport or other incomplete protocols remain explicitly unavailable until their complete owner stacks have live evidence.
- AC-7: The window manager is installed and launched from the filesystem on supported ISA rows and produces a real guest screen with correlated input, frame identity, process lifecycle, and backend evidence; unavailable physical/native-host rows remain blocked with exact resume commands and retained artifacts.
- AC-8: Shared interfaces and app code obey one-codebase/MDSOC ownership: platform differences live in HAL owners, mutable authority never crosses execution domains without owner-result transfer, and no parallel per-OS server, toolchain, filesystem, or WM implementation is introduced.
- AC-9: Every touched hot path has bounded asymptotic complexity and resource caps; reviews cover allocations/copies, data layout/locality, loop hoisting, dispatch overhead, lock scope, and duplication, and later verification records same-input timing plus peak RSS/allocation evidence with no meaningful regression.
- AC-10: Executable SSpec scenarios and generated operator manuals trace every AC across x86, ARM, RISC-V and 32/64 capability rows, using real assertions and explicit blocked/unsupported classifications; no unavailable row is omitted, skipped, or counted as PASS.
- AC-11: Knowledge is refreshed in requirements, architecture, design, plans, `doc/07_guide`, feature- and layer-expert `skill.md` files, and `doc/08_tracking/bug` for every unfixed gap with file/line and unblock condition; must-check ledger TODO rows name an owner and resume action, while PASS rows cite committed receipts.

## Scope Exclusions

- Replacing pure-Simple owners with C/Rust implementations.
- Treating host-side execution, seed execution, marker applications, fixed QEMU commands, source presence, or static review as runtime completion evidence.
- Claiming unavailable physical-board, native-host, protocol, or accelerator rows as PASS.

## Cooperative Review

- Sidecars: filesystem backend convergence, in-guest toolchain/Clang, web server launch, SSH protocol/loader binding, window manager, Linux-tool inventory, and performance/duplication audits.
- Merge owner: `/root`; final reviewer: a separate normal/highest-capability agent for each broad implementation lane.
- Shared interfaces: `StableFileSnapshotHandle`, `ExecutableOpenBinding`, `ExecutableImageHandleV1`, `ServerDataLaunchGrantClaim`, `TaskExecutionInstance`, `VfsObjectIdentity`, `OutputMutationReceipt`, and canonical scheduler execution evidence.
- Manual flow helpers: `step("Install authenticated filesystem payload")`, `step("Launch through canonical admission")`, `step("Observe guest program output")`, `step("Reap the exact child")`, and `step("Reject stale or forged authority")`.
- Setup/checker helpers: shared SimpleOS QEMU settings, host admission, immutable media producer, filesystem-exec row collector, and mission-critical aggregate.
- Any unfinished scaffold must fail explicitly with `assert(false)` or `fail(...)`; no placeholder PASS is permitted.
- Generated-manual review owner: the final independent reviewer for the affected lane.

## Phase

dev-done

## Log

- dev: Created the umbrella state with 11 independently testable acceptance criteria (type: feature).
