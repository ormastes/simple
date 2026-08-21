# Feature: SimpleOS filesystem toolchain and servers

## Raw Request
> $sp_dev do with pherallel agents with guide and verify of higher model. check simple os’s simple web sever and simple db server works. find history and revive it if not works.
> check llvm/clang port to simple os as exectuable file from fs. impl simple compiler/loader/interpeter like llvm/clang to launch from file system.

## Task Type
feature

## Refined Goal
Restore and prove SimpleOS web/database services and target-native Clang and Simple compiler/interpreter/loader execution from the mounted SimpleOS filesystem in QEMU.

## Acceptance Criteria
- AC-1: A current QEMU smoke proves the SimpleOS web server accepts a real HTTP request and returns the expected response from guest networking.
- AC-2: A current QEMU smoke proves the SimpleOS database server starts and completes a real create/write/read query flow rather than matching only a readiness marker.
- AC-3: History for both server lanes is identified; any stale or broken entrypoint is revived through the existing canonical implementation and documented guide.
- AC-4: The target-native LLVM/Clang executable itself is read from the mounted filesystem and runs in a SimpleOS user process; it then compiles a C hello program whose filesystem-resident ELF is loaded in ring 3 and produces an independently checked result.
- AC-5: The SimpleOS install image contains target-native, non-placeholder payloads at `/usr/bin/simple(.smf)`, `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`, `/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`, `/sys/apps/simple_loader(.smf)`, plus `/SYS/SIMPLETOOL.SDN`.
- AC-6: In-guest `/usr/bin/simple --version` succeeds and the same filesystem-resident toolchain compiles and runs a hello-world Simple source from the mounted filesystem; host `bin/simple`, fixed-command responses, and marker-only apps do not count.
- AC-7: Loader/interpreter launch uses the existing filesystem/VFS executable-source path; GOT-resident launch remains limited to explicit bare-metal metadata.
- AC-8: Executable SSpec and generated manuals cover AC-1 through AC-7 with real assertions, typed evidence, readable `step("...")` flows, and zero generated stubs.
- AC-9: Focused checks, direct-env/runtime guards, numbered-artifact guards, generated-spec layout guard, and relevant compiler/core/MCP gates pass once; final normal/highest-capability review records `STATUS: PASS` only if every AC has direct current evidence.
- AC-10: Relevant SimpleOS/toolchain/server guides and architecture/design/plan artifacts describe the canonical commands, filesystem paths, guest-vs-host distinction, and remaining host limitations.

## Scope Exclusions
Physical-board claims without a supplied board, release/versioning, unrelated dirty work, and replacing existing server, VFS, ELF-loader, or compiler abstractions.

## Cooperative Review
- Lower-model sidecars: server-history/runtime audit; LLVM/Clang filesystem-exec audit; Simple compiler/interpreter/loader install-image audit.
- Merge owner: root Codex agent; sidecars report evidence and proposed minimal paths and do not edit shared dirty files without coordination.
- Final reviewer: root normal/highest-capability Codex agent using `$verify`.
- Shared interfaces: existing `resolve_executable_bytes` / `x86_64_fs_exec_spawn`; existing initramfs/install-image toolchain manifest; existing RV64 HTTP and DB QEMU check entrypoints. No parallel launch abstraction.
- Manual flow helpers: `step("Boot SimpleOS with the server image")`, `step("Send a real guest service request")`, `step("Launch the tool from the mounted filesystem")`, `step("Compile and run hello world in the guest")`.
- Setup/checker helpers: reuse `qemu_rv64_http_test.shs`, `check_simpleos_rv64_db_server.shs`, the canonical filesystem-exec QEMU wrapper, and the install-image content checker; add only the smallest missing checker if evidence shows no existing owner.
- Fail-fast placeholders: any temporarily missing scenario path must use `fail(...)` or `assert(false)`, never marker-only success.
- Generated-manual review owner: root Codex agent after sidecar merge.

## Runtime Boundary Decision
- runtime_need: none assumed; first reuse existing VFS, ELF loader, networking, filesystem, and process facades.
- facade_checked: `resolve_executable_bytes`, filesystem exec spawn, install-image builder, HTTP/DB service entrypoints, app I/O facades.
- chosen_path: reuse-facade; escalate only if focused evidence proves an owner-layer defect.
- rejected_shortcuts: host-side compilation as guest proof, fixed SSH command responses, boot-preloaded executable bytes as general filesystem proof, marker-only server checks, and new leaf-level `rt_*` aliases.

## Phase
implementation


Historical entries through 2026-07-23 are preserved in [state_history.md](state_history.md).

### 2026-08-21 SFTP fail-closed boundary

- SFTP v3 negotiation and bounded framing remain available, while every
  filesystem request fails closed with `SSH_FX_OP_UNSUPPORTED`.
- Atomic beneath/no-follow lookup, paged directory cursors, and per-principal
  namespace capability binding must land together across the driver,
  MountTable, and SFTP layers. Partial adapters were reverted.
- Live OpenSSH/QEMU evidence remains blocked; no Rust-seed substitution or
  capability claim was made.
