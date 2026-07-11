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
design-done

## Log
- dev: Created state file with 10 acceptance criteria (type: feature); defined three parallel audit lanes and highest-capability merge/verify ownership.
- research: Three parallel audits found stale HTTP evidence, no DB server, an unstaged 119 MiB guest Clang blocked by whole-file loading, fake Simple payload evidence, and no live in-guest Simple compiler proof.
- design: Selected existing boot TCP, mounted VFS, ELF mapper, and centralized image role paths; separate HTTP/DB QEMU scenarios avoid speculative multi-listener work.
- impl: Fixed `scripts/os/simpleos-native-build.shs` repository root and SimpleOS target/output contract; it now rejects the Rust seed and fails explicitly because the available self-hosted compiler lacks `native-build --target`.
- evidence: `sh -n` and `--help` pass; the real builder invocation exits 1 with the exact self-hosted target-support blocker. Fresh RV64 build exits 1 because the deployed Rust seed lacks LLVM.
- docs: Added selected requirements/NFRs, local/domain research, architecture/TLDR, design/TLDR, system-test and agent plans; refreshed LLVM, QEMU, and Simple DB guides.
- recovery: Three isolated self-hosted mini-build attempts and one focused check all exited 1 before cache/object output (the check reported a core dump). Recorded `doc/08_tracking/bug/self_hosted_simpleos_target_native_build_crash_2026-07-11.md`; stopped at the iteration cap.
- guards: Scoped diff check, generated-spec layout, SPipe command wiring, direct-env/runtime, and numbered-artifact working guards pass.
- verify: Highest-capability interim review saved at `doc/09_report/verify_simpleos_filesystem_toolchain_servers.md`; `STATUS: FAIL` because live server/toolchain requirements remain unmet.
- impl-loader: Replaced the x86_64 whole-file/preload shortcut with exact-path FAT32 streaming into each validated PT_LOAD frame, retained an explicit blob-backed SMF path, added overflow/short-read guards, and populated bounded SysV binary-path/argv/envp/auxv state.
- impl-db: Added a bounded persistent Pure-Simple `SimpleDbService`; the existing boot HTTP listener now routes real `POST /db` requests through CREATE/INSERT/SELECT state while preserving the existing web response path. The RV64 live wrapper now requires the inserted `codex-41` value rather than a DB bind marker.
- impl-target: Preserved `x86_64-unknown-simpleos` through codegen and routed canonical user executables to the SimpleOS sysroot; legacy `x86_64-unknown-none[-elf]` kernel linking remains isolated.
- impl-image: The target builder now requests the full `src/app/cli/main.spl` entry closure with stub fallback disabled and writes target provenance. Image staging rejects marker payloads, missing/mismatched build stamps, and wrong ELF architecture before copying one payload to all canonical roles.
- review: Highest-capability review rejected the first loader revision because it regressed blob-backed SMF reads and blessed argc=0; both issues plus ELF arithmetic overflow were corrected before acceptance.
- evidence: A manual link probe showed the existing broad generated Simple object links against `build/simple-core/libsimple_runtime.a` plus SimpleOS libc with no unresolved symbols. An isolated target-native Pure-Simple `simple_core` archive build is now the required runtime path; the 17-symbol hello-only sysroot runtime is insufficient for the full CLI.
- blocker: Two fresh self-hosted stage2 focused specs each timed out silently (120s DB spec, 180s target-flow spec); no retry was made. Live QEMU and target payload PASS claims remain prohibited.
