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
- compiler-recovery: Focused LLVM call coercion and scalar-global fixes reached an isolated full CLI link, but the runtime selector rejected a valid full archive because it required optional lifecycle hooks; 806 weak stubs corrupted the interpreter `Option.unwrap -> rt_is_none` path. The selector now requires only real CLI hot-path symbols and has a focused archive-selection regression test.
- loader-review: Retained logs prove FAT/NVMe streaming succeeded; a stale kernel left MMIO test mode active and hid valid ELF magic. Current architecture init disables test mode, and the unkeyed global-preload substitution is absent, so the requested path reaches bounded PT_LOAD streaming.
- db-review: Higher review corrected the apparent state-loss diagnosis: broken RV64 `text.len()` truncated `CREATE codex` to `CREATE code`. The boot DB now uses listener-bounded slicing, connection-close framing, and a module-init-safe literal owner; the QEMU producer persists `db_query.log` and the checker rejects `Content-Length: -1`.
- clang-review: Historical guest Clang evidence is LLVM bitcode only; host-produced `hello.o` is not accepted. The existing cc1 disk lane now requests `/hello.o` and fails unless the guest dump is x86-64 ELF REL with `main` and exit 0.
- simple-fs-review: The SimpleOS init flow now distinguishes interpreter success from native compile/run success, and its live SSpec/manual require exact markers and fail closed when the QEMU lane is not enabled.
- concurrency: A separate session bulk-reset the shared checkout at 06:08:13 UTC. Restoration continued in detached worktree `build/worktrees/simpleos-filesystem-goal`; unrelated shared-checkout changes were not folded into this lane.
- current-blocker: A newer 117 MB pure-Simple stage3 from another lane timed out on the bounded `-c 'print(1 + 1)'` smoke and was rejected. No functional non-seed host compiler or target-native Simple payload currently satisfies provenance and runtime gates.
- isolated-checks: Shell syntax, full isolated diff whitespace, generated-spec layout (`0` executable specs under `doc/06_spec`), SPipe dev-command wiring, and direct-env/runtime working+staged guards pass. Live specs/builds were not rerun because no functional non-seed compiler passed its prerequisite smoke.
- traceability-review: Replaced the old always-skip Clang lint spec with a live fail-closed REQ-003 scenario requiring guest object, link, and filesystem-exec markers; link/exec assertions are intentionally red until implemented. REQ-005 now traces the `/usr/bin/simple` version/interpreter/native flow, orders exact markers, and avoids chained text methods.
- clang-provenance: `build_clang_disk.shs` no longer hardcodes the Rust seed; `SIMPLE_BUILD_COMPILER` (defaulting to the self-hosted release path) must be executable and Rust-seed provenance is rejected before kernel/image work.
- clang-link-impl: Enabled the existing embedded LLD in the SimpleOS cross build, removed duplicate cached C/C++ flags on reconfigure, added the single-thread LLD allocator fallback (no fake TLS resolver), and implemented guest compile -> guest link -> exact ELF reconstruction -> FAT32 `/FSEXEC.ELF` -> shared exact-path loader execution. Image generation removes stale outputs and all live skip knobs fail closed.
- clang-build-evidence: Cross Clang/LLD rebuilt successfully. The guest-static relink produced a 122,233,168-byte ELF with `_start`, zero undefined symbols, and SHA-256 `f5bb5e75f5b8bc7abb25c7b0b8baf49aa817381799490b0b3a2ccb4d667aa22b`.
- clang-live-blocker: Three bounded live attempts failed before QEMU during pure-Simple kernel native-build: reserved local `cs` was fixed and now parses; the fresh 766-weak-stub full CLI then failed HIR lowering with a nil receiver; the prior stable pure CLI segfaulted. Recorded `doc/08_tracking/bug/simpleos_clang_fs_pure_compiler_native_build_2026-07-11.md`; no further retry this session.
- clang-final-source-review: Closed the final fail-closed findings: native-build output is logged without a status-masking pipe, nonempty kernel output is required, compile/link QEMU exits must be 3, payload execution QEMU exit must be 171, and every kernel/image is SHA-256 identified before execution. Overall runtime status remains FAIL because the capped attempts never reached QEMU.
- compiler-recovery-2: The unstable-build workflow reproduced the fresh CLI SIGILL in an isolated one-thread shard and diagnostics proved HIR completed before bootstrap MIR started. Root cause was seed `if val` binding a nil `_bootstrap_entry_hir_module`; replaced with explicit presence + typed unwrap and added a regression. A cache-preserving bootstrap then exposed the next real stage2 error, missing `MirLowering.local_is_float`; added the shared F32/F64 predicate and focused source contract. Stage4 remained CPU-bound with no output for 11 minutes and was terminated with 4,905 cached objects preserved. The three-cycle cap is reached; no QEMU retry occurred.
- compiler-recovery-review: Highest-capability read-only review reports `STATUS: PASS` for both compiler fixes and regressions. Overall build remains `FAIL` because no completed post-fix stage4/native artifact exists.
- compiler-recovery-3: Cache-preserving dynload completed stage2 and stage3 after the MIR fixes with zero weak/undefined symbols. The capped full-CLI cycle exposed a Rust discovery-parser failure in `access_cli_grammar.spl`; structured spans and independent parallel audit localized it to three dedented terminal operands at lines 227/243/259. The minimal indentation-only fix passes the Rust bootstrap-seed module check. No additional bootstrap or QEMU attempt was made this turn.
- compiler-recovery-4: The fixed cache produced a fresh stage2 pure compiler (`a5bd7c...`, zero uppercase weak definitions) and passed `native-build --target` provenance. Stage4 smoke initially passed only because the bootstrap script opted into 3,216 weak definitions; strict no-stub mode and stale-output removal now fail honestly on optional runtime/entry-closure unresolved symbols. The stage2 compiler nevertheless built the current x86_64 filesystem-exec kernel from 257 modules with zero failures (`d247013...`, 21,592 KiB).
- clang-gate-4: Three bounded gate attempts stopped before QEMU at FAT image generation. The legacy pure runner silently produced no prefix; replacing it with a native-built existing writer exposed six noncanonical array `.length` uses, now `.len()`. The writer then compiled as a 52 KiB host ELF but segfaulted before output. No Clang guest compile/link/exec claim is made; diagnose the writer runtime ABI before retrying next turn.
- runtime-file-bytes-fix: Existing-binary disassembly proved the native writer jumped from `rt_file_read_bytes` to `spl_file_read`, returning a raw `char*` where compiled `[u8]` callers expect the tagged `RtCoreArray` layout. Its `rt_file_write_bytes` sibling also had three C arguments against codegen's four-argument path/data ABI. `runtime_native.c` now returns `rt_byte_array_new_len` data and matches both canonical signatures; corrected standalone C syntax passes. Runtime execution is intentionally deferred because the Clang gate exhausted its three attempts.
- rv64-live-pass: The zero-weak stage2 compiler built a current 522 KiB RV64 Cranelift kernel from the canonical `src` module root (SHA-256 `788a224cb1553a29b0b403e5c0d866dd79261ec1681c8d56134c9e09011fa6ec`). Its newer nine-field stamp records exact compiler/entry/target/linker/backend/sources/args. One combined QEMU boot passed HTTP `/health`, HTTP `/`, JSON/HTML content types, storage/NVFS, and real DB CREATE/INSERT/SELECT returning `codex-41`; the retained-evidence checker passed all three assertions.
- clang-gate-5: The native FAT writer ABI and packed-byte fixes now produce a valid FAT32 BPB/signature, and QEMU streams/validates the exact 122,233,168-byte Clang ELF. The kernel still traps at BMI2 `shlx` in PMM because the stage2 native-build ignores `--cpu x86-64-v1`; adding `qemu64,+bmi2` did not change the retained trap. Three attempts are consumed and no guest compile/link/exec PASS is claimed.
- cpu-policy-fix: Spark and focused sidecar audits were reviewed against source. Both Rust `rt_native_build` and pure-Simple `cli_native_build` now parse `--cpu`/`--cpu=`, forward the existing `SIMPLE_NATIVE_CPU` seam, and restore pure-path environment state. Rust package check and the focused CPU contract case pass; the wider contract suite retains one unrelated pre-existing failure.
- clang-gate-6: Three capped live attempts used fresh CPU-v1 kernels. The first two localized and removed unsafe Option transport from `pmm_alloc_page_raw`; the final kernel (`7995a823a8a76f44868d9d4d1e6a6d86147a8d135318d53c91ffa02a8106baa5`) reaches valid ELF parsing, PMM/VMM, user-AS creation, and PT_LOAD mapping, then fails rewinding the FAT stream to offset 4096. Source now copies the already-buffered 64-KiB prefix from memory so subsequent disk reads remain forward-only. Its focused check produced no diagnostics for 90 seconds and was terminated; no fourth QEMU attempt was made.
- simple-fs-producer-review: Higher review confirms the Simple-only payload is incorrectly nested beneath full toolchain/rustc staging, and the current raw-disk spec cannot boot. The minimal valid route is a raw nested `/usr/bin/simple` through the streaming loader. `src/runtime/simple_core/core_process.spl` still hardcodes Linux and `rt_process_run` return 3, so real SimpleOS spawn/wait is the REQ-005 implementation blocker.
- final-review: The requested independent high-model review lane failed authentication without edits. The primary highest-capability reviewer repeated the source/evidence gate directly: REQ-001/002 PASS; REQ-003/004/005 FAIL. Spark findings were accepted only where confirmed by source or live evidence.
- simple-core-process-impl: Replaced the fixed `rt_process_run` sentinel with runtime-owned argv construction plus `fork`/`execvp`/`waitpid`; stdout/stderr intentionally inherit the guest console until task-local descriptor inheritance is live-proven. A focused Cranelift target archive contains the real symbol and expected libc imports.
- simple-image-impl: The canonical FAT producer now allocates independent file chains for one real target ELF at `/USR/BIN/SIMPLE`, `/BIN/SIMPLE`, and `/SYS/APPS/SIMPLE`; `fsck.fat` rejected the first shared-chain revision and passes the corrected image structure. The installer no longer emits a nonbootable descriptor fallback.
- focused-tool-review: Guided Spark audits, reviewed against source by the primary high-capability model, rejected the 942-unresolved-symbol desktop CLI closure. The canonical target entry is now the focused real compiler-driver surface `src/app/simpleos_tool/main.spl`; marker/public host-process facades are excluded and provenance remains exact/fail-closed.
- smf-loader-blocker: The same higher review rejected an apparent `CompileMode.SmfExec` success. Direct `.smf` input is parsed as source before mode dispatch; `CodegenPipeline.load_smf_and_execute` uses the compatibility JIT's synthetic bytes/address and returns that address without calling `main`. The curated mapper has no execute entry and its required executable-memory runtime path is not wired into SimpleOS. REQ-005 remains FAIL until a real filesystem SMF/native execution path is implemented and live-proven.
- focused-tool-check: Pure stage2 `check src/app/simpleos_tool/main.spl` remained silent/CPU-bound for 120 seconds and was terminated once. Shell syntax and diff whitespace pass. No repeated source check, target build, image boot, or QEMU attempt was made.
- native-tool-choice: Higher review compared both real candidates and rejected SMF: its producer drops required symbol metadata and its compatibility JIT synthesizes addresses. The focused tool now interprets source in-process and compiles mounted source to a native SimpleOS ELF through the existing LLVM/LLC + static LLD + sysroot lane; the production FAT/NVMe ELF loader is the only execution path.
- static-llvm-tools: Reused the existing SimpleOS static relinker for `llc` and `lld`. Both outputs are static x86-64 ELFs at `_start`, have zero undefined symbols, and were produced without recompiling LLVM libraries. The canonical FAT producer stages those plus static Clang, CRT0, Simple-core, SimpleOS libc, and linker script at FAT-safe guest paths.
- focused-target-build-final: The final allowed strict target-build attempt reached LLD and failed without producing `/usr/bin/simple`. The focused closure is smaller than the desktop CLI but still has 397 external missing symbols after full object-definition subtraction. Real hot-path gaps begin with file/dir/getpid functions; the rest is unreachable generic backend/JIT/CUDA/SQLite surface retained at module granularity. No weak-stub workaround or retry was used. See `doc/08_tracking/bug/simpleos_focused_compiler_entry_closure_2026-07-11.md`.
- focused-dispatch-cut: Guided small-model audits plus higher-model relocation review proved per-function sections work but live `CompilerDriver` dispatchers retain every backend branch. A fresh section-aware stage2 (`372deb53...`) and stage3 built successfully. The guest tool now uses a standalone concrete parse/HIR/MIR/LLVM facade and direct interpreter; the strict unresolved set fell from 397/500 to 15. No target ELF or QEMU PASS is claimed; the three-cycle cap stopped further retries. Objects: `/tmp/.tmpffD0yH`.
- simple-core-runtime-expansion: Added real Dict/enum dispatch, string builder, filesystem/path/time/process primitives, and libc exec argv/envp plus `/usr/bin`/`/bin` lookup. The Simple-core target archive reports `complete=true`. Its combined behavioral probe reached the C probe but exhausted three cycles on a test-source ordering defect; the corrected probe remains unrerun and behavioral status is WARN.
- runtime_need: The target-native focused compiler must read/write guest files, configure the installed LLVM sysroot, and launch LLC/Clang/LLD through the Simple-core ABI.
- facade_checked: Existing compiler and std I/O facades were reviewed; their broad host/runtime imports retain unavailable optional backends in the entry closure.
- chosen_path: `fix-codegen-runtime-owner` for Simple-core ABI functions and `reuse-facade` for the concrete frontend/interpreter/LLVM/linker modules.
- rejected_shortcuts: No weak/zero runtime stubs, fake SMF executor, host `bin/simple`, generic `CompilerDriver`, or in-process dynamic LLD/WFFI fallback.
- current-status: REQ-001/002 PASS; REQ-003/004/005 FAIL. The forward-only Clang loader fix and focused Simple payload both require fresh-session build/QEMU evidence.
- closure-root-fix: Reviewed object evidence showed Cranelift packed every module into one `.text`, so a dead optional function retained all of its unresolved references despite strict `--gc-sections`. Both AOT builders now enable Cranelift's existing per-function and per-data-object sections, with a regression that requires at least two discardable text sections. No ignore-unresolved or weak symbols were added.
- closure-root-check: The first focused Cargo command incorrectly built all integration targets and exhausted disk; its generated target was cleaned. The corrected `--lib` command was then interrupted because another active session removed Cargo output directories during compilation. Neither run reached the regression, and no third retry was made.
- runtime-hot-review: Relocation BFS from `spl_main` identified 32 real missing target ABI functions after excluding 57 Cranelift and two GPU branch alternatives. Higher review also found `rt_dict_new` incorrectly aliases arrays (text-key compiler dictionaries cannot work) and `rt_enum_check_discriminant` always returns true. These are production correctness blockers, not symbols to stub; `rt_getpid` now delegates to SimpleOS libc as the first real hot-path fix.
- focused-driver-fallback-plan: If rebuilt per-function sections do not prune the closure enough, extract exactly `interpret_single_file(path)` and `aot_llvm_native_single_file(path, output)` from shared strict frontend/MIR phases. The focused runner must reject all bootstrap stub/skip envs and import no generic backend factory, JIT, SMF, CUDA, or public host-process facade.
- focused-target-elf: Guided small-model closure audits plus highest-capability review removed the final 15 retained symbols without stubs. A strict fresh build produced the real static x86-64 target ELF at `bin/release/x86_64-unknown-simpleos/simple` (SHA-256 `10d52ba87e706cc424fa450e87a93645d2164ed45299e2155fbb6d2906b6f3a9`, 616 compiled, zero failed).
- simple-fs-live-1: The canonical 512 MiB FAT image staged that ELF at `/USR/BIN/SIMPLE`; production QEMU resolved the nested path, streamed all PT_LOAD segments, built `argc=2`, and entered ring 3. The first run exposed undefined weak `__bss_end`; guarded CRT startup fixed the runaway BSS clear.
- simple-fs-live-2: The guarded payload reached `--version` dispatch and exited zero, but string boxing could not allocate because the production stream lane had no registered anonymous heap. Three guided audits were reviewed; the active `rt_string_new` -> `rt_println_value` ABI is correct, so a conflicting raw-pointer diagnosis was rejected.
- current-blocker: The third and final retry added the proven 64 MiB standalone heap contract, but the kernel exhausted available page mappings at page 5065 and failed closed before user entry. Per-session three-cycle cap reached: do not retry unchanged. REQ-005 remains FAIL; next session must make heap sizing/allocation compatible with the production PMM (or add demand mapping) before version/interpreter/native/loader proofs.
- heap-root-review: Three guided small-model audits and highest-capability ELF/address review proved page 5065 was not exhaustion. The production entry supplied stale kernel end `0x14000000`, while the linked kernel ends at `0x16f51000`; allocation `0x15750000` zeroed the page containing `g_pmm`/`g_vmm`. A conflicting demand-paging expansion was rejected.
- heap-root-fix: The production entry now reuses linker-backed `_get_kernel_start()`/`_get_kernel_end()` and advertises the QEMU default 512 MiB rather than nonexistent 2 GiB. The existing 64 MiB standalone heap remains unchanged. A focused source regression records the invariant; its pure-stage2 interpreter run was terminated once after 90 seconds without diagnostics, and the capped QEMU gate was not repeated.
- version-live-cycle: Three fresh bounded QEMU attempts progressed from PMM rejection to complete PT_LOAD/64 MiB heap/argv-frame mapping and user entry. Attempt 1 exposed tagged linker accessors; their shared C owner now returns raw scalar addresses. Attempts 2/3 reached the CLI but printed usage and exited 2.
- argc-root-review: Guided ELF review proved CRT0 calls `rt_set_args(2, argv)`, but Cranelift emitted the Simple implementation as a no-op and constant-folded `rt_cli_get_args` to argc zero because mutable module globals are not retained in this AOT lane. The two argument slots now live in existing SimpleOS libc static storage behind three narrow functions; SimpleCore's public ABI is unchanged.
- argc-root-build: Rebuilt SimpleOS libc and strict target Simple successfully (616 compiled, zero failed). The new ELF calls `simpleos_runtime_set_args` and loads `simpleos_runtime_argc/argv`; SHA-256 is `7859f1522e587765409dd8655b572ac76a392f8b609cde8cdae0ed1a3bb61b98`. No fourth QEMU retry was made.
- argv-conversion-live: Guided Spark/small-model review moved the complete argc/argv-to-runtime-array conversion into the libc state owner and replaced tagged-byte stack copies with raw NUL-terminated copies. The strict target ELF rebuilt successfully (SHA-256 `f21c338dde66008eea2efc988a197aa96b81c996db132b68d4eb892e2c960f46`; 616 compiled, zero failed), and the canonical FAT image is `a1a8ecf412bdf3bae939cf891abef02eb995c49066bd413a10946e3b9bc70c29`.
- current-blocker: The third and final bounded version boot maps the target ELF, 64 MiB heap, and exact argc=2 frame, enters ring 3, then dispatches `--version` as an interpreter path: three null-argument filesystem syscalls precede an empty `error:` and exit status 1 (QEMU rc 7). This localizes the remaining defect after frame construction and libc array conversion to runtime text identity/dispatch. Do not repeat the version boot unchanged; REQ-005 remains FAIL.
- version-live-pass: Guided sidecars plus higher review found a cross-TU `RuntimeString` ABI split: the producer stored data at offset 16 while the startup-frame helper read offset 12. The shared header now asserts offset 16 and the helper uses canonical accessors. Production QEMU prints exact `Simple v1.0.0-beta`, exits status 0, and returns expected rc 3; checker normalization now handles QEMU's doubled carriage returns. Kernel SHA-256 `8af96dd81fc22e56b563f26191c65c0bf3e6219ef757d5b8bfdacfc7291d8ae3`.
- interpreter-live-cycle: A generated `interpret` profile launched the restaged target Simple from `/USR/BIN/SIMPLE` and read the real 41-byte `/HELLO.SPL`. The first boot localized a fault to `rt_index_get` treating tagged strings as arrays; the shared operator now dispatches strings to `rt_string_char_at`. Host reproduction then exposed zero-initialized parser array globals and optimizer-inlined unchecked length loads. Parser guards now use `rt_array_len_safe`, implemented at both native and SimpleOS libc boundaries; the rebuilt sysroot archive exports the symbol. The final target build stopped at the stale archive before that rebuild, so no further build/QEMU retry is allowed this turn. Interpretation remains FAIL pending a fresh target rebuild and host smoke.
- interpreter-host-cycle-2: A fresh strict target link succeeded (616 modules, zero failed). Three bounded host smokes advanced through deterministic failures: zero-BSS lexer token slots, then raw token kinds `161`/`169` misclassified as heap strings by `rt_native_eq`, then declaration arena allocation. Lexer and token-capture slots now use `rt_array_len_safe`; generic equality requires heap values >=4096; AST/expr/stmt reset owners now install fresh containers and count slots use the safe boundary. Final built ELF SHA-256 `7fd9209c103aa035c8f08ac761c0f2f1ea31116ca0af4e329fef4167c4073c75`; the AST reset fix is newer than that artifact. The three-cycle cap is reached, so no fourth rebuild/QEMU boot is allowed this turn.
- interpreter-host-cycle-3: Three fresh target builds succeeded (616 modules, zero failed). Live host smokes proved AST/expr/stmt reset coverage and localized the remaining frontend issues: `module_decl_slots` was the sole omitted arena, compact zero-argument `fn main:` was rejected, and weak-BSS `_NL` constants made newline bytes token kind 191. The shared reset now initializes `module_decl_slots`, the parser accepts the established compact zero-argument form, and both lexers use literal newlines. The final built artifact parses cleanly and exits 0 but prints nothing; source review found `process_module` gated valid `module.functions` behind a duplicate symbol-table `has_main`. That gate is removed and main is matched directly by `HirFunction.name`, but this newest source is intentionally unrebuilt after the three-cycle cap. Interpreter remains FAIL pending fresh host/QEMU proof.
- interpreter-host-cycle-4: Three more strict target builds succeeded (616 modules, zero failed). The host hello smoke remains silent but exits 0. Read-only breakpoints prove `process_module -> call_hir_function(main) -> try_call_builtin("print") -> rt_println_value` is reached; the final runtime argument is tagged nil `3`. This rejects empty-HIR/main-dispatch diagnoses and localizes the defect to nested `Ok(Value.String(value))` construction losing its inner payload on stage4 AOT, matching the documented FunctionValue hazard. String literal evaluation now hoists `Value.String` into a typed local before `Ok`; payload-bearing String patterns also precede Nil/Unit conversion. These newest sources are intentionally unrebuilt after the three-cycle cap. No interpreter/QEMU PASS is claimed.
- interpreter-host-cycle-5: Replacing the call-argument `?` boundary with an explicit typed `Result<Value, BackendError>` check/unwrap rebuilt successfully (616 modules, zero failed). Target SHA-256 `95f2dc26b00f47f83e097fc4f4be1d3fee76cef8de9eaf2ae38a885e0378409d` prints exact `Hello from SimpleOS` and exits 0 in the bounded host smoke.
- interpreter-qemu-cycle-5: One fresh 512 MiB image/production QEMU attempt streamed `/USR/BIN/SIMPLE`, mapped all PT_LOADs and the heap, built argc=2, and entered ring 3, then timed out rc124 after PF 0xC on the first stack read. Full serial-order review found the preceding causal `ud2` at `kernel__memory__vmm___alloc_table_page`: its `Option<PageFrame>` unwrap lost the struct payload and recovery continued with corrupt page tables. NXE is present in the current kernel, so NX/W^X weakening was rejected. Next bounded fix is the existing raw-scalar `pmm_alloc_page_raw()` owner; no retry this turn after the cap.
- interpreter-qemu-pass: `_alloc_table_page` now reuses `pmm_alloc_page_raw()`. Fresh kernel SHA `ee07b61044a8f3afd96c44b4b07be42c4cb4aec1a014a170a353d577c20856ab` boots, streams the target, reads `/HELLO.SPL`, prints exact `Hello from SimpleOS`, exits 0, and returns QEMU rc3 with final production PASS.
- emit-object-cycle-1: Added the shared emit-object early return, stable sysroot Simple entry shim, profile-selected filesystem executable path, optional HELLO.O/FSEXEC.ELF image roles, and one-way `/USR/BIN/LD.LLD` link profile. Target SHA `4f2b48b31c80e09ee3a6ca2cd2d0919faec0d8feff857e1bee11c1bfc40e784e` opened the real `/HELLO.SPL` in QEMU but exited 1 without an object. Higher review localized the first failure before LLVM/LLC to corrupted composite `mir_lowering.errors[0]`; the patterned pointer masks the actual diagnostic. A final capped rebuild hoists `CompiledModule` before Result.Ok but was not rebooted. The overlapping user/kernel RIP syscall-return heuristic is also recorded; no emit/link/execute PASS is claimed.
- emit-object-cycle-2: Conditional GDB tracing proved zero MIR-error pushes. `MirLowering.new` emitted `loop_stack` and `errors` as kind-6 Dicts, so `.len()` read Dict capacity 8 and indexed garbage. Both now use typed empty-array locals; the earlier `CompiledModule` hoist remains. Rebuild cycle 1 failed with 98 per-file timeouts. `unstable-build-fixes` was applied: cycles 2/3 used an isolated persistent cache with 8 then 1 writer threads, but both spent their full bounded windows in Btrfs contention on the 99%-full filesystem alongside 14+ native builds and produced zero cache objects. No fourth build was run.
- syscall-cpl-root-fix: Serial/disassembly proved low user RIPs near 0x200000 matched the stale `[0x100000,_kernel_end)` LSTAR heuristic and returned at CS8. Kernel-only `rt_x86_syscall` now directly calls `rt_syscall_dispatch`; `syscall_entry.s` has no RIP classifier/ring0 jump and always iretqs to user CS0x2b. Source guards exist, but no post-fix QEMU evidence exists; prior interpreter output cannot claim ring3 isolation.
- syscall-cpl-live-pass: After contention cleared, the isolated one-writer cache-backed target build completed 616 modules/zero failures in 354.5s (SHA `e27d5e534cbdc8a23693c9b4a8af7ba3fee49d1d0bd20442687419980c0567bd`). Updated libc exports `simpleos_current_cs`. Fresh kernel SHA `0c6f70972ddcc6eeea686da0e0901827894b2bca272ca05739a771b9bd19cc81` enters the target at CS0x2b, opens/reads `/HELLO.SPL`, reports exact `[simpleos-cpl] phase=post-read cs=0x2b cpl=3`, prints exact hello, exits0, and returns QEMU rc3/final PASS. Interpreter behavior and ring3 provenance are now both live-proven.
- emit-object-cycle-3: Fresh CPL3 target opened/read `/HELLO.SPL`, then the existing direct LLVM-object helper issued fork/wait syscalls 57/61, received ENOSYS, faulted at user CS0x2b, and timed out rc124 with no output. Higher review rejected fork/scheduler and multi-output RAMFS expansion. The focused tool now emits LLVM IR in-process as its sole output; fresh boots stage that IR and launch filesystem LLC as the sole producer, then LLD similarly. Added optional `/HELLO.LL` image role and profiles `emit-llvm`/`llc-object`. Fixed LLVM header target ownership, removed redundant `spl_init_args` from SIMAIN, and added runtime `rt_print`/`rt_println`. Cache rebuild completed 3 compiled/613 cached, zero failed; target SHA `63b362e327b58ba7718e8f42e446a4ec73e6d058313ff53639bf1d433345e71b`, fresh image SHA `e2dda2bf3009ccb4ab00800150ebcd9d3a9b99d5bdcbf127c11e4004b7865c6d`. No staged-profile QEMU run this turn after the cap.
- emit-llvm-cycle-4: Guided Spark/small-model symbolization localized user RIP `0x526101` to `LlvmTargetTriple.datalayout`: explicit `SimpleOS_X86_64` construction unnecessarily called `get_host_os -> uname` first, producing ENOSYS 57/61 and corrupting the aggregate receiver. `from_target_with_mode` now returns a typed intrinsic SimpleOS triple before all host probing; the focused triple/config/datalayout and source-order regression passes 3/3. Three cache-preserving rebuild attempts were capped: the current release compiler segfaulted twice before output (parallel and one-writer), while the older stage3 spent 14 minutes compiling an over-broad closure and failed on unrelated unsupported app modules. The fix is therefore source-tested but unbuilt; no QEMU rerun or emit-LLVM PASS is claimed. Higher review also requires the hello fixture to return explicit `i64 0` and a duplicate-free C-compat runtime archive before the later LLC/LLD gates.
- emit-llvm-cycle-5: Spark recovered the exact proven producer (zero-weak isolated stage2 + Cranelift + one writer), replacing the stale LLVM/release attempts. Three cache-backed target builds completed with 3 compiled/613 cached/zero failed; final target SHA `a6e5317564b6ea10c632aef1db9e343a8cd162965904952bcd94305460e0f008`, final image SHA `e85715ca7af3c55acba76409658ef600cec71a5beb4115c4bdcf07eb633bb174`. Live QEMU now proves the explicit-target fix: no fork/wait ENOSYS and no user fault, with post-read CPL3. It exits 1 at the newly labeled `phase=hir-error` before MIR/LLVM. A typed shared HIR collection constructor and factory deduplication pass the focused regression 7/7 but did not clear the live HIR error, so a real HIR diagnostic remains hidden by the stage4 `Result<..., text>` error-payload loss. The hello fixture is now explicit `i64`/`return 0`; a clean one-member `libsimple_runtime_compat.a` is the staged link default and has unique `rt_print`/init/shutdown definitions. The three-cycle cap is reached; no LLC/LLD/execute run or PASS is claimed.
- runtime-decision-emit-llvm-hir-diag: `runtime_need` = distinguish a real HIR error push from corrupted target-AOT error-vector readback; `facade_checked` = existing `hir_type_env_get` and focused-tool `rt_env_set`; `chosen_path` = `reuse-facade`; `rejected_shortcuts` = unconditional compiler printing, new raw runtime aliases, module-global diagnostic capture, fixture bypass, and weakening the explicit-i64 ABI.
- emit-llvm-cycle-6: A focused, env-gated push-time marker proved the HIR errors are real: `unresolved type: Option` is pushed twice. A flat-bridge marker then proved `main` enters conversion with correct return tag `TYPE_I64=2`; high review rejected registering Option because that would mask i64 payload corruption and violate the `__simple_main` ABI. Guided comparison found the focused facade used an untyped `HirLowering` local that the normal driver documents as ANY-erased on stage4; it now uses an explicit type and its contract passes. The rebuild produced byte-identical target/image hashes (`0cbbd7e2...63786` / `ec4d7852...d4690`), initially suggesting stale cache. Cycle 7 disproved that inference: a fresh cache key compiled to identical machine code because this annotation is codegen-neutral in the proven producer.
- emit-llvm-cycle-7: Cache inspection corrected cycle 6: the typed edit did create a fresh focused object, but its machine code was identical, so invalidation is healthy and cache deletion was rejected. Three changed target/image pairs then tested the shared HIR Named boundary. (1) Extracting Named before other enum exemplars still produced Option. (2) Direct `rt_enum_payload` slots decoded Option plus nested f64. (3) Moving typed accessors beside the frontend TypeKind owner, with no HirTypeKind import/collision, still decoded the same Option/f64. Every boot retained CPL3, zero host-process ENOSYS, correct flat tag 2, and exact two HIR pushes, then exited 1. Final target SHA `ddab9e4ae824aec22a0c055010164966dd4274283883c45b6cb959bda04d25cb`; image SHA `dc7f6d4cd2e9381ceb17a400e864d6a8916b7333e9592be7a807159fabf25cae`. The three-cycle cap is reached. Next fix must preserve primitive flat tags across a non-enum boundary or repair the stage4 TypeKind construction/payload ABI; do not register Option or weaken the i64 fixture.
- emit-llvm-cycle-7-postmortem: Read-only target disassembly proves both endpoints are correct: `convert_flat_type(2)` constructs `Named("i64", [])` with the expected payload array, and the frontend owner accessors call `rt_enum_payload` plus indexed slots 0/1 correctly. The remaining corruption boundary is the untyped `val fn_ = convert_decl_fn(idx)` aggregate return before insertion into the module function dictionary (`_FlatAstBridge/module_assembly.spl`). Next bounded fix candidate is explicit `Function` locals for normal and extern conversion, followed by before/after insertion markers; high review must accept this stronger assembly evidence before replacing the TypeKind representation.
## 2026-07-12 cycle 8 — HIR boundary fixed; eager-heap ceiling exposed

- The raw flat return tag now survives flat-module assembly and HIR lowering as `i64`; the focused run reached `phase=hir-ok` before allocation returned nil in MIR lowering.
- High-model review traced the nil receiver to `rt_alloc`/`malloc` exhaustion of the production loader's former 64 MiB eager user heap, not a new MIR type defect.
- The focused loader contract passed 4/4 after changing the bounded arena to 65,536 pages (256 MiB).
- Final QEMU evidence: `[spawn] FAIL heap frame alloc i=36047`; the 512 MiB guest cannot eagerly back 256 MiB after kernel/runtime allocations, and filesystem spawn failed closed before CPL3 entry.
- The mandatory three-cycle cap is reached. Do not retry in this session. In a fresh turn, test the bounded 32,768-page (128 MiB) candidate once, or implement demand allocation only with separate design and verification.
- Evidence: `build/os/elfexec/emit_llvm_profile_run12.out`.
- The failed 65,536-page experiment was reverted to the live-proven 16,384-page production baseline; no known-broken loader setting remains in source.
## 2026-07-12 cycle 9 — 128 MiB maps; nil is not bump-heap OOM

- Guided Spark/small-model review selected the existing 32,768-page (128 MiB) eager heap as the smallest safe candidate below the observed 36,047-page physical ceiling; high-model review accepted it without adding scheduler or demand-paging machinery.
- QEMU run 13 mapped all 32,768 pages, entered CPL3, preserved `main -> i64` through HIR, and reproduced the same post-HIR nil-receiver trap.
- A fail-only marker was added to the shared bare-exec `_user_heap_bump`. QEMU run 14 reproduced the trap without emitting `[user-heap] OOM`, disproving bump-arena exhaustion as the immediate cause.
- Next owner-boundary investigation: distinguish `rt_alloc(size <= 0)` from allocator-internal failure before another behavioral fix. Do not increase the heap again without new evidence.
- Evidence: `build/os/elfexec/emit_llvm_profile_run13.out`, `build/os/elfexec/emit_llvm_profile_run14.out`.
## 2026-07-12 deployed-runtime recovery

- Spark and high-model GDB review proved the deployed 42 MiB pure-Simple ELF still implements the obsolete two-argument `rt_env_set`; current four-argument callers pass key length in argument 2, which the stale callee dereferences as the value pointer and crashes in libc `strlen`.
- A full isolated bootstrap first exposed and removed a duplicate `module_init_symbol`; the retained implementation is the one covered by the dotted-module regression.
- The next two cache-preserving cycles reached stage 4 and failed honestly on missing `rt_array_len_safe`. The existing safe `rt_array_len` owner now has a one-line `simple_core` facade, and the missing Rust static SFFI registry row is present.
- The mandatory three-cycle cap is reached. Do not rebuild again this turn. Next fresh turn: resume the same cache once, require focused `check` to pass, then inspect the rebuilt `rt_env_set` machine signature before deployment acceptance.
- Evidence: `build/bootstrap/sync-runtime-bootstrap*.log` and `build/bootstrap/sync-runtime/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`.
## 2026-07-12 self-host recovery — interpreter-safe array length

- Guided Spark/small-model preflight plus high-model review localized the bootstrap failure across three owner registries: native SFFI signature, seed-interpreter extern dispatch, and the Simple-core facade.
- `rt_array_len_safe` now delegates to existing `rt_array_len` in Simple-core, is declared `(I64)->I64` in the static SFFI registry, and has a dedicated seed-interpreter handler for `Value::Array`, raw runtime arrays, and invalid values. A focused Rust regression covers interpreter arrays.
- Fresh stage 2 and self-hosted stage 3 succeeded. Stage2 SHA-256: `17ae4bedae2a1f07641f1b733041f43be67ff3fea3133a9312b2dd289c0dc34c`; stage3: `b1070f110c1eb713eb4e2fa679a7eac44e0227ca088817cd7d968cbc7a36e9aa`. Spark disassembly verified the stage2 runtime consumes all four `rt_env_set` arguments.
- The resumed strict stage 4 reached final link and failed because the bootstrap owner command selected `core-c-bootstrap` for a hosted full CLI. Both stage4 branches now pass the existing `--runtime-bundle rust-hosted` option.
- Three-cycle cap reached; do not rebuild again this turn. Next fresh turn: resume only stage 4 from the proven stage2/cache, then require exact full-CLI hash, zero uppercase weak definitions, four-argument env ABI, `--version`, `-c 'print(1+1)'`, focused check, and focused interpreter spec.
- Evidence: `build/bootstrap/sync-runtime-bootstrap-retry{3,4,5}.log`, `build/bootstrap/sync-runtime-stage4-resume.log`.
- Correction: current Cranelift native-build intentionally rejects the removed `rust-hosted` bundle name, and `SIMPLE_RUNTIME_PATH` does not override its supported core bundle lane. The full host CLI closure still includes hosted-only/platform symbols and remains a separate bootstrap blocker; no ineffective runtime-path workaround remains in the script.
## 2026-07-12 focused SimpleOS target rebuild handoff

- Full host CLI recovery remains separate: current native-build supports only `simple-core`/`core-c-bootstrap`; the full CLI entry closure still pulls hosted-only/platform symbols. Removed bundle names and `SIMPLE_RUNTIME_PATH` do not change the Cranelift bundle lane, so no workaround remains in the bootstrap script.
- The final cycle used the proven self-hosted stage2 compiler to build `src/app/simpleos_tool/main.spl` for `x86_64-unknown-simpleos`. Compilation reached target link, but this isolated workspace lacks the target Simple-core archive, leaving core `rt_*` symbols undefined.
- The canonical next action is `scripts/os/simpleos-native-build.shs`, which first builds the target archive with `check-simple-core-runtime-smoke.shs`, places it in the sysroot, and exports `SIMPLE_SIMPLE_CORE_PATH` before native-build. Do not reuse the old worktree's archive as unproven current evidence.
- Three-cycle cap reached. Next fresh turn: run the canonical wrapper once with the stage2 compiler and focused entry, verify the exact target ELF/hash, then bake and run the emit-LLVM filesystem profile.
- Evidence: `build/bootstrap/simpleos-tool-target-current.log`.
## 2026-07-12 current focused target PASS

- The canonical wrapper now bootstraps a missing SimpleOS sysroot before building/copying the current target Simple-core archive. This makes fresh workspaces provide the complete `crt0.o` + runtime + libc tuple required by Rust target linking.
- Restored the conflict-lost `llvm_translate_module_direct_ir` owner helper in `llvm_codegen_adapter`; it uses `module.name` and the explicit `options.target`, and the existing direct compile path reuses it.
- Fresh focused target build PASS: `bin/release/x86_64-unknown-simpleos/simple`, SHA-256 `ef40c3ea4486d90b1d71e6b2e86b8da64f7a11dbae94461adad00c9074efc16a`, 3,692,112 bytes, ELF64 x86-64 ET_EXEC, static/no dynamic section, entry `0x202080`, zero defined uppercase `W`, zero strong `U`.
- Target Simple-core SHA-256 `c782eacad9e68def0ea79afc280de62be699c53e4d15f407a15d6be3da5ff1f8`; sysroot copy matches. Each required symbol `rt_string_replace`, `rt_to_string`, `rt_array_new`, `stdin_read_char` has exactly one strong definition.
- Build stamp is newer than the ELF and records target `x86_64-unknown-simpleos`, entry `src/app/simpleos_tool/main.spl`, entry closure, Cranelift, and self-hosted stage2 producer.
- Next gate: restage or rebuild cross LLC/LLD in this pinned workspace, bake the fresh target into a new image, and run one emit-LLVM QEMU profile. Do not claim filesystem compile/run from the target ELF alone.
- Evidence: `build/bootstrap/simpleos-native-build-current3.log` and the target/stamp above.
## 2026-07-12 LLVM guest-tool relink handoff

- High-model review rejected reusing static guest LLC/LLD whose sysroot link inputs were newer. The existing cross LLVM objects remain reusable; only static relink is required.
- `clang_static.shs` now links the full sysroot `libsimple_runtime.a` beside `libsimpleos_c.a`, because current libc calls Simple array/string ABI owners. The compatibility-only archive was insufficient.
- LLC relink reached a static ELF with `_start` and exactly one strong undefined symbol, `rt_math_pow`. Codegen intentionally emits the real `(f64,f64)->f64` ABI; SimpleOS libc now owns a one-line wrapper delegating to its existing `pow` implementation.
- Three LLC relink cycles reached the mandatory cap. Next fresh turn: force current SimpleOS libc/sysroot rebuild so the wrapper enters `libsimpleos_c.a`, relink LLC once, then LLD once, validate zero strong undefineds/hashes, and bake the fresh compiler image with no staged `/HELLO.LL`.
- Evidence: old artifact lane `build/os/llc_static/relink-current{,2,3}.log`.
## 2026-07-12 fresh filesystem emit-LLVM cycle 1

- Baked `build/os/elfexec/fat32-simple-toolchain-current.img` from the fresh focused compiler and relinked static Clang/LLC/LLD. The 512 MiB image SHA-256 is `c5195b1c321f4f155aeeb21a583987be3fd2e19db5ded4dd04982954c2e6b8bd` and its timestamp is newer than the compiler.
- The production ring-3 lane loaded `/USR/BIN/SIMPLE`, parsed its ELF, mapped all `PT_LOAD` segments, constructed six CLI arguments, and entered CPL3 at `0x202080`.
- Emit-LLVM did not reach HIR. The fresh executable page-faulted at `spl_main+0x85` (`0x208b95`) while reading offset 8 from nil after the `rt_cli_get_args` / `rt_unwrap_or_self` startup sequence; CR2 was `0x8`. QEMU timed out with rc 124 instead of the expected debug-exit rc 3.
- This is verification/fix cycle 1 for the fresh image. Next cycle must repair the target CLI argument handoff/startup ABI and then rerun this profile once; do not alter WebIR/DrawIR or GUI/web/2D shared IR for this native filesystem failure.
- Evidence: `build/os/elfexec/emit_llvm_profile_current.out` and `build/os/elfexec/prod_ring3_run.log`.
## 2026-07-12 filesystem emit-LLVM heap verification handoff

- Cycle 2 reused the existing 64 MiB user-heap mapper for normal streaming filesystem spawn and separated returning exit from the explicit QEMU-halting smoke mode. It proved `[spawn] user heap mapped` before CPL3, but the new computed size argument arrived as zero; the returning owner now takes only the fixed base and owns the already-specified 64 MiB size.
- Cycle 3 passed the former `rt_cli_get_args`/`args.len()` fault, entered the focused compiler, and opened `/HELLO.SPL`. It then exposed a distinct address-layout collision: the user compiler is linked at `0x200000` while the kernel bump heap begins at `_heap=0x215080` and spans 192 MiB. Under the user CR3, the file-open syscall reads user PT_LOAD bytes as kernel `_heap_off` (`0x6502c641000001c9`) and halts with `heap exhausted`.
- The canonical SimpleOS userspace linker script already places `.text` at `0x10000000`; the current focused Cranelift target did not consume it. The next fresh turn must rebuild the focused target through the existing LLVM SimpleOS link path (or make the Cranelift SimpleOS linker select the same sysroot script), require entry/PT_LOAD at `0x10000000`, rebake, then run emit-LLVM once.
- The mandatory three-cycle cap is reached. Do not rerun this profile in this turn. WebIR/DrawIR remains N/A: this is a native address-layout/linker selection defect.
- Evidence: `build/os/elfexec/emit_llvm_profile_heap_fix{,2}.out`, `build/os/elfexec/prod_ring3_run.log`, `src/os/port/llvm/sysroot.shs`.
## 2026-07-12 canonical-layout and desugar handoff

- Guided Spark confirmed the canonical LLVM SimpleOS link route; a small audit localized the Cranelift omission to Rust `NativeProjectBuilder`. The shared linker now defaults x86_64 SimpleOS to `<sysroot>/share/simpleos/simpleos.ld`, preserves explicit overrides, fails closed when missing, and leaves non-SimpleOS targets unchanged. Its focused Rust test passes 1/1.
- The deployed focused Cranelift compiler was rebuilt with the same canonical script: static ELF64, entry and first `PT_LOAD` `0x10000000`, no `PT_INTERP`, zero strong undefineds. Final cycle artifact SHA-256 is `367fed3ae83e3f8af01dcdf31417952626d6382d328bf57a18f382bf4792824a`; image SHA-256 is `d2130fc2cb8162347d351829860019eca1b298fe021ae819fba71826d5f9c17e`.
- Loader review fixed literal 4096-byte heap mapping, explicit 64 MiB bounds, returning-vs-halting exit mode, and per-exec RAMFS reset. Guest proof now maps the heap, enters CPL3 at `0x10000000`, reads `/HELLO.SPL` from NVMe, and reaches the parser/HIR bridge.
- Cycle 1 exposed unsafe inlining in `rt_array_len_safe`; an explicit low-value guard is present in machine code. Cycles 2/3 then localized a nil `Function` to dictionary tuple iteration in `desugar_module`. The duplicate Simple-core `rt_for_iterable` owner was deleted, all desugar dictionaries now use `keys()` plus typed lookup, and callers retain `desugar_module`'s returned Module.
- Three-cycle cap reached before rebuilding the final desugar-key fix. Next fresh turn: rebuild target/runtime/image once, require `phase=hir-ok`, `phase=mir-ok`, `phase=ir-ready`, post-write CPL3, `/HELLO.LL` dump, and exit 0; do not repeat already-green layout/heap checks separately.
- Evidence: `build/os/elfexec/emit_llvm_{layout,safe,iterable}.out`, `build/os/elfexec/prod_ring3_run.log`, `build/bootstrap/simpleos-native-build-{cranelift-layout,safe-array,iterable}.log`.
## 2026-07-12 HIR-to-MIR payload handoff

- The final key-based desugar rebuild passed its prior nil-Function trap. A complete `parser_function_new` reconstruction fixed dropped Function metadata and produced live `phase=hir-ok` with `main -> i64`.
- Guided cycle 2 localized raw null between `[HirStmt]` indexing and positional `HirStmt` destructuring. MIR now uses a typed array read plus direct `stmt.kind`/`stmt.span` fields.
- Cycle 3 changed the failure from raw null to a garbage frontend expression pointer in `MirLowering.lower_expr`, proving statement transport improved. The HIR statement source already documented that stage4 pattern-extracted `StmtKind.Expr` payloads are garbage and declared `rt_enum_payload`, but still used the broken pattern binding; it now uses `rt_enum_payload(stmt_kind_value)` exactly as documented.
- Three-cycle cap reached. Next fresh turn: rebuild only the focused target/image once and rerun emit-LLVM. Required evidence remains HIR/MIR/IR markers, post-write CPL3, `/HELLO.LL` dump, exit 0, and wrapper rc3; if green, decode and validate with `llvm-as-18` before LLC/LLD/execute phases.
- Latest tested artifact SHA-256 `67cde9ce8224cdfeebb25f1e80c353ccfa2e7b522d8eb5346ab115a5411cd0fe`; image `875a57b5baa7c039d71c99809907a1c5c8c58d4a8383e650857fc1af94d34570`.
- Evidence: `build/os/elfexec/emit_llvm_{desugar,complete_function,direct_hirstmt}.out` and `build/os/elfexec/prod_ring3_run.log`.
## 2026-07-12 enum-payload boundary handoff

- Spark and a small ABI audit confirmed the frontend `StmtKind.Expr` / `StmtKind.Return` payload extraction is one-word ABI-compatible with the single target Simple-core `rt_enum_payload` owner. Both branches now use that owner; valid target enums use kind 4/tagged pointer/payload +16.
- Cycle 1 showed the frontend payload change alone did not alter the MIR garbage pointer. Cycle 2 added Return extraction and remained at the same MIR boundary.
- Higher-model review found MIR still matched an unresolved `kind` after the outer positional `HirStmt` destructure was removed. Cycle 3 rebuilt with `stmt_kind_value` and a MIR-side `rt_enum_payload` call. The fault changed from a machine-code-like garbage pointer to tagged nil at `MirLowering.lower_expr` (`0x101c44a2`), proving the new boundary executes but does not recover a valid HirExpr payload.
- Three-cycle cap reached. Next fresh turn must inspect the actual target representation of `HirStmt.kind` before changing code: log/disassemble its discriminant, object kind, and payload at the producer and consumer, then choose either a direct typed field/accessor or correct runtime owner. Do not weaken `lower_expr` to accept nil.
- Latest tested compiler SHA-256 `760b2d05720bd80fd03e5383c85f8fba69af8765d71e34959a5da11e3f92e9ca`; image `54e794f01091308e07a5c8fd6ef26036fa85d4d4a959375fd2964464a103f02f`.
- Evidence: `build/os/elfexec/emit_llvm_{enum_payload,return_payload,mir_payload}.out` and `build/os/elfexec/prod_ring3_run.log`.
## 2026-07-12 typed HirStmt and block-value handoff

- Spark disassembly proved the rebuilt HIR producer constructs a direct `HirStmtKind.Expr(HirExpr)` kind-4 enum and the MIR consumer receives the same direct payload; no tuple projection is valid. The producer's inferred `kind` is now explicitly `HirStmtKind`, and MIR uses a qualified typed match.
- Cycle 1 retained the recursive nil trap; cycle 2 ruled out Return's known-broken `if val` optional binding by replacing it with positive presence plus typed unwrap.
- Cycle 3 enabled the existing trace flag only for diagnosis. It proved print statement 0 lowers successfully, then `HirBlock(stmts=1, has=true)` reaches `block:value-read` and crashes because `if val actual_value = block.value` binds nil. `HirBlock.value` is nonoptional and guarded by `has`; MIR now directly lowers the typed `block.value`. The temporary global trace flag was removed.
- Three-cycle cap reached before rebuilding the direct block-value fix. Next fresh turn: rebuild target/image once and run emit-LLVM; expect `block:value-lowered`, MIR/IR markers, post-write CPL3, output dump, exit 0. If green, immediately decode/validate IR and continue LLC/LLD/execute using existing profiles.
- Latest diagnostic compiler SHA-256 `895b3aedae0589ed6d861f78da4957f239c5432a9f338b34793297763bb0124c`; image `8e08a7a83357eff6dd85ac87bf0dbefef3bd6d7ae72a00ca65ff0c49379f617b`.
- Evidence: `build/os/elfexec/emit_llvm_{typed_hirstmt_kind,return_unwrap,mir_trace}.out` and `build/os/elfexec/prod_ring3_run.log`.
## 2026-07-12 MIR PASS and LLVM target handoff

- The rebuilt direct `HirBlock.value` fix passed live: HIR and MIR both report OK. The first backend cycle then exposed `LlvmTargetTriple.datalayout` on an invalid triple after hosted fork/wait ENOSYS.
- `CodegenTarget.SimpleOS_X86_64` was compared with enum pointer equality. A qualified discriminant match removed host probing in cycle 2, proving target selection, but the returned target struct was still erased before datalayout.
- Cycle 3 used a typed target triple constructed outside the match; HIR/MIR remained green and no ENOSYS occurred, but datalayout still received an invalid `self`. Review found the portable config immediately rebound the triple through untyped `val triple`; that local is now explicitly `LlvmTargetTriple`.
- Three-cycle cap reached before rebuilding the typed config local. Next fresh turn: rebuild target/image once, require HIR/MIR/IR/post-write/output/exit markers; if green decode and validate IR then continue existing LLC/LLD/execute profiles.
- Latest tested compiler SHA-256 `8d90374665152f87618fa52c1536799c6a1253c6e5a98998627e585ee825f647`; image `fbc978d4dd1a075b1d10204664ba5233f5bb249b086f508008dd7ae468adc736`.
- Evidence: `build/os/elfexec/emit_llvm_{direct_block_value,qualified_target,typed_target_triple}.out` and `build/os/elfexec/prod_ring3_run.log`.
## 2026-07-12 scoped SimpleOS LLVM header handoff

- Cycle 1 rebuilt the direct `HirBlock.value` fix and passed live HIR and MIR. It then exposed hosted target/datalayout handling in `LlvmTargetTriple.datalayout` after fork/wait ENOSYS.
- Cycle 2 used qualified SimpleOS target matching and removed the ENOSYS calls, while retaining the invalid datalayout receiver failure.
- Cycle 3 scoped the canonical SimpleOS LLVM header through `llvm_ir_builder_set_simpleos_header`; HIR/MIR remain green and the former target/datalayout fault is gone. The next failure is `rt_native_eq` at RIP `0x103537e9` (symbol base `0x10353708`), error 5, CR2 `0x183f6f18`, before `phase=ir-ready`.
- Three-cycle cap reached; QEMU was stopped. Next fresh turn: identify the remaining LLVM translation equality call operating on an erased/invalid value, replace it with a qualified discriminant or typed owner operation, then perform one focused rebuild/run. Do not rerun already-green HIR/MIR checks separately.
- Latest compiler SHA-256 `f5217bf69246a655cbb3499e96072f2265a8a9ab08a0534b434635916aa4ae58`; image `535f26ef60571719455c81cf9e3fc94a8014346fe5ae60327bb64fca984918ca`.
- Evidence: `build/os/elfexec/emit_llvm_scoped_header.out` and `build/os/elfexec/prod_ring3_run.log`.
## 2026-07-12 nonoptional MirLocal equality fix handoff

- Guided Spark disassembly mapped the current live fault exactly: `MirToLlvm.translate_function` loaded `body.locals[local_i]`, then called `rt_native_eq(local, nil)` at `0x102be0d7`; the guest fault at `rt_native_eq+0xe1` (`0x103537e9`) is therefore the impossible nil guard on a nonoptional `[MirLocal]` element.
- Higher-model review confirmed `MirBody.locals: [MirLocal]`. Both identical loops now bind `val local: MirLocal` and delete the impossible `local == nil` branches. No runtime guard, new facade, or feature-local workaround was added.
- Focused rebuild could not produce new runtime evidence this turn: the canonical wrapper first hit an unrelated `core_array` archive compiler segfault, then direct native-build using the existing proven archive remained CPU-bound for several minutes versus the prior ~67-second baseline and was stopped under the runaway/performance guard. The target ELF remains the prior SHA-256 `f5217bf69246a655cbb3499e96072f2265a8a9ab08a0534b434635916aa4ae58`; do not treat it as containing this fix.
- Next fresh turn: retry the single direct native-build when competing compiler workloads are quiet, bake the resulting ELF into the toolchain image, and run one `emit-llvm` filesystem proof. Do not rerun HIR/MIR separately. If green, decode with the recorded base64 envelope, validate with `llvm-as-18`, then continue `llc-object`, `link-object`, and `execute-artifact`.
## 2026-07-12 target-build configuration handoff

- Two retry commands reproduced long CPU-bound compilation because they used the pinned worktree's stage3 compiler and omitted or selected the wrong cache. This was command drift, not evidence that the two-line `MirLocal` fix caused a compiler regression.
- Guided small-model audit recovered the proven producer contract from the artifact worktree: compiler `/home/ormastes/dev/pub/simple/build/worktrees/simpleos-filesystem-goal/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, backend `cranelift`, one writer/thread, cache `/home/ormastes/dev/pub/simple/build/worktrees/simpleos-filesystem-goal/build/bootstrap/native_cache_simpleos_fs`. The cache contains the prior target closure; preserve it and let only the changed owner module miss.
- Three build attempts were consumed this turn (canonical wrapper archive segfault, uncached stage3 build, wrong-cache stage3 build). All were stopped without overwriting the target ELF; SHA remains `f5217bf69246a655cbb3499e96072f2265a8a9ab08a0534b434635916aa4ae58` and does not contain the fix.
- Next fresh turn must use the recovered stage2/Cranelift/one-thread/absolute-cache contract once, after unrelated Rust builds are quiet. Do not clean caches, increase writers, rerun the Simple-core archive wrapper, or repeat HIR/MIR separately.
- Exact build command: `SIMPLE_SIMPLE_CORE_PATH=build/os/simple-core-simpleos/libsimple_runtime.a SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 /home/ormastes/dev/pub/simple/build/worktrees/simpleos-filesystem-goal/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build --source src/compiler --source src/lib --source src/app --backend cranelift --runtime-bundle simple-core --entry-closure --entry src/app/simpleos_tool/main.spl --target x86_64-unknown-simpleos --threads 1 --cache-dir /home/ormastes/dev/pub/simple/build/worktrees/simpleos-filesystem-goal/build/bootstrap/native_cache_simpleos_fs -o bin/release/x86_64-unknown-simpleos/simple`.
## 2026-07-12 MirType-to-text handoff

- The recovered stage2/Cranelift/one-writer cache contract converged. Cycle 1 built 61 modules/556 cached, embedded the compiler, and proved HIR/MIR live before moving the fault from the deleted `MirLocal == nil` guard to `llvm_type_text(ty: MirType)`'s impossible `ty == nil` call.
- Cycle 2 deleted that guard. Spark mapped the next live fault exactly to `core_codegen.spl`'s legitimate `llvm_ty == "ptr"`: `llvm_type_text` had used bare variants and an implicit match result. The owner now binds `MirTypeKind`, uses qualified variants, and explicitly returns text from every arm.
- Cycle 3 rebuilt 3 modules/614 cached and again proved HIR/MIR, but the same first `llvm_ty == "ptr"` comparison faults in `rt_native_eq+0xe1` (`RIP 0x555ca9`, CR2 `0x183f6f18`). Disassembly proves the returned value is malformed after its untyped local handoff, not that text equality itself is invalid.
- Higher-model review rejected duplicating pointer/bool classification. The minimal pending fix is applied but unbuilt: `val llvm_ty: text = self.llvm_type_text(local.type_)`. Only replace text classification with a qualified `local.type_.kind` match if this explicit owner still fails in a fresh turn.
- Three live cycles reached; QEMU was stopped after each fault. Latest tested compiler SHA-256 `e7bcfbeb7b144c85697cb840520c71f709095a5fa823f1430c46f60370239466`; image `aa37ab6cf72bfa49290a7e43941c298d77d4e4d61fca84650c59f0afc000fc92`. Neither contains the final `llvm_ty: text` annotation.
- Next fresh turn: use the same proven cached build command once, bake a new image, and run emit-LLVM. Require IR-ready/post-write/dump/exit evidence before decoding; do not rerun separate HIR/MIR checks.
## 2026-07-13 LLVM type classification and return-metadata handoff

- Cycle 1 proved `val llvm_ty: text` alone does not repair the returned-text equality boundary: the guest retained the exact `llvm_ty == "ptr"` `rt_native_eq+0xe1` fault. This ruled out simple untyped-local erasure.
- Cycle 2 replaced derived-text pointer/bool classification with a qualified match on the owning `local.type_.kind`. HIR/MIR remained green and execution advanced to `remember_function_return_type(ret_ty: text)`'s impossible `ret_ty == nil` call.
- Cycle 3 typed the `ret_ty` producer, removed nonoptional `ret_ty == nil` and sibling `name == nil` clauses, and advanced to the same helper's remaining `ret_ty == "nil"` comparison (`RIP 0x556669`, `rt_native_eq+0xe1`, CR2 `0x183f6f18`). The exhaustive `llvm_type_text(MirType)` owner can return only nonempty concrete LLVM type spellings, so the entire redundant return-type validation guard is now deleted but unbuilt.
- Three live cycles reached; QEMU was stopped after each exact fault. Latest tested compiler SHA-256 `3cdce70b7c30a5b007ffb32c6620b1e5a4a95a91ff4a69c5cbe65c91c2bade54`; image `03d5a2f3df9a75acab15844dcc4a9c4d4a62cfd874adc410804fe8b599980c69`. Neither contains the final guard deletion.
- Next fresh turn: rebuild with the proven cached command, embed once, and run emit-LLVM. If the next fault is `name == ""` in `remember_function_param_types`, map it before changing it; unlike `ret_ty`, it is not yet disproven by live evidence. Do not add runtime guards or duplicate type mapping.
## 2026-07-13 optional presence lowering blocker

- Cycle 1 rebuilt the deleted return-type guard and advanced to `mark_instruction_dest_defined`'s `LocalId?` `Some/nil` match. It was replaced with positive `.?' plus typed unwrap.
- The first rebuild retry hit ENOSPC. Only superseded, reproducible filesystem-toolchain images from this lane were deleted; this recovered about 11 GiB. No source or unrelated agent artifacts were removed.
- Cycle 2 rebuilt successfully and advanced to `translate_terminator`'s `MirOperand?` `Some/nil` match. It was replaced with positive `.?' plus typed unwrap and the existing default-return else path.
- Cycle 3 proved `.?' itself is currently broken in the stage2/Cranelift target: generated code calls `rt_is_some(value)` but on the false path still calls `rt_native_eq(value, nil)`. The live absent Ret value faults at `rt_native_eq+0xe1`, RIP `0x556589`, CR2 `0x183f6f18`.
- A backend-local raw `rt_is_some` extern was rejected under the runtime-boundary rule. The owner bug is recorded in `doc/08_tracking/bug/pure_simple_bootstrap_nil_lowering_fix_request_2026-07-07.md`: optional presence lowering must branch on the predicate result without adding generic nil equality, with a focused generated-code regression.
- Latest tested compiler SHA-256 `38dab594f3d82f2745e6d30765fee49468012a7d5c56d855a2a7b5a096da1355`; image `7e18aa0d8f6518c0bef9ec62aab6376d45f22fa6c52e0836dce459acd0bb544b`.
- Three live cycles reached. Next fresh turn: locate and fix the Cranelift optional-presence lowering owner, run its smallest IR/machine-code regression once, then rebuild the same filesystem compiler and resume emit-LLVM. Do not add a translator-local runtime shortcut.
## 2026-07-13 optional-presence owner fix and bootstrap evidence

- Guided audits identified the Rust owner at `src/compiler_rust/compiler/src/hir/lower/expr/control.rs::lower_exists_check`: it manufactured `Binary(NotEq, expr, Nil)`, which MIR dispatches through `rt_native_neq`/`rt_native_eq`. It now emits the existing `rt_is_some` builtin directly.
- Added focused HIR-shape regression `test_exists_check_uses_presence_predicate_without_nil_equality`; focused Cargo evidence passed 1/1 and explicitly excludes `NotEq` and `Nil`.
- Aligned the pure-Simple MIR `ExistsCheck` owner to emit a direct `rt_is_some` call returning bool instead of passing the optional base through.
- Isolated one-writer full bootstrap passed: patched Rust seed/runtime rebuilt, stage2 SHA-256 `615e8eed9a14b512cf9b312a8e6ba1b3d562fca93c14ecf74dc021af631e4c00`, stage3 SHA-256 `f8d59f246a6bc3f8ae4b68b2edecda3356b02cc87161566a02dc13a0a9603c73`.
- Patched stage2 cold-built the 617-module SimpleOS compiler with zero failures. Target ELF SHA-256 `5df5d57c8680fc8808a530d159598ea88f1e756a68b33c9dee6f47eecc2349fa`; image `ecf2d80c15f4f08ad249e200433efa41900363424e4b91c1dcb8c9e558a3dbde`.
- Live emit-LLVM still faults after HIR/MIR at `rt_native_eq+0xe1`, RIP `0x103543b9`, CR2 `0x183f6f18`. Disassembly of `translate_terminator` still shows an `rt_is_some` call followed by a false-path `rt_native_eq(value, nil)`, so the direct HIR builtin fix alone did not remove the fallback in generated native code.
- Next fresh turn: finish mapping the remaining fallback to its exact Rust codegen/truthiness owner before editing. Do not repeat the successful bootstrap or add a backend-local runtime extern.
- Final Spark disassembly narrows the remaining owner to pure-Simple `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` around line 790 (`if value.?:` before typed unwrap). In the exact target ELF, `MirLowering.lower_expr` contains generated `rt_native_neq` calls but no reference to `rt_is_some`; the pure-Simple mirror change was not incorporated into that lower-expression path. Next run must prove the rebuilt `lower_expr` references `rt_is_some` before another QEMU cycle.

## 2026-07-13 shared is_some lowering and third live cycle

- Guided Spark review identified the minimal shared owner in `MirLowering.lower_method_call`: zero-argument `is_some()` now lowers the receiver once and emits the existing typed `rt_is_some` builtin returning `MirType.bool()`. Higher-model review accepted this over a runtime shim or another caller-local workaround.
- The cached target rebuild passed with 3 compiled, 614 cached, 0 failed. Target ELF SHA-256 is `76067f4cd46c4c598342005d288319743e6dd40e663372be89fa9d82febfa95c`; canonical rebuilt image SHA-256 is `5752be7dd6d7252806a74e04df4d756f03f53f3347cbde2e3f12452ee6d0e23c`.
- The third live `emit-llvm` cycle again proved filesystem load plus HIR and MIR, then faulted at `rt_native_eq+0xe1` (`RIP 0x103546d9`, `CR2 0x183f6f18`) before IR-ready. QEMU timed out only because the recovered fault handler returned to a stopped user task; the wrapper correctly failed.
- Root cause of the unchanged generated path: the target compiler was rebuilt by the previously bootstrapped stage2. The new pure-Simple lowering code is present inside the target compiler for compiling later inputs, but that old stage2 necessarily compiled `translate_terminator` itself with the old optional/method lowering. A fresh isolated bootstrap is required before rebuilding the target; otherwise source edits to the self-hosted compiler cannot change its own machine-code call path.
- Three-cycle live cap reached. Do not run QEMU again this turn. Next fresh turn: bootstrap the pure-Simple owner change once, rebuild the target with that new stage2, require static evidence that `translate_terminator` no longer contains the fallback equality path, then spend one live cycle.

## 2026-07-13 bootstrapped is_some live result

- Fresh isolated one-writer bootstrap passed. New stage2 SHA-256 is `1e1687ab27c8d37a5bdc31e0e4e436c6f016a7fc2e6ded00496ad4e017bcf743`; stage3 SHA-256 is `398103ab6e60c955e51949d578ce0c844ae2ca85ce269e6ec3bbcba5ea103759`.
- The new stage2 cold-built all 617 SimpleOS target modules with zero failures. Target ELF SHA-256 is `8ca3a9e8e2c8494d89846c541a25040e6dccc5cad33b565af0a88db6e2799dd6`; image SHA-256 is `312e341c1ac4fda3c02646ae1a5abbf3c1146958453f920cb408b36528665440`.
- Live filesystem execution again passed load, CPL3, HIR, and MIR, then faulted at `rt_native_eq+0xe1` (`RIP 0x103546b9`, `CR2 0x183f6f18`). This disproves the hypothesis that only the stale stage2 kept the fallback alive.
- Higher-model review rejected the sidecar static gate because the previously live-failing ELF also passed it; the Option wrapper call itself is clean, so the fault is a later equality.
- Source tracing found the immediate next operation in `translate_terminator`: `get_operand_type(operand: MirOperand) -> text` was assigned to an inferred `maybe_ret_ty` and compared with `nil`, despite its nonoptional return type. The pending minimal owner fix binds the result directly as `text` and removes the impossible nil equality. No runtime shim or duplicated type classifier was added.
- Live cap reached. Next fresh turn: bootstrap this one-line translator fix, cached-rebuild the target, and run one live emit-LLVM cycle. Do not rerun the clean Option wrapper static gate or separate HIR/MIR checks.

## 2026-07-13 nonoptional operand-type live result

- Isolated one-writer bootstrap of the direct `get_operand_type` text binding passed. Stage2 SHA-256 is `1f9419085c461ad63168fa3b9f55f8e909242f571e01b02f5a5f7fbae70bc565`; stage3 remains `398103ab6e60c955e51949d578ce0c844ae2ca85ce269e6ec3bbcba5ea103759`.
- Cold SimpleOS target build passed 617 compiled, 0 failed. It took 579.7 seconds versus the prior 345.6-second compile under host contention; no semantic failure was observed, but retain this as a performance-regression signal if repeated on a quiet host.
- Target ELF SHA-256 is `5c4034e07e099dde2cc64bdbbfc5375aca482fcebba21af577d0f71062755102`; image SHA-256 is `56ff4394b7e334a34f3bee7ee26f698aa915b10956eaf2817a6a7de749421457`.
- Live filesystem execution again passed load, CPL3, HIR, and MIR, then faulted at `rt_native_eq+0xe1` (`RIP 0x103544b9`, `CR2 0x183f6f18`). The removed local `maybe_ret_ty == nil` guard was not the final bad equality.
- Guided sidecar audit, accepted by higher-model review only after this live result, identified the next shared owner: every normal Ret immediately passes through `valid_llvm_type(ty: text)`, which still compared its nonoptional text parameter with `nil`. The pending minimal fix removes only `ty == nil` and retains the empty-string and literal-`"nil"` fallbacks.
- One live cycle consumed; QEMU stopped. Next fresh turn: bootstrap the shared `valid_llvm_type` fix, rebuild, and run one live emit-LLVM cycle. Do not stack the sidecar's lower-ranked `get_local_type` or `translate_const` cleanups without new evidence.

## 2026-07-13 valid LLVM type live result and diagnostic handoff

- Isolated bootstrap passed with stage2 SHA-256 `c3265f660097406ce98970dd211407b33700538dadd9de459256a628109eb045`; stage3 remained `398103ab6e60c955e51949d578ce0c844ae2ca85ce269e6ec3bbcba5ea103759`.
- Higher-model review accepted the sidecar cache audit: native-build cache scope and freshness omit compiler identity, so reusing the preceding target cache after a compiler semantic change is unsafe. A fresh cache was used; the concrete defect is recorded at `doc/08_tracking/bug/native_build_cache_omits_compiler_identity_2026-07-13.md`.
- Cold target build passed 617 compiled, 0 failed, but took 633.6 seconds compile plus 62.0 seconds link. Target ELF SHA-256 is `057ed4dd67ea8050a31c522c481e6e310c5c48b7c71733eab64c50895813357c`; image SHA-256 is `81841df67cba240b8d49addfccc32bdba2e55cd690bea7b7d351b428817a2abc`.
- Live filesystem execution again passed load, CPL3, HIR, and MIR, then faulted at `rt_native_eq+0xe1` (`RIP 0x103544e9`, `CR2 0x183f6f18`). Removing `ty == nil` from shared `valid_llvm_type(text)` did not move the failure.
- Repeated source-order deletion is now rejected. The focused guest entry pending change sets the existing `SIMPLE_BOOTSTRAP_DEBUG=1` switch, enabling already-present `MirToLlvm` function/phase markers. Because only `src/app/simpleos_tool/main.spl` changes and the current cache was produced by the same compiler, the next target rebuild may safely reuse this exact cache and should miss only the focused entry module.
- One live cycle consumed. Next fresh turn: cached-rebuild the diagnostic entry, run one live emit-LLVM cycle, use the last emitted translator marker to identify the exact operation, then remove the temporary debug env setting after the owner fix is proven.

## 2026-07-13 exact third-local type-mapping localization

- Same-compiler diagnostic rebuild correctly reused the cache: first pass 2 compiled/615 cached, then trace refinements 3 compiled/614 cached. No stale compiler-object cache was crossed.
- Setting the existing `SIMPLE_BOOTSTRAP_DEBUG=1` exposed that it changes translation semantics: the guest took the bootstrap-global registry path and faulted at `bootstrap_mir_function_count+0x18` (`CR2=0x8`). This separate defect is recorded at `doc/08_tracking/bug/mir_to_llvm_bootstrap_debug_changes_translation_semantics_2026-07-13.md`.
- Higher-model review separated tracing from semantics with the temporary `SIMPLEOS_TRANSLATE_TRACE` flag. The focused guest entry enables it; the normal `bootstrap_debug` branch remains false.
- Real-path trace ELF SHA-256 was `10d29a6aae88250fb847bad009dcff81cc286a3fd9c8cefdb7fc8c0b20e8860f`; image SHA-256 was `4342e17a721e2a29e88ef3fdb199e9ea88948c82943a4ee9d47fa16ed6221b90`. It localized the crash to `translate_function(__simple_main)` after `function:start` and before `function:locals`.
- Final fine trace ELF SHA-256 is `6c38ec4a8cae0dea0e71366eb091503a9b59f13ace9a8fe72fccf29264c4fc92`; image SHA-256 is `c5cdd9b5ec3732d8f314f51c35315b9bc0fd9aa97a51409f1b8a8a86238d9615`.
- The first two `__simple_main` locals completed load, `llvm_type_text`, id extraction, map insertion, type-kind classification, local-kind classification, and loop advance. The third local printed `local:type` and then faulted inside `llvm_type_text(local.type_)` at `rt_native_eq+0xe1` (`RIP 0x10355c89`, `CR2 0x183f6f18`) before `local:id`.
- Three live cycles reached. Do not run QEMU again this turn. Next fresh turn: identify the third MIR local and its `MirTypeKind` from host-side MIR/source construction, then fix the producing representation or the exact type-match owner. Do not delete another nil/equality guard by source order. Remove temporary trace markers and `SIMPLEOS_TRANSLATE_TRACE` after the owner fix is proven.

## 2026-07-13 discriminant equality root cause

- Guided source audit proved `body.locals[2]` is the `LocalKind.Temp` / `MirTypeKind.Unit` placeholder produced by `lower_bootstrap_print_call`; local order is Return/I64, print string/Opaque, print result/Unit, return literal/I64, return placeholder/Unit. Higher-model review accepted the source chain after the live index trace matched it exactly.
- Machine-code review proved Unit construction is valid. `llvm_type_text` calls `rt_enum_check_discriminant(value, expected_hash)` for match arms. That helper called `rt_enum_discriminant`, then generic `rt_native_eq` on the two integer hashes.
- Unit's expected hash is `0x183f6f19`. `rt_native_eq` treats odd integers above `0x1000` as tagged heap handles, masks the low bits, and dereferences `0x183f6f18`, exactly matching every live `CR2`. This is the complete causal chain for the recurring fault.
- Pending shared owner fix is in `src/runtime/simple_core/core_values.spl`: `rt_enum_check_discriminant` and the same unsafe fixed-discriminant comparison in `rt_is_none` now use numeric `<`/`>` and accept equality only when neither relation holds. No translator-local workaround or new runtime alias was added.
- runtime_need: compare raw integer enum discriminants without tagged-value heuristics.
- facade_checked: existing Simple-core `rt_enum_discriminant` owner and hosted C runtime implementations, which already use numeric equality.
- chosen_path: `runtime-owned-change` in the existing Simple-core ABI implementation.
- rejected_shortcuts: translator Unit special case, malformed-local substitution, new raw extern, `rt_native_eq` pointer heuristics, or deleting additional source guards.
- Concrete bug and regression contract: `doc/08_tracking/bug/simple_core_discriminant_equality_uses_tagged_value_compare_2026-07-13.md`.
- Next fresh turn: rebuild the Simple-core archive once, relink the cached target compiler, statically prove `rt_enum_check_discriminant` no longer calls/references `rt_native_eq`, then run one live emit-LLVM cycle. Remove temporary trace markers after the owner fix advances past the third local.

## 2026-07-13 discriminant runtime fix live proof

- Rebuilt Simple-core archive SHA-256 `1d81411ccf6f99fce6a06af289134bb8866da63a3b794ad4c436baf6a5f2208f`, installed it in the SimpleOS sysroot, and relinked the target compiler SHA-256 `d6245954c4f7c1049408b92d5b76a14d0691d6701499a4410fb28cf05a20aa0f`.
- Static higher-model gate passed for the linked ELF: `rt_enum_check_discriminant` calls `rt_enum_discriminant` exactly once, contains numeric compare/branch instructions, and does not reference `rt_native_eq`; the `rt_is_none` compatibility closure also contains no `rt_native_eq` reference.
- Live filesystem `emit-llvm` loaded `/HELLO.SPL`, reached CPL3, completed HIR and MIR, and processed all six `__simple_main` locals. This proves the former Unit-local discriminant crash is fixed.
- The same bounded live cycle exposed the next independent fault after `function:started __simple_main`, during LLVM function-body emission: user RIP `0x10352539`, CR2 `0x0`, page-fault error `0x5`. The wrapper timed out with rc 124 after the recovered task stopped, so IR was not written.
- Removed the temporary `SIMPLEOS_TRANSLATE_TRACE` guest setting and fine-grained translator markers after proof. The existing `SIMPLE_BOOTSTRAP_DEBUG` diagnostics remain unchanged.
- Next fresh turn: map RIP `0x10352539` to the linked compiler symbol/instruction and identify the exact body-emission owner before editing. Do not rerun the discriminant gate or repeat this live cycle.

## 2026-07-13 strict hosted stage2 runtime decision

- runtime_need: strict `bootstrap_main` linking reaches legacy filesystem ABI names `rt_path_parent` and `rt_mkdir_p`, but `libsimple_native_all.a` exposes only the equivalent owner functions `rt_path_dirname` and `rt_dir_create_all`.
- facade_checked: `runtime::value::sffi::file_io::{path,directory}` already owns the matching pointer/length implementations and behavior.
- chosen_path: add ABI-compatible owner aliases that delegate to those existing functions and re-export them from `file_io`; no new implementation or cache is introduced.
- rejected_shortcuts: weak linker stubs, ignored unresolved symbols, caller-local wrappers, or a parallel filesystem implementation.
- Strict cycle 1 removed the targeted `danger`, `rt_path_parent`, and `rt_mkdir_p` failures, then failed only on `ExactSizeIterator.is_empty` from the newly split Lean MIR translator. The local array already exposes `len`; the call now uses `keys.len() == 0` and avoids retaining an unmaterialized default trait method.
- Strict cycle 2 advanced past the Lean failure, then linked `CompilerBackendImpl.process_module` calls authored as `CompiledModule.cleanup()` to the unrelated `TieredJitManager.cleanup()`, retaining missing interpreter-only `rt_jit_cleanup`. Relocations in `/tmp/.tmpy70sui/mod_308.o` prove the wrong binding. The intended codegen method and all eight callers now use the unique name `release_codegen_module`; no runtime stub was added.
- Guided review found the final two `driver_pipeline` callers only after strict cycle 3 had started. That run was aborted, the callers were updated, and verification stopped at the mandatory three-cycle cap. A fresh session must run one strict staged bootstrap before target/QEMU/server work or GitHub push.

## 2026-07-13 fresh strict bootstrap result

- The single fresh one-writer strict bootstrap failed closed with exit 2; no seed fallback was accepted. Stage2 linked all prior cleanup/runtime fixes and stopped only at undefined default trait method `Len.is_empty` from `SdnBackendImpl.process_module`; stage3 was unavailable as a consequence.
- The SDN collection check now uses its existing `len()` surface. The compiler-wide default-method retention defect is recorded in `doc/08_tracking/bug/bootstrap_default_len_is_empty_not_materialized_2026-07-13.md` rather than hidden by a runtime stub.
- This turn's strict-bootstrap allowance is consumed. Next fresh turn must run one strict staged bootstrap; only an exit-0 stage2/stage3 pair may produce the SimpleOS target compiler or QEMU evidence.

## 2026-07-13 strict stage3 full-closure result

- The next single strict run produced a cached stage2 but stage3 recompiled the 616-file closure and failed closed on 50 files; wrapper exit was 2 and no seed fallback is accepted. The stage2 artifact has 62 uppercase weak definitions, so it is not target-build evidence.
- The grouped failures are recorded in `doc/08_tracking/bug/strict_stage3_selfhost_body_failures_2026-07-13.md`. The cache-wide fingerprint now includes `stub_fallback=forbidden`, preventing old stub-permitting objects from passing a later strict stage2 link.
- Relocation review found reachable array emptiness calls in `NoteSdnMetadata` misbound to `Span.is_empty`, plus Lean text emptiness misbound to `List.is_empty`; both now use their existing `len()` surface. The shared receiver-method resolution defect remains tracked by the cleanup bug.
- The Clang filesystem execution wrapper now pins `execute-artifact`, validates the exact Clang output and exit 42 inside the shared production runner, rejects multiline values, treats option-shaped output as literal text, and leaves canonical Simple profiles immutable.
- No target compiler or QEMU cycle is authorized until a fresh-cache strict stage2/stage3 run exits 0 with no weak/stub evidence.
- Focused closure regression: `use lib.shared.{value}` from `src/app/main.spl` incorrectly includes both `src/lib/shared.spl` and `src/app/lib/shared.spl`. A one-resolver experiment still chose the relative candidate and was removed after the third focused cycle. The next owner fix must make recognized top-level project namespaces absolute per import, while preserving relative local-module resolution.

## 2026-07-13 canonical lib namespace and clean strict result

- `lib.*` now resolves as the canonical project `src/lib` namespace in both `ModuleResolver` and entry-closure filesystem fallback. The existing shared-fan-in fixture includes a colliding `src/app/lib/shared.spl`; focused Rust evidence passed exactly once: `1 passed; 0 failed`.
- A full seed rebuild and clean no-stub stage2 succeeded. Stage3 still failed closed with wrapper exit 2 and 53 critical files, including GPU, benchmarks, MCP experiment, legacy interpreter, DAP, TCP, compression, and unrelated networking. No stage3 artifact or target/QEMU evidence is accepted.
- Higher-model review confirmed the remaining owner: entry discovery unions answers from every resolver despite its `first hit wins` contract, then its filesystem fallback adds every matching root independently. Next fresh turn must make resolution atomic per import (first resolver success; fallback only after all miss; first fallback success), add a collision matrix gate, then spend one strict bootstrap cycle.

## 2026-07-13 atomic discovery and terminal-hang result

- Entry discovery now resolves each import atomically and runs one deterministic filesystem fallback only after every resolver misses. The existing colliding `src/app/lib/shared.spl` regression passed with `1 passed; 0 failed`.
- Fresh strict cycle5 stage2 passed: 603 compiled, 0 failed, with a 21,922 KB binary. Stage3 failed on 144 files, so no stage3, target, QEMU, web, DB, LLVM, or Clang evidence is accepted.
- The wrapper then incorrectly entered seed-fallback stage4. Its orphaned worker consumed one core and about 1.16 GiB RSS for 83 minutes, stopped producing files/logs, and produced no binary. Higher-model review accepted the Spark process/log diagnosis: this was a nonconverging compiler worker after an already-failed strict stage, not blocked terminal I/O.
- The cycle5 timeout/worker was terminated. `bootstrap-from-scratch.sh` now treats stage2/stage3 failure as fatal when the caller sets `SIMPLE_NO_STUB_FALLBACK=1`, refusing the invalid seed fallback before stage4. `sh -n` and `check-bootstrap-portability.shs` pass.
- Remaining owner failure is strict stage3 compilation, beginning with receiver-method ambiguity and Cranelift/body failures. Do not rerun bootstrap this turn; the three-cycle cap is consumed.

## 2026-07-13 bootstrap closure hub pruning

- Higher-model review accepted the Spark closure audit: reachable driver leaf modules imported the broad `compiler.driver` facade, and `smf_getter.spl` imported the broad `app.io` facade, whose initializer fans into CLI, JIT, test, CUDA, and Vulkan modules.
- Bootstrap and driver leaf imports now name the concrete `compiler.driver.driver` owner; `smf_getter.spl` now names `std.nogc_sync_mut.io.file_ops` directly. No new facade or parallel I/O path was added.
- Focused entry-closure evidence passes: `test_bootstrap_entry_closure_avoids_driver_package_hub` ran 1 test with 1 pass and proves the driver package hub, `app/llm_caret`, and `app/leak_finder` are absent.
- No further strict bootstrap is allowed this turn. The next fresh run must trace the actual stage3 discovery set if unrelated application files recur; do not repair their bodies as a substitute for fixing closure drift.

## 2026-07-13 strict stage3, filesystem version PASS, interpreter handoff

- Guided Spark audits and higher-model review found the stage3 runaway cause: native `rt_native_build` discarded the supplied RuntimeValue argv and read Rust process args, which are empty when linked under the C entrypoint. Always extracting the supplied argv restored `--entry-closure`; strict cycle8 passed with 482 modules, zero failures, stage2 SHA-256 `35aa0cba315acb0b73c1a032b9c6d88734b77ca7c5bff27ee8cc4ac282b18002`, and stage3 `1d1ac5ac1a7d6f7d2d02eb7b64d87a84650f7338de2803998f9bf4d8b81cdccc`.
- The focused target wrapper now defaults to Cranelift (LLVM remains an explicit override). Missing Simple-core `copy_mem` and `rt_string_chars` owners were implemented; the x86_64 RuntimeValue list copy uses an explicit eight-byte slot count. Final target ELF SHA-256 is `9968a232615fbb06747a59093e01baecf2d4fcf74b8dab00b59fb453c1278f75`: static ELF64 EXEC, entry/first LOAD `0x10000000`, no PT_INTERP, no strong undefineds, and no defined uppercase-W fallback functions.
- The manual FAT32 builder now emits physical raw and SMF Simple role paths plus a VFAT long-name `/SYS/SIMPLETOOL.SDN` manifest with `runtime_source = "simpleos-filesystem"`. Each alias owns an independent FAT chain. Current image SHA-256 is `e9e8ae65a50562c52d3cb5ae335b9e5a3c8ac4c5e185095b99b70d824e6ff43e`; `fsck.fat -n -l` resolves all required long paths. Pre-existing missing dot/FSINFO/backup-sector warnings remain outside this lane.
- The production proof now accepts the loader's deliberate returning-spawn contract and lets the wrapper validate the exact child status. Live version profile PASS: FAT/NVMe `/USR/BIN/SIMPLE`, CPL3 entry, exact `Simple v1.0.0-beta`, syscall status 0, kernel resume rc 0, QEMU rc 3, and `[prod-ring3] PASS`.
- Interpreter cycle 1 faulted in `ast_count_slots_ensure` because zero-initialized array globals used unsafe `.len()`. Cycle 2 proved the initial facade still compiled to the unsafe intrinsic. The Simple-core `rt_array_len_safe` owner now contains its own validity guard, and decl/lexer slot wrappers route through it; target disassembly proves the guard precedes the offset-8 load.
- Interpreter cycle 3 advanced past those owners and faulted at `rt_string_join+0x3e` (`RIP 0x103983b4`, `CR2=0x8`): that function still calls unsafe `rt_array_len` on a nil array. Three live cycles are consumed. Next fresh turn: change only `rt_string_join` to use the guarded length owner, rebuild archive/sysroot/target/image once, and resume the interpreter profile. Do not rerun the green version profile.
- Emit-LLVM, LLC, LLD, Clang, RV64 web, and RV64 DB gates were not run and remain unclaimed. WebIR/DrawIR refactoring is N/A for this headless native loader/runtime work. Process inspection showed the long final kernel build remained CPU-active under unrelated native-build contention; no owned terminal process was hung or orphaned.

## 2026-07-13 filesystem interpreter PASS and capped compiler handoff

- `rt_string_join` now uses the guarded array-length owner. The next parser fault was traced to lexer text slicing: Simple-core `rt_slice` handled strings but not `[text]`, so it now implements array slicing through the existing array validity/get/push owners. Runtime archive/sysroot SHA-256 is `0a8b08cf3a44fd73fe33c296b8cd84b81a9110c2e68b61c2fe8bfe47f80b5166`.
- Live interpreter proof PASS: real FAT/NVMe `/USR/BIN/SIMPLE` read `/HELLO.SPL` (63 bytes), printed exact `Hello from SimpleOS`, exited status 0, kernel resumed rc 0, QEMU rc 3, and the wrapper printed `[prod-ring3] PASS filesystem Simple ELF executed`. Do not rerun the green version or interpreter profiles.
- Emit cycle 1 reached HIR then exposed lost `HirModule` typing after `unwrap`; explicitly typing `val hir: HirModule` corrected the symbols-field load from offset `+0x08` to `+0x28`.
- Emit cycle 2 reached HIR then exposed an unsafe optional pattern binder in `lower_bootstrap_print_call`; the established positive-presence check plus typed `MirType` unwrap was applied. Static root and Spark review proved the target calls `Option.unwrap`, validates the payload, and only then reads `MirType.kind`.
- Current guest Simple ELF SHA-256 is `982d96f473efec60a06439616ebdd7535dab54f16a3eb2d26a94ab2fda834ecf`; current rebaked FAT image SHA-256 is `98d980c7e63e63ae3402073e9322bc748a72190051a7ef100ac1c141fbf80546`.
- Emit cycle 3 reached both `[simpleos-compile] phase=hir-ok` and `phase=mir-ok`, proving the two fixes, then failed in `mir_opt__mir_opt__var_reassign_analysis__var_reassign_local_id_value` at target address `0x102a7b1c`: a nil/invalid `LocalId` receiver reaches the enum match. QEMU timed out rc 124 and produced no `/HELLO.LL`. The three-cycle cap is exhausted; no fourth emit attempt is permitted this session.
- Toolchain audit found a real static guest Clang at `/home/ormastes/dev/pub/simple/build/os/clang_static/bin/clang_static` and complete relink prerequisites, but no `llc_static` or `lld_static`. The physical FAT still lacks `/USR/BIN/CLANG`, `/USR/BIN/LLC`, and `/USR/BIN/LD.LLD`; LLC/LLD/Clang execution remains unclaimed until the post-MIR owner is fixed and all binaries are staged.
- The terminal hang was an orphaned marker-poll shell whose QEMU had already failed to lock `build/os/fat32-arm64.img`; only that watcher was terminated. Other concurrent builds/sessions were left untouched.
- A strict-stage3 `os build --arch=riscv64` remained CPU-bound near 97% and reached about 5.0 GiB RSS without output or producing `simpleos_riscv64.elf`/stamp in the bounded observation window. It was stopped cleanly. Therefore the RV64 HTTP/DB live gate could not start and remains unclaimed.

## 2026-07-13 post-MIR matcher fixes and bounded emit result

- Guided Spark disassembly plus higher-model review proved `var_reassign_written_local`'s first `Const(dest, _, _)` pattern was lowered as irrefutable: it read the `MirInstKind` enum header as a `LocalId`. The owner now discriminates `Const` numerically before destructuring it; target SHA-256 `6b35ae0aaad3b3c2c2f71f715957833f24ea96141e05161fce681d01a0b63896` statically proves raw `cmp/sete`, guarded `rt_enum_payload -> rt_index_get(0)`, and no header-as-LocalId load.
- The same audit found optional payloads passed through without unwrap in both Ret escape collectors and four optional call destinations. They now use explicit typed `Option.unwrap`; the three bootstrap-print optional results do likewise. Static review passed.
- The final bounded filesystem `emit-llvm` cycle again reached `phase=hir-ok` and `phase=mir-ok`, then advanced to `local_count_index` and faulted at `0x102a793f`, dereferencing offset 8 from a nil `[i64]` array (`CR2=0x8`). QEMU timed out rc 124 and no LLVM IR was produced. No fourth live cycle is permitted this session.
- The next bounded run proved `pages=32768` live but faulted at the identical `local_count_index` PC with identical `CR2=0x8`; heap size is not the root cause, so the 128 MiB change was reverted. `alias_keys` is nil at some live call, but the fault frame does not prove it is the first call or that the fifth constructor failed. Next cycle must add focused optimizer phase/pointer tracing to distinguish initialization from a later tuple/alias update; do not mask nil with safe length or sentinel keys.
- Concrete shared compiler defect remains: a keyword-named multi-field `MirInstKind.Const` pattern can lower irrefutably in native target code. The current guarded owner workaround is correct but allocates a marker per instruction; replace it after fixing the shared matcher and record warm optimizer latency/RSS evidence.
- Correct RV64 routing was identified but not started under two unrelated concurrent native builds: use full `bin/release/simple os build --arch=riscv64` with `SIMPLE_BINARY` pointing to strict stage3. The earlier 5 GiB run directly invoked minimal `bootstrap_main` and was a wrong command shape, not a terminal hang.

## 2026-07-13 optimizer array classification and RV64 CLI result

- Heap experiment cycle 1 rebuilt the kernel with 128 MiB and proved `[spawn] user heap mapped ... pages=32768`, but reproduced exact `local_count_index` RIP `0x102a793f` / `CR2=0x8`. The ineffective heap change was reverted.
- Static review found four real `Option<i64>` representation defects in reassignment analysis; all now use explicit typed unwrap. Target SHA-256 `fe7a5072f95c94b761377eca25cb628ad0521c8a30752c4cd0f3f9135cbdbaf5` proved `rt_enum_payload` before alias/count consumers. Cycle 2 reproduced the same fault, so these fixes are retained but were not the nil-array producer.
- Cycle 3 target SHA-256 `242e306457b79465102db215568f727ed8246d673ddc90c8cf67ad1c536a57bd` added a temporary literal low-value marker inside `local_alias_root`. The marker did not print before the exact same fault, ruling out alias-root as the immediate caller; the marker was removed from source. Three cycles are consumed. Next fresh session must distinguish direct callers `local_count_value`, `local_count_increment`, and `local_alias_set`, preferably by saved caller PC/raw array register or caller-specific literals, then fix only the exact producer.
- The one authorized full-CLI RV64 attempt used the worktree `bin/release/simple`, which fell back to `release/x86_64-unknown-linux-gnu/simple` SHA-256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`. It exited 1 silently in 1.056 seconds before any `[build][riscv64]` marker and produced no ELF/stamp, so HTTP/DB QEMU checks were correctly skipped. Next session must use/stage a known-good full CLI rather than this silent fallback; do not invoke minimal `bootstrap_main`.
- LLVM/Clang staging remains blocked by missing `/HELLO.LL`, `llc_static`, and `lld_static`. Shared Clang remains valid at `/home/ormastes/dev/pub/simple/build/os/clang_static/bin/clang_static` SHA-256 `1af0e604de6759fd64bd521ef7500cd4f831404563b0fefd2afe7994b71f254a`; LLC additionally needs its two tool objects plus `libLLVMMIRParser.a` built before sequential static relink.

## 2026-07-13 optimizer tuple-state fix and runtime handoff

- Caller-specific cycle 1 proved `local_count_value` received a valid array while the later `local_count_increment` saw tagged nil; independent Spark disassembly found no caller-slot write. It also confirmed native `and`/`or` lowering eagerly evaluates both RHS helpers.
- A reviewed call-order workaround rebuilt successfully but cycle 2 reproduced the exact `local_count_index` fault, so ordering was not the owner. Disassembly proved all six initial arrays come from `rt_array_new`, not nil literals.
- Both Spark audits then localized the poison boundary to allocation-backed count/alias tuple updates. The helpers now mutate their persistent arrays in place and return unit. Target SHA-256 `b0a789066c151f7ef71675d233fa1f305301b5cbc4b7f8e57086077c50811386` statically contains no tuple runtime calls in those update helpers.
- Cycle 3 passed the old optimizer PC and exposed a new independent fault in Simple-core `rt_index_get`: RIP `0x10392869`, CR2 `0`, error `0x5`. Its compound string guard computes validity but unconditionally loads the header before branching because logical operators are eager. `/HELLO.LL` remains absent.
- Three live cycles are consumed. Next fresh turn: rewrite only the `rt_index_get` string guard as nested checks, build once, require the header load to be branch-dominated, then run one emit-LLVM profile. Do not rerun the now-resolved optimizer diagnostics or the green version/interpreter profiles.
- Current image SHA-256 is `34d7a2f61ce3575c3513da1266b3ad4aab2ae54669b140cb32ae3cdf88708e30`. LLVM/Clang staging and RV64 HTTP/DB remain unclaimed; WebIR/DrawIR is N/A for this headless runtime path.

## 2026-07-13 `rt_index_get` deletion proof and exact count handle

- Spark review found the unsafe Simple-core string fast path was redundant. It was deleted rather than duplicated with nested guards; the existing dict/array/string fallback already validates before dereference. Runtime/sysroot SHA-256 is `eff65d42dec1ce2824494d657ce00b784cc7a76460226c3ea718b7c8b5de5ab5`; rebuilt target SHA-256 `741dddc20e42bfa2f3246819571adeece640ca12c679cc43c0ab3b019741ffc4` contains no old string-magic fast-path load.
- Live cycle 1 passed the former `rt_index_get` PC but exposed `local_count_index+0x29` again (`RIP 0x102a78b1`, `CR2=8`). A proposed `rt_array_len_safe` lowering was rejected and reverted before completion because it masks invalid optimizer state.
- Cycle 2 used target `0008ab4f24688bb114e90fec1515c39c97d2290ca268626bd32ff7fe3ceccf11` with temporary caller literals. It proved `[var-reassign] count-increment=3`; alias-root receives a valid handle first. Generated code reloads `local_ids` from its constructor-only `rsp+0x180` slot, which has no generated later store.
- Cycle 3 attempted a QEMU hardware watchpoint at the post-constructor instruction. The breakpoint was installed before the user CR3 existed and did not bind across the address-space switch; the same marker/fault reproduced. Temporary probes were removed from source.
- Next fresh turn: launch paused QEMU, continue until serial reports `[spawn] entering user`, then attach/interrupt GDB under the active user CR3, break at analyzer entry/post-store, and watch the concrete `local_ids` slot. Capture the first write or stack displacement before editing. Do not use safe length, sentinels, heap growth, or restore tuple updates.
- Current source includes the reviewed `rt_index_get` deletion and tuple-free optimizer helpers. The on-disk diagnostic target/image still contain temporary marker machine code and therefore are not source-current release evidence. `/HELLO.LL`, LLC/LLD/Clang filesystem execution, and RV64 HTTP/DB remain unclaimed. Three live cycles are consumed; no further QEMU run is permitted this turn.

## 2026-07-14 array call-boundary proof and GitHub sync

- Two bounded active-CR3 GDB attempts confirmed the post-CR3 kernel handoff but user execution breakpoints did not trap reliably across the address-space transition. Static review found no overlapping analyzer stack slot, unbalanced frame, or callee-saved-register defect; those paths were not retried.
- The final source-level checkpoint image used target SHA-256 `599bb392be5c4e88ceb3355e4db6829a2725173fb5ae3aafceb4518f524e1d7e` and FAT image SHA-256 `1dbd044aadbbb311048ff812a5b734821f3a0b33119a378482a6dd25d7fd7358`. Serial printed the hard-coded low-positive branch label `[var-reassign] count-increment=3` and faulted at `local_count_index` (`RIP 0x102a793f`, `CR2=0x8`), but the label did not print the numeric argument.
- Higher-model disassembly review rejected the apparent call-boundary conclusion. The caller compares and reloads the same constructor-only `rsp+0x298` slot into `RDI`; the direct callee preserves `RDI` and passes it to `local_count_index`. There is no intervening store or argument reorder, and all FAT Simple aliases match the retained ELF. Silence from caller-side `eprint` checkpoints is therefore insufficient evidence of a valid handle. Temporary checkpoints are absent from source; the diagnostic binary/image are retained only as non-release evidence.
- The recovery lane rebased onto the concurrent upstream `main` and was pushed linearly to GitHub as `f0240a9e4`. Rebase review preserved upstream `Some(0)` matching and package-export traversal while retaining tuple-free optimizer mutation and atomic import resolution.
- Three live diagnostic cycles are consumed. Do not patch call lowering: the retained ELF already preserves the three arguments statically. Next session must capture the actual caller-slot and callee-entry values with a numeric/global diagnostic that cannot fail silently, then reconcile the contradictory serial evidence before editing an owner. `/HELLO.LL`, filesystem LLC/LLD/Clang execution, and RV64 HTTP/DB remain unclaimed.

## 2026-07-18 current-main recovery and focused parser cap

- The old goal clone was fetched without changing its 103,458-file baseline, but it is 161 commits behind and has 73 mixed dirty paths. It was not rebased, committed, or pushed. A clean isolated `main` checkout was created at `/home/ormastes/dev/pub/simple-simpleos-goal-20260718` from current `origin/main` (`3f577c312de` at checkout time); the old clone remains untouched as recovery evidence.
- Guided lower-model audits plus highest-model review agree that AC-1/2 and AC-4/5/6 remain current-live unclaimed. AC-3 history recovery is satisfied; AC-7 remains source-only. Retained July 11 HTTP/DB logs and older filesystem images are stale and are not promoted to current proof.
- The contextual `loop` owner now treats `loop` as an identifier only before member access, retains statement-form `loop:`, and still rejects unsupported loop expressions. The former placeholder contextual-keyword unit spec now has three real assertions covering those branches; no test was deleted.
- Focused native cycle 1 failed before the spec on the reverted invalid nested quote in `c_type_mapper.spl`; the canonical single-quoted separator was restored. Cycle 2 advanced and found the same parse-unsafe separator in the SDoctest summary owner; it was restored without changing behavior. Cycle 3 advanced to a distinct current test-runner semantic blocker: `method 'trim_start' not found on value of type str in nested call context`. The three-cycle cap is exhausted; no fourth native run or bootstrap is allowed in this session.
- An external isolated producer in `/home/ormastes/dev/wt_s58` remains CPU-active building a full CLI; its output is absent. Do not duplicate it. If it finishes, first run the canonical redeploy admission gate once. No target/image/QEMU command is allowed before an admitted candidate exists.
- GitHub fetch completed and the file-count guard stayed stable. Push is withheld because the focused native spec and production verify have not passed; the isolated source changes remain uncommitted.

## 2026-07-18 native preflight continuation and temp-dir handoff

- Highest-model review accepted the minimal documented method-chain rewrite in the three test-runner owners reached by native execution. The new focused cycle advanced past the prior `trim_start` semantic failure.
- Cycle 1 then failed because the older LLVM-enabled seed did not register current `rt_process_run_bounded`. No shim or seed rebuild was added. A guided existing-artifact audit found the current seed `/home/ormastes/dev/wt_q_crossmodule/src/compiler_rust/target/bootstrap/simple`, SHA-256 `a61856ae1a5a6398c5e8b7eff33d663890dc0910db7c52652bd3058d41b05c22`, with the canonical runtime and interpreter registration.
- Cycle 2 reused that seed and failed closed because the isolated checkout intentionally has no `bin/simple`; no source defect was inferred. Cycle 3 supplied the documented `SIMPLE_BINARY`, `SIMPLE_RUNTIME`, and `SIMPLE_BUILD_COMPILER` paths and advanced to the exact failure `nil/spipe_wrapped_test_01_unit_compiler_parser_lexer_contextual_keywords_spec.spl`.
- Root cause is in the shared `std.env.platform.get_temp_dir` owners: unset `env_get("TMPDIR"|"TMP"|"TEMP")` returns nil, but each branch checks only `tmp != ""` and therefore returns nil before the OS fallback. The sibling test-runner temp helpers correctly require both nonempty and nonnil. Next fresh turn must add the missing nil checks in both `nogc_sync_mut` and `nogc_async_mut` owners, then run `test/01_unit/app/test_runner_spipe_expect_helper_spec.spl` once before retrying the contextual parser spec.
- Three focused native cycles are consumed; no fourth retry or bootstrap is allowed this turn. The external `/home/ormastes/dev/wt_s58` full-CLI producer remains healthy and CPU-active, and its candidate output is still absent.

## 2026-07-18 temp fallback proof and platform nil handoff

- Both `nogc_sync_mut` and `nogc_async_mut` `std.env.platform.get_temp_dir` owners now require a temp environment value to be both nonempty and nonnil before returning it. No caller-local fallback was added.
- The focused SPipe helper cycle with `TMPDIR`, `TMP`, and `TEMP` unset advanced through `/tmp` wrapper creation. Its first run exposed outer-string interpolation of intended generated `{name}`/`{reason}`/`{message}`/`{deps}` placeholders; all were escaped at the single inline-helper owner. The documented remaining method chains in the two touched runner helpers were split into typed intermediate values.
- The second helper run produced `1 example, 0 failures`, proving wrapper creation/read/rewrite/delete, but the bootstrap-seed outer runner still returned an inconsistent aggregate `Passed: 1, Failed: 1`. This remains diagnostic evidence, not a production PASS.
- The final native contextual parser cycle advanced past the prior `nil/spipe_wrapped_...` path and exposed the next shared platform owner defect: `semantic: method lower not found on type nil`. Both runtime-family `detect_os` implementations call `.lower()` on `env_get("OSTYPE")` without normalizing nil; the `OS`, `HOSTTYPE`, `MACHTYPE`, and Windows architecture branches have the same unsafe shape.
- Three cycles are consumed. Next fresh turn must normalize those shared platform environment reads once in both family mirrors, run the smallest platform/temp fallback check, then retry the native contextual parser spec. Do not add a test-runner-specific OS fallback.
- The external `/home/ormastes/dev/wt_s58` full-CLI producer remains CPU-active and its output is absent. AC-1/2 and AC-4/5/6 remain unclaimed.

## 2026-07-18 infix-expect lint handoff

- Both shared `std.env.platform` owners now normalize unset OS and architecture variables before calling `lower`; the Windows OS check also uses a documented intermediate rather than a chained method call. The focused native path again reached `/tmp`, so the nil temp/OS fallback defects are no longer the active blocker.
- Guided Spark audits and highest-model review localized two shared SPipe preprocessing defects. `spipe_helpers_used` now recognizes a rewritten `expect ...` inside a scenario body, and `SPIPE005` accepts canonical infix expectations only when the exact `expect ` boundary, a comparison operator, and nonempty operands are present. Regression coverage includes body-only helper injection, canonical acceptance, and an `expectation == true` false-positive guard.
- Focused cycle 1 exposed the old linter rejection. Cycle 2 ran `spipe_quality_lint_spec.spl`: all 18 examples passed, including both new lint cases, but the bootstrap-seed outer runner later invoked a malformed `simple fix` path and returned an inconsistent aggregate failure. Cycle 3 retried the original native contextual parser spec and was rejected before compilation by the bootstrap seed's embedded stale `SPIPE005` implementation; it cannot consume the just-fixed Simple linter source.
- The three-cycle cap is exhausted. Do not add a lint suppression or weaken the assertion. The next fresh turn must wait for an admitted current full CLI, then run the body-helper spec and contextual parser spec once with that CLI. The external `/home/ormastes/dev/wt_s58` producer remains CPU-active and its candidate is absent, so full bootstrap, target/image/QEMU verification, commit, and push remain gated.

## 2026-07-18 ARM64 and RISC-V64 sidecar lanes

- The user added guided ARM64 and RISC-V64 agents. Root review keeps both on the shared `resolve_executable_bytes` / mounted-VFS / existing ELF-spawn interfaces; neither may add a parallel loader or promote task registration as execution.
- ARM64 currently prepares an ELF task but `_fs_exec_spawn_ring3_active` explicitly logs `arm64:no-ring3-handoff` and returns `-16`. Historical EL0 evidence runs canned SVC instructions, not a mounted tool. HTTP/DB wrappers and current AArch64 Simple/LLVM/Clang payloads are absent.
- RISC-V64 has the canonical live HTTP/DB boot-service gate, but filesystem spawn proves only a U-mode handoff frame. It has no RV64 Clang/LLC/LLD image lane and no current filesystem `/usr/bin/simple --version` plus compile/run evidence.
- A retained stage-3 candidate (`7ab3d644...`) failed the canonical redeploy gate `0/11 PASS`: `-c` and `run` commands were unregistered. It is rejected. The active `/home/ormastes/dev/wt_s58` producer remains the only current admission candidate; no architecture build or QEMU run is authorized before it passes.

## 2026-07-18 architecture handoff implementation checkpoint

- ARM64 now has a dedicated ring-3 filesystem-spawn route through the existing `user_entry_bridge`, recorded-handoff probe, and `rt_arm64_enter_recorded_user_live`. PID-returning registration remains separate, the old unconditional `arm64:no-ring3-handoff` branch is gone, and a returning runtime failure maps to `-16`. The current single-launch global handoff is explicitly bounded; concurrent exec requires PID-keyed state before enablement.
- Highest-model review did not promote this to runtime proof: the retained `hello_world.smf` enters at its ELF header, so only a genuinely runnable mounted AArch64 ELF may exercise the live path. The static contract pins the loader -> facade -> probe -> live runtime chain; QEMU evidence remains mandatory.
- RISC-V64 review found the scheduler SATP switch encoded Sv48 while the canonical RV64 paging owner builds Sv39. The shared scheduler owner now uses mode 8/Sv39 and the numbered address-space spec rejects regression to mode 9. Real RV64 filesystem execution remains blocked on a canonical Sv39 user-AS facade, scheduler/trap state install, real `sret` dispatch, and exit-to-kernel continuation.
- No bootstrap or QEMU run was started. The existing full-CLI candidate failed admission, so these architecture changes are unverified source progress and must not be committed or pushed yet.

## 2026-07-18 RV64 Sv39 adapter and producer diagnosis

- The RV64 user-address-space adapter now creates through the existing Sv39 paging owner and maps through a root-parameter form extracted from that owner's existing three-level walk. It no longer routes its RV64 cfg body through the x86-oriented generic VMM create/map functions. Zero roots fail closed; root reclamation stays boot-lifetime until the Sv39 owner has a safe tree walker.
- A numbered static contract isolates the RV64 cfg body and pins the Sv39 owner calls plus absence of the generic create/map calls. Root review replaced its broad `app.io` dependency with the existing `std.io_runtime.file_read` surface. No `sret`, trap scheduler, syscall exit, or QEMU claim was added.
- The external full-CLI producer is CPU-active rather than terminal-blocked: at 1h28m it used about 96% CPU and 20.7 GiB RSS, its 110 MB verbose log was still advancing through new compiler modules, and the output artifact remained absent. It is owned by another session and was not killed or duplicated.
- Focused tests remain gated on a functional admitted CLI. The source-contract diffs are whitespace-clean, but no runtime PASS, commit, or push is claimed.

## 2026-07-18 mounted ARM64 payload and RV64 trap scheduler

- ARM64 no longer uses the kernel-synthesized SVC payload for its live gate. A 4,904-byte static AArch64 ET_EXEC payload at entry `0x400000` prints `[arm64-fs-user] mounted-elf-ok` through syscall 60 and exits through syscall 0. Its host build passed once; SHA-256 is `acb32d7338ef43fac7e137195853e471fbacce6bd1abb80c880b17de16aba8ab`.
- ARM64 disk creation builds/stages that payload as `/FSEXEC.ELF` only when the caller has not supplied `SIMPLEOS_FSEXEC_BINARY`. The QEMU entry now invokes the dedicated ring-3 filesystem spawn and fails if it returns; the acceptance marker list requires the payload nonce, so fixed exit-handler text alone cannot satisfy the gate. This is a one-shot mounted-ELF proof, not yet a general process-exit or compiler argv proof.
- RV64's installed trap runtime can now replace only its Scheduler while preserving IPC and KernelLog state. The behavioral spec rejects pre-install replacement, schedules a nonzero PID, proves GetPid returns that PID with `sepc + 4`, and proves the prior IPC port and log sentinel survive the replacement.
- The current full-CLI output is still absent and its producer remains CPU-active. No Simple test, target build, QEMU run, commit, or push is claimed.

## 2026-07-18 RV64 exit state and ARM argv boundary

- RV64 syscall 0 now uses the existing Scheduler exit owner with `arg0` as the exact exit code and returns the updated Scheduler state. The focused numbered spec schedules a real task and requires `Zombie` plus exit code 37; the existing IPC cases remain intact. Together with the trap-Scheduler replacement, this prepares state for the later saved-frame kernel continuation but does not yet perform `sret`.
- ARM compiler/interpreter argv support cannot safely reuse the generic stack builder as-is: the freestanding ABI may supply raw array handles, `AuxEntry` aggregate arrays hit a known lowering defect, and the direct-load branch currently skips stack mapping. A bounded implementation requires one raw-safe staged ARM stack owner, one raw byte-copy-to-physical bridge, consumption in the ARM process image, and `map_stack` after direct ELF staging.
- The ARM stack implementation sidecar was stopped before editing because that coordinated slice cannot be verified without the admitted CLI and should not be reduced to an unsafe one-line reuse. The one-shot mounted ELF remains valid source progress; `/usr/bin/simple /hello.spl` remains unclaimed.

## 2026-07-18 guided ARM64/RISC-V64 prerequisite checkpoint

- ARM64 now stages one bounded SysV startup frame for argc 1-2, covering both `/FSEXEC.ELF` and `/usr/bin/simple /hello.spl`. It serializes absolute argv pointers, NUL strings, `AT_ENTRY`, and `AT_NULL` without the aggregate aux/result boundary; the direct-load path maps the frame and fails closed on empty metadata or zero/short physical copies. The global staging owner remains intentionally one-shot; concurrent exec requires PID-keyed state.
- The ARM64 mounted payload now resolves through the FAT32 root alias, links all `PT_LOAD` bytes within the existing 1 MiB direct-load arena, and makes Arm64 disk readiness require the payload nonce. These source gates are not QEMU evidence; the payload must be rebuilt once after CLI admission before the target lane runs.
- RISC-V64 audit found that kernel `0x80200000` and old user `0x90000000` both occupied Sv39 VPN2 slot 2. The canonical RV64 userspace link base is now `0x100000000` (slot 4), while new user roots validate and inherit the supervisor-only kernel slot-2 leaf. Missing, non-leaf, or user-accessible kernel entries fail closed.
- The existing 272-byte `Riscv64Context` now has a validated `RV64KRET` continuation helper. Live entry assembly remains paused until focused specs can run; it must reuse that exact frame and the existing trap vector, not add a second jump/context ABI.
- Highest-model review rejected and corrected ARM silent-success copy handling. Workspace `git diff --check` and shell syntax checks for the touched OS scripts pass. No Simple test, target build, QEMU run, commit, or push is claimed.
- The external full-CLI producer remains active at about 97% CPU; at 2h10m its trace log reached 155 MB, RSS reached about 24.7 GiB, and the artifact remained absent. It was not killed or duplicated because it belongs to another active session.

## 2026-07-18 Stage4 mut-parameter parser repair

- The prior traced Stage4 producer failed at `src/compiler/mir_opt/mir_opt/collection_opt_core.spl:470`: speculative snapshot/backtracking parsed `mut` as the parameter name and left `counts` before the closing parenthesis in `count_inst_uses(inst: MirInst, mut counts: Dict<i64, i64>)`.
- The canonical declaration parser now uses one deterministic consuming `(name, is_mut)` helper at both free-function parameter sites. Focused Flat-AST contracts cover the exact producer signature and the legal parameter name `fn keep(mut: i64)`. Executable proof still awaits an admitted current CLI.
- A replacement incremental Stage4 producer was started from `/home/ormastes/dev/wt_s58/build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple` with compiler, parser, and lexer tracing unset. Its local cache is `build/bootstrap-recovery/native_cache`, log is `build/bootstrap-recovery/logs/stage4-native-build.log`, and output is `build/bootstrap-recovery/full/x86_64-unknown-linux-gnu/simple`; candidate production and redeploy admission remain pending.

## 2026-07-18 native arena repair and Stage3 refresh handoff

- The first trace-disabled Stage4 cycle passed the former `mut counts` parser failure, then emitted a finite corrupt-AST batch: statement IDs `1706..1756` were read against an arena of length `462` and converted to `NilLit`. The producer was stopped after 1h20m because that candidate could not pass admission; it produced no binary.
- Native statement and expression arenas now use zero-based arrays exclusively when `SIMPLE_NATIVE_ARENA_DECLS=1`; bootstrap environment counts, tags, and payload mirrors remain only for the true interpreter-bootstrap branch. `bootstrap_ast_native_arena_spec.spl` poisons both count and payload mirrors, parses sequential modules, rejects `NilLit` substitution, and preserves the opposite interpreter-mirror behavior.
- A second full-CLI cycle from the same pre-fix Stage3 reproduced the exact 3,718-byte OOB batch, proving the running compiler binary—not another source duplicate—still owned the stale allocator. It was stopped at 50m with no candidate.
- Three bounded Stage2-to-Stage3 refresh attempts were consumed. LLVM was unavailable in Stage2. Cranelift compiled the 662-module closure, but both dynload and one-binary links omitted the `rust-hosted` runtime and failed on unresolved `rt_*`/`spl_*` symbols. Logs are `build/bootstrap-recovery/logs/stage3-fixed-native-build.log`, `stage3-fixed-cranelift-native-build.log`, and `stage3-fixed-cranelift-one-binary.log`.
- No third full-CLI cycle, target build, image build, QEMU run, commit, or push is allowed until a fresh session repairs the Stage3 runtime-bundle link or reconstructs the exact known-good Stage3 command. The next candidate must contain the arena fix and pass the canonical redeploy gate before architecture work resumes.

## 2026-07-18 Core-C Stage3 runtime selection repair

- Guided linker and historical sidecars confirmed both Cranelift output modes converge on `NativeProjectBuilder::selected_runtime_library`; response-file routing and object mode were not the unresolved-symbol cause. The failed recovery commands supplied an explicit runtime directory with no `libsimple_runtime.a`, and the selector incorrectly let that directory suppress its required Core-C fallback.
- Bootstrap Stage2/Stage3 now request the supported `core-c-bootstrap` lane. That lane selects `libsimple_native_all.a` for `bootstrap_main.spl` only when the explicitly requested bundle is the legacy hosted recovery lane; otherwise it builds/selects an ABI-checked Core-C archive even when an explicit runtime path is present, and fails closed if no archive can be produced.
- The exact regression `test_core_c_bootstrap_entry_builds_runtime_when_explicit_path_has_only_native_all` passed: 1 passed, 0 failed. Bootstrap shell syntax and `git diff --check` passed before the regression. No further Stage3/full-CLI build was started because the three recovery cycles for this session were already consumed.
- Next fresh turn: run one cache-preserving Cranelift Stage2-to-Stage3 refresh using the repaired selector, then run the canonical full-CLI admission gate once. ARM64/RISC-V64 builds and QEMU remain gated on that admission; no commit or push is yet authorized.

## 2026-07-18 post-sync CLI recovery and architecture review

- Main was rebased linearly and pushed at `34740e42a9312590743230ada7cc02df57491fae`; the file-count guard increased and the Core-C selector regression passed after rebase. The external `/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple` was independently rechecked and rejected because it prints the Rust bootstrap-seed warning; it cannot run product/SPipe evidence.
- A current debug Rust driver built successfully, but its Stage2 entry-closure discovery remained CPU-active for 15 minutes with zero cache objects. It was stopped without cache loss. A two-job `--profile bootstrap -p simple-driver` build is the active bootstrap-only recovery path; no full bootstrap, target build, or QEMU run has started.
- Higher-model ARM64 review accepted two shared fixes from the guided audit: `/usr/bin/simple /hello.spl` now uses `arm64_fs_exec_spawn_ring3` and checks the returned exit status, and the direct-load owner now validates PT_LOAD/file arithmetic and a bounded 7 MiB image span. Address-space regions are 8 MiB and fallback stack frames moved to the disjoint in-RAM `0x52000000..0x57000000` range. AArch64 C syntax and workspace whitespace checks pass; Simple specs await an admitted CLI.
- RV64 PMM now stops at `RISCV_HEAP_START` instead of overlapping the heap, and each user root inherits validated supervisor-only slot-0 MMIO plus slot-2 kernel RAM. The live filesystem lane is still not wired: its target remains marker-oriented and RV64 lacks a generic mounted-FAT byte reader feeding `resolve_executable_bytes`; do not substitute the legacy generated proof ELF for filesystem evidence.
- Current web/DB and LLVM/Clang audit found retained history only. RV64 `POST /db` still routes through `SimpleDbService`, but current ELF/log artifacts are absent. After CLI admission, rebuild one stamped x86 Simple payload/kernel/image and prove CPL3 `emit-llvm`; then run filesystem LLC/LLD/Clang and finally the existing HTTP/DB wrappers. Reuse existing profiles and service owners; do not add new wrappers.

## 2026-07-18 package-data recovery checkpoint

- Native-project import discovery now carries selected package-data types into HIR before strict MIR lowering. Explicit and current/ancestor package exports are eligible; unrelated globally unique data is deliberately excluded so a typo cannot bind another package's declaration. Untyped `let`/`static` data remains `Any`, constants reuse the shared constant evaluator, and ambiguous named-type owners degrade to `Any`.
- The focused Rust regression passed once and proves typed current-package data, untyped data, constant data, ancestor visibility, ambiguous-type handling, rejection of an unrelated global, and valid object production. Source-contract specs also cover the corrected bidirectional-call type argument and native backend imports; executable Simple evidence still requires an admitted CLI.
- The optimized bootstrap-only driver rebuilt successfully. The cache-preserving Stage2 gate reduced the strict-MIR failure set from 16 files to five, all in the interpreter subtree: sibling-owned `val_arrays`, `val_struct_fields`, and `eval_implicit_new_stack` exposed the remaining package-private visibility gap. A follow-up patch now indexes unique owners per effective package, treats underscore-prefixed split directories as transparent, and rejects ordinary-child, unrelated-package, and duplicate-owner access; its focused Rust regression passes. The session iteration cap is reached, so the patch has not received a Stage2 retry and no Stage3, full bootstrap, target build, image build, or QEMU run is claimed.

## 2026-07-18 hosted Stage2/3 recovery and Stage4 phase-one allocation

- The package-private data patch passed a fresh cache-preserving Stage2 build and Stage2 sanity, then a Stage3 self-host build and the same sanity. The remaining Stage2 link failure was command configuration: `bootstrap_main.spl` requires the existing bootstrap-only `rust-hosted` bridge for `rt_native_build`/`rt_cranelift_*`; Core-C remains correct for Stage4. The hosted selector regression passed, `simple-native-all` was built separately, and its three required symbols were verified. The canonical bootstrap script now uses `rust-hosted` for Stage2/3 only.
- Stage4's fixed in-process API silently dropped the requested low-memory option. It now sets `CompileOptions.low_memory=true`, and the existing Stage4 source contract requires that assignment. A refreshed Stage2/Stage3 pair compiled this change successfully.
- A profiled Stage4 retry reached `phase1:load_sources:start` but consumed about 11.3 GiB before phase 1 completed. A bounded 20-second trace scanned 905 unique physical files totaling only 11.8 MiB, disproving duplicate-graph and bucket-array theories. The phase-one docstring scanner was allocating a `spl_str_slice` C string for every source character solely to count triple quotes. It now searches only actual `\"\"\"` delimiters while preserving odd/even block and same-line behavior; a focused behavioral/source regression was added.
- The Stage2 cycle cap is reached, so the phase-one scanner patch has not yet been embedded or executed. Next fresh continuation: rebuild cached Stage2/Stage3 once, run the focused closure spec, then make one profiled Stage4 attempt. No full bootstrap, target build, image build, QEMU run, server claim, commit, or push follows from this checkpoint.
- ARM64 re-audit also found that mounted VFS reads cap arrays at 1 MiB and silently truncate a real Simple payload; the direct-load image span is capped at 7 MiB. RV64 web/DB remains gated on an admitted CLI and stamped kernel, and the retained system spec has stale marker expectations. These lanes remain queued behind CLI admission.

### Checkpoint correction after embedding the scanner patch

- Fresh cached Stage2 and Stage3 builds both passed with the delimiter-search scanner embedded, but one bounded Stage4 profile still remained in `phase1:load_sources:start` and grew from about 6.0 GiB at 39 seconds to about 13.7 GiB at 81 seconds. The scanner fix is therefore retained as a valid allocation reduction, not claimed as the complete Stage4 fix.
- Stage3 disassembly shows `_driver_text_bucket_index` validating the Simple-core string magic before hashing. The Rust-hosted Stage3 runtime uses a different `RuntimeString` header, so that validation returns hash zero and collapses every entry into bucket zero. `_driver_text_bucket_set_has` then repeatedly splits the entire growing bucket, matching the observed quadratic retained allocation. The next bounded cycle must replace this layout-dependent hash with a runtime-compatible text hash and prove that distinct keys distribute across multiple buckets under the actual Stage3 binary before one final Stage4 profile.

### Dual-layout hash repair and next import blocker

- A focused Cranelift JIT regression passed an actual Rust `RuntimeString` to generated `rt_hash_text` code. It failed before the fix with generated result `0` versus runtime result `193485963`, then passed after the inline hash accepted both the Core-C `STR1` layout and the shared Rust/SimpleOS header-plus-hash layout; the strengthened check exercises both byte offsets. `_driver_text_bucket_set_has` now uses exact newline-sentinel boundary checks instead of allocating an array and copied strings through `split` on every probe.
- The optimized bootstrap seed rebuilt once. A single cached dynload cycle produced sane Stage2 and Stage3 executables; both sanity gates and the Stage2 native-build capability gate passed. No full CLI wrapper or full bootstrap ran.
- The next profiled Stage4 attempt made bounded progress: phase one stopped after 7.2 seconds at 450 MiB RSS on the concrete unresolved import `std.alloc.sffi`, instead of remaining in the earlier multi-gigabyte prefix. Combined with the focused dual-layout regression this supports the hash fix, but the early import failure means full phase-one convergence is not yet proven and no CLI is admitted.
- The compiler has eleven imports of the existing `std.alloc.sffi` facade but its only source lived below the Rust-seed legacy tree. The pure source roots now contain the narrow canonical `src/lib/alloc/sffi.spl` owner for the three actually imported dictionary operations. Runtime boundary decision: reuse the existing facade and runtime symbols; reject a product resolver fallback into `src/compiler_rust`, per-caller extern duplication, and new runtime aliases. The iteration cap prohibits another Stage4 attempt in this cycle.
- Stage3 single-positional pure-driver probes with both terminal-symbol and brace imports resolved the new facade, parsed both modules, completed HIR and MIR, then faulted only at `aot:borrow_check:start` with `field access on nil receiver` (SIGILL 132). This proves the import fix but exposes a separate single-file AOT borrow-check bug; the temporary always-red fixture was removed. The resolver unit assertion retains terminal-symbol fallback coverage, and no import spelling is blamed for the later failure.

### Stage4 phase-two allocation diagnosis and fix

- One bounded Stage4 attempt completed phase one in 7.237 seconds and parsed 307 of 1,278 unique sources. It then hit the 8 GiB cap at 7,218,796 KiB RSS while requesting exactly `0x90000010` bytes.
- That allocation is the Rust heap-pointer registry's hashbrown resize after more than 117 million registered transient objects, not an array-length corruption and not a regression in the dual-layout text hash.
- Rust and Core-C `rt_string_new` now intern immutable empty and one-byte strings (257 entries total). Module/declaration flat-AST mode checks use registry-allocation-free `rt_env_get_i64`; expression/statement mode is cached during reset. All three arenas clear in place while preserving current flat-body, GPU, and ASM fields.
- The focused Rust interning regression passes 1/1; rustfmt check, `git diff --check`, and Core-C/runtime-focus syntax checks pass. The bootstrap seed runner failed with `no examples executed`, so it is recorded as unsuitable and will not be repeated.
- No Stage2/Stage3 rebuild or Stage4 retry has run after this fix. The next fresh bounded cycle is one incremental optimized seed refresh, one cache-preserving Stage2/Stage3 refresh, then at most one profiled Stage4 attempt.
- The incremental optimized driver plus cache-preserving Stage2/Stage3 refresh is now complete. Stage2 sanity, Stage3 sanity, and Stage2 native-build capability all passed at 332,936 KiB peak RSS. Canonical Stage2 hash: `40b734440d7a6627f23e46199e22c82e3b1247ac4678b9044760943f3dfe4a98`; Stage3 hash: `360f0447bb4912ba6a9bd5df10035c439a2ac28a6527c6cf4d36bd2ee4a5b1b4`.
- Do not run another Stage4 in this session: its single bounded attempt was consumed before the allocation fix. The next fresh cycle may make one profiled Stage4 attempt and compare against the old 307-file/7.2-GiB phase-two baseline before any full CLI admission, target build, image build, or QEMU work.
- Final higher-model review covered runtime-registry clearing: it now re-registers the stable short-string cache pointers, and the extended focused Rust test passes again. This lifecycle-only follow-up does not alter the Stage4 hot path; do not repeat the successful Stage2/Stage3 refresh for it in this session.

### 2026-07-19 corrected Stage2 runtime handoff

- Artifact review rejected the session's one Stage4 profile because the admitted Stage2 still embedded the pre-interning `rt_string_new`; `simple-native-all` had not been rebuilt. The rejected run reached 7,277,400 KiB RSS and failed the same exact 2,415,919,120-byte registry growth allocation during phase-two parsing. The Stage4 cap is consumed; do not run another profile this session.
- The run exposed a real inline fat-arrow match-arm bug: the parser stored expression ids but the flat bridge consumed statement ids, producing out-of-bounds tags and silent Nil substitutions. Inline expressions are now normalized through `stmt_expr_stmt`; the executable literal/return-arm bridge regression passed once (`1 example, 0 failures`, `flat_ast_fat_arrow_match_bridge=true`).
- `simple-native-all` was rebuilt incrementally, followed by the normal one-thread dynload Stage2/Stage3 wrapper without `--full-bootstrap`, full CLI, deploy, or MCP. Both sanity gates and the Stage2 capability (`windows native hello`) passed at 371,256 KiB peak RSS. Fresh Stage2 `a1d5e46b795534d057d4d6ab199b7dc0d18fe8db11b317aefbbea665ea0d5bcc` and Stage3 `c4ade909cf6590138f27bcf2f7a0fd668c3e488666cff62aac048b088d5d9d05` both disassemble with the short-string branch; no full CLI exists.
- The cache re-registration lifecycle proof now reuses the existing serialized registry-clear test and passes 1/1. The native-arena fixture uses accepted bootstrap-entry paths and proves the first converted Module retains value 7 after the second parse/reset; all 3 examples pass. Scoped rustfmt and `git diff --check` pass.
- Next fresh session: run at most one bounded Stage4 profile from the corrected Stage2, then admit the CLI only after version/expression/source validation and `bootstrap_essential_tools_smoke=true`. Target Simple, filesystem image, LLVM/Clang CPL3 execution, and live web/DB QEMU remain queued behind that admission.

### 2026-07-19 corrected Stage4 profile result

- The one permitted Stage4 profile from corrected Stage2 `a1d5e46b795534d057d4d6ab199b7dc0d18fe8db11b317aefbbea665ea0d5bcc` was externally stopped at 2:48.43 after 344 files completed and 345 started (3,948,533 source characters). Peak RSS was 3,313,200 KiB; no AST out-of-bounds, missing-tag, NilLit, crash, or giant-allocation diagnostic appeared, and no output binary was produced.
- The repair materially improved throughput and memory per source character, but two consecutive roughly 100-file windows still grew by more than 1 GiB, so the profile is rejected and the Stage4 cap is consumed. Logs: `build/native_probe/stage4-short-string-intern.log` and `.time`.
- `STATUS: FAIL`: no full CLI is admitted, so filesystem Simple/LLVM/Clang execution and live web/DB QEMU remain unverified. Do not run Stage4, full bootstrap, target/image builds, or QEMU again in this session.
- Next fresh session: add the smallest preprocessor and domain no-op fast paths with focused identity/directive/domain tests, refresh Stage2/Stage3 incrementally, then permit one bounded Stage4 profile.

### 2026-07-19 filesystem/server pre-admission repair

- The preprocessor/domain fast paths and focused regressions are now pushed at `38d2020707`; the preprocessor, domain, native-arena, and declaration-slot diagnostics passed. A first cache-preserving Stage2 refresh was stopped before completion when parallel audits found goal-blocking OS source regressions, avoiding a redundant build of known-bad source.
- x86 filesystem exec no longer consumes the unkeyed global preload buffer. All normal launches now continue through the opened path's bounded streaming loader. The returning 64 MiB heap registration needed for multi-command filesystem compiler execution is restored from `a5fdae0384`, while the explicit heap smoke retains its QEMU-halting mode.
- RV64 routing again matches its live checker: `GET /health` selects JSON health, `GET /` selects the historical HTML page, and file routing is unchanged. The pure classifier diagnostic passed 11/11. Current-source HTTP/DB QEMU evidence remains absent.
- The restored x86 numbered spec exposed two test defects: reserved keyword `spawn` used as a variable and an unescaped `{live_rc}` source literal. The variable fix let 3/4 scenarios pass and proved the streaming/preload contract; the final literal fix is applied but unverified because the three-cycle cap is consumed. The broader boot transport diagnostic also remains unsuitable under the seed because an unrelated imported FAT32 module fails on `Fat32Core.new`.
- `STATUS: FAIL`: no refreshed Stage2/3 or full CLI is admitted. Next fresh continuation must run the corrected x86 filesystem spec once, then one cache-preserving Stage2/3 refresh and at most one profiled Stage4. Do not start target/image/QEMU work before CLI admission.

### 2026-07-19 pre-bootstrap artifact admission gates

- Explicit x86 image payloads now require the canonical SimpleOS tool entry, target, entry closure, LLVM/Cranelift backend, non-seed compiler provenance, a newer build stamp, and an exact SHA-256 match. Unset x86 overrides retain the historical generic image-fixture fallback; ARM64/RISC-V behavior is unchanged. The native producer writes the matching `artifact_sha256` stamp field.
- Both x86 filesystem-exec wrappers now validate every newly built or reused kernel before hashing/QEMU: ELF64 little-endian x86-64 EXEC, nonzero entry inside an executable PT_LOAD, no PT_INTERP, no defined weak fallback symbols, and no strong undefined symbols. Guarded weak undefined hooks remain permitted by design.
- The disk-free shell matrices, one real freestanding x86-64 ELF parse, shell syntax, and the focused `make_os_disk_contract_spec.spl` diagnostic pass. The focused SSpec reports 4/4 under the Rust seed and is bootstrap-only evidence; no target/image/QEMU claim follows from it.
- No Stage2/3 or Stage4 run started while unrelated compiler jobs owned the shared cache. Next gate remains one cache-preserving Stage2/3 refresh, then at most one bounded Stage4 admission profile.

### 2026-07-19 current runtime, Stage2/3, and Stage4 parser result

- The isolated Rust seed and `simple-native-all` archive were refreshed incrementally, not through full bootstrap: seed SHA-256 `b2fe74eacbd8d67f5e94a015d7221b13237e14becf35ebf7b7595e7cdb2baef4`; runtime archive SHA-256 `0173a73aab5a71829c80f1c0e0c9f94b20a7393124850ebeca7e49312e7a5127`.
- One cache-preserving pure-Simple dynload Stage2/3 refresh passed both compiler sanity gates and the Stage2 native-build capability in 16:05.97 at 316,372 KiB peak RSS. Stage2 SHA-256 is `e7dcdeb568a360a0f0d9ef27f52c67a80462180c3978100c1e7147eb7f6c2fc3`; Stage3 SHA-256 is `24f31e811ed3bc6d5ebfa49f3e6258bca3b6d435353d3a1147215ab9a1976a90`.
- The one bounded Stage4 profile parsed 633/1,281 unique files in 1:34.32 at 5,900,992 KiB peak RSS, then failed before HIR on `collection_opt_core.spl:470:43`: `expected ), got Ident 'counts'`. Unlike the 2026-07-17 historical failure, this run emitted zero stale statement-arena OOB/missing-tag diagnostics.
- Root review found the separate impl/class method parser omitted the already-supported prefix-`mut` parameter helper and never stored method parameter mutability. That owner now reuses the helper, preserves alignment through synthetic `self`, and records `[0, 0, 1]` for `(self, inst, mut counts)`. The isolated focused spec passes 1/1 under the refreshed Rust seed as repair-only evidence.
- The Stage4 cap is consumed; no full CLI, target Simple payload, filesystem tool run, or live web/DB QEMU claim is made. Next fresh session must rebuild Stage2/3 from this parser fix, then permit at most one new bounded Stage4 admission profile.

### 2026-07-19 current-head refresh, bounded parse wall, and gate recovery

- One cache-preserving current-head Stage2/3 refresh passed Stage3 sanity and Stage2 native-build capability in 16:35.66 at 290,284 KiB peak RSS. Fresh Stage2 SHA-256 is `dcef35aed8b98e16d3ae8e3fa4f42d72b2239060cf30089bb51aa9600848518c`; Stage3 is `76b85ba4f372b0da52c7801d853f43cd69c189c116e60b760abc7cd09e377205`. The wrapper explicitly reused the existing Rust seed/runtime and warned that their input provenance stamp is stale.
- The one permitted Stage4 attempt completed phase 1, collected 1,282 unique sources, and completed 86 files before the 1,200-second cap while actively parsing `src/app/jj/sync.spl`. Peak RSS was 3,263,384 KiB. It emitted no parser/OOB/missing-tag/allocation failure, but it did not reach `collection_opt_core.spl`; this is a bounded phase-two parse-performance result, not full-CLI admission or independent end-to-end proof of the parser repair.
- Unrelated commit `fd51a8dd6d` had deleted the passing payload provenance/hash gate, its focused spec/manual, the shared x86 kernel ELF checker, and caller wiring. Those reviewed files/calls are restored byte-for-byte from `23dc24a605`; the canonical UEFI `/usr/bin/simple /hello.spl` wrapper now also validates its kernel before GRUB packaging. The focused contract then caught a second unrelated clobber in `fa1ee50c35`: the root `HELLO.C` entry and Clang/LLC/LLD-only `/usr/bin` creation were restored. The checker self-test, C/shell syntax, and five focused scenarios pass.
- The existing x86 sysroot producer passed in 4.33 seconds with optional libc++ skipped. `crt0.o`, `libsimpleos_c.a`, `libsimple_runtime.a`, and `share/simpleos/simpleos.ld` now exist. Target Simple remains queued behind full-CLI admission; no target/image/QEMU/server execution claim is made.
- Next fresh Stage4 work must address the existing compiled-frontend dispatch task recorded in `doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout_2026-07-05.md`; do not raise the timeout or add a parallel cache/wrapper.

### 2026-07-19 multi-architecture filesystem continuation

- Three reviewed checkpoints are pushed through `3833544b91`: target-matched Simple/Clang payload validation, ARM64 mounted-filesystem EL0 exit/return restoration, and Stage4-safe LLVM construction plus the diagnosed raw-string contract correction. ARM64 focused contracts passed 8/8 and 2/2; the payload contract passed 5/5.
- The dead LLVM patch applicator referenced assets that never existed and had no callers. Commit `94fe3f4539` removes it and pins both documentation and the build owner to published fork source `3b33ba807a99855133981897fa8c9d91933f759d`; the external dirty LLVM checkout remains untouched. OVMF Clang evidence is described honestly as guest object emission, not in-guest link/execute completion.
- Guided RV64 restoration now reuses the historical Sv39 paging, trap-vector, Scheduler, user-entry bridge, and filesystem-spawn owners. Userspace links in VPN2 slot 4 at `0x100000000`; user roots retain supervisor-only MMIO slot 0 and kernel slot 2; syscall 0 restores the saved S-mode continuation and raw exit code. No parallel loader or context ABI was added.
- `test/01_unit/os/kernel/loader/riscv64_fs_exec_spawn_spec.spl` is the single focused source contract for that chain. Three bounded Rust-seed diagnostics failed without exposing an assertion or interpreter error, even after interpreter-sensitive source operations were removed. The mandatory retry cap is consumed; its generated manual and live QEMU proof remain pending and no RV64 PASS is claimed.
- Final crash review also found two implementation blockers: the user handoff lacks `fence.i` after loading executable pages, and the `rv64gc/lp64d` payload ABI can execute floating-point instructions while supervisor FS remains Off and trap/task contexts omit FPR state. The RV64 restore must remain unlanded until both contracts are resolved and a fresh-session focused check passes.
- An externally owned bounded Stage4 v45 attempt is still CPU-active in `/tmp/simple-tooling-hardening-land`; its log is empty and candidate absent. Do not duplicate it. If a candidate appears, require current-source validation, the canonical redeploy gate, and `bootstrap_essential_tools_smoke=true` before target/image/QEMU work.

### 2026-07-19 Stage4 v45 terminal result and lexer scratch reuse

- The externally owned v45 run terminated at its 1,200-second cap with no candidate. Import discovery completed at +38.293s and 40 files completed by +346.179s; `lexer_struct.spl` started at +346.203s and never emitted its done marker. This is inside `parse_full_frontend`, before post-parse admission. The compiled Stage4 route is direct; no interpreter fallback is implicated.
- Higher review rejected the sidecar's 360-second-cutoff interpretation because the observed compiler process remained active for the full 1,200-second envelope. The file therefore had about 854 seconds, not 14 seconds. No second Stage4 attempt is permitted this session.
- `CoreLexer.char_slice` already avoided quadratic prefix concatenation but allocated one temporary `[text]` per token. Commit `0cb8fa82eb` reuses one per-lexer `slice_parts` array, clearing and joining it for each span. The exported lexer facade and token semantics are unchanged; no new runtime symbol, abstraction, or legacy-scanner rewrite was added.
- The existing five-case lexer regression passes once under the bounded Rust repair runner (`SIMPLE_TEST_RUNNER_RUST=1`, 4 GiB, 180 seconds). Its manual was refreshed to match the executable source. This is bootstrap-repair evidence only; `simple optimize` and product verification remain pending because this worktree has no admitted pure-Simple `bin/simple`.

### 2026-07-19 RV64 filesystem handoff crash-safety repair

- The opaque RV64 contract failure was a parse-time test defect: `spawn` is a reserved token. Renaming the local to `spawn_source` exposed the assertions normally; the strengthened focused contract now passes on its final bounded cycle, and its generated manual is current.
- Same-hart PT_LOAD publication now executes the existing `fence_i` intrinsic after switching to the user address space and before `_rv64_enter_user`. The contract scopes and orders all three operations so unrelated calls cannot false-green it.
- RV64GC/LP64D state is now explicit: the aligned context is 544 bytes, trap and first-user-entry frames preserve all 32 FPRs plus `fcsr`, voluntary switches preserve `fs0`-`fs11` plus `fcsr`, user `fcsr` is cleared before compiled kernel dispatch, and generated S-mode entry enables FS Initial with RNE/default `fcsr`. Both RV64 assembly blocks assemble as `rv64gc/lp64d`; the trap-model spec passes 6/6.
- Duplicate numbered and legacy test-tree `Riscv64Context` constructors now initialize the 264-byte FP area and alignment pad. Independent Spark fence, ABI, assembly-layout, and false-green reviews report PASS after the final fixes.
- Evidence remains bootstrap-repair only because this worktree still has no admitted pure-Simple CLI. No Stage4, full bootstrap, target/image build, QEMU, filesystem executable, LLVM/Clang, web, or DB execution was started or claimed in this slice.

### 2026-07-19 pre-admission disk payload and RV64 TCP-close repair

- The host matrix no longer expects the removed dedicated port-5432 forward or the stale `DB SELECT 1` marker. Its current `/db` POST contract uses the HTTP listener's 8080 forward; the RV64 network-port row passes and FPGA network capacity is explicitly planned. The aggregate matrix remains honestly failed because current RV64 WM/display and host-launch evidence is absent.
- `make_os_disk.shs` retains x86_64's optional default LLC/LLD payloads, validates them as ELF machine 62 when present, and accepts ARM64/RV64 LLC/LLD only through explicit machine-183/243 inputs. This prevents host-x86 tools from being silently embedded in non-x86 images. Shell syntax/self-test and the focused five-scenario disk contract pass; the executable evidence used the bounded Rust bootstrap-repair runner only.
- Runtime need: honor HTTP `Connection: close` on the wire so byte-written web/DB replies complete without relying on client timeouts. Facades checked: `rt_net_close`, `rt_boot_tcp_write_bytes`, `rt_boot_tcp_write_text`, and the existing packet sender. Chosen path: one runtime-owned `rt_boot_tcp_send_fin_once` helper with bind/SYN reset, text-write use, and byte-write close fallback. Rejected shortcuts: longer `nc` timeouts, `|| true` as proof, content-length-only workarounds, duplicate per-feature FIN paths, and a new wrapper.
- The focused TCP-close scenario passes with send-once/reset/write/close assertions. The broad RV64 network spec reached 21/22; artifact results isolated the other failure to an unused reintroduced `rt_gpu_fill_test_pattern` helper. The helper had no callers and was removed while keeping its regression assertion. The numbered manual was regenerated without rerunning the spec. The three-cycle cap is consumed, so that final dead-code removal has static/source review only and must not trigger a fourth run in this session.
- Higher review and Spark review accept the FIN implementation as minimal and safe. C syntax and final repository gates are recorded separately at handoff. No target/image/QEMU run was started. The externally owned incremental Stage4 cycle 27 terminated without a candidate after about 1,571 seconds in phase-3 HIR lowering; MIR/codegen/link were not reached. Its log reports 43,632 unresolved types (26,832 lowercase/value-like), 14,709 unresolved names, 731 missing return types, and 17 unsupported-generic diagnostics. The smallest next compiler lane is one focused lowercase-identifier repro in shared HIR expression-vs-type/name-category dispatch before module-specific cleanup. That owner's cache/output was not touched, and no retry or full bootstrap is authorized in this session.

### 2026-07-19 Stage4 imported-parameter dispatch checkpoint

- Three independent read-only audits traced the earliest `unresolved type: print` to imported callable signature registration, before body lowering. `declared_callable_type` indexed erased `[Param]` elements directly; the current uncommitted repair applies the established typed-`Param` rebind before every `.name`/`.type_` read in that owner and in its simple return-type inference helper.
- `test/01_unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl` keeps the frozen scenario/step vocabulary and contains a functional imported-signature probe plus a source-contract guard. The source-contract scenario passes, but the functional scenario remains red under the bounded Rust bootstrap-repair runner (1 pass, 1 fail) across the three permitted cycles, and the runner exposes no assertion detail.
- The compiler patch and red spec are intentionally uncommitted. Do not delete or weaken the test, do not run a fourth cycle in this session, and do not start Stage2/3/4 or full bootstrap. The next fresh session must first split the functional scenario's import-resolution and diagnostic assertions (or use a single diagnostic fixture) to identify the remaining harness/implementation failure, then review the typed-rebind patch before any incremental build.

### 2026-07-22 Stage4 imported-parameter dispatch acceptance

- The functional probe was split and reduced to an import-only consumer. It now proves both zero HIR diagnostics and local-or-qualified callable registration; the source contract continues to guard every erased `Param` rebind.
- The focused spec passes 3/3 once under the bounded Rust bootstrap-repair runner, and its generated manual is current. Independent small-model review plus final higher-model review accept the shared `declared_callable_type` root-cause fix.
- No Stage2/3, Stage4, full bootstrap, target/image, or QEMU work ran. An unrelated Stage4 build owns another worktree, so the next step is an isolated Cranelift Stage2/3 refresh only after that owner clears, followed by at most one bounded Stage4 admission attempt.

### 2026-07-22 current-evidence and low-resource preflight

- Three small-model audits, checked against the canonical scripts/specs by the final higher-capability reviewer, classify AC-3 as current PASS; AC-7 and AC-10 remain source/documentation-only partials; AC-1, AC-2, AC-4, AC-5, AC-6, AC-8, and AC-9 remain FAIL or current-unproven. Historical HTTP/DB, Clang, and Simple filesystem logs are not current-source evidence.
- Shell syntax for `make_os_disk.shs`, `build_fsexec_prod_ring3.shs`, `build_clang_disk.shs`, and `simpleos-native-build.shs` passes. `make_os_disk.shs --self-test` and `check-simpleos-x86-kernel-elf.shs --self-test` each pass once on current source.
- An active 24-GiB Stage4 build belongs to stale July 18 source in `/tmp/simple-memory-sync-resume`; it is isolated and cannot admit this worktree even if it succeeds. No competing compiler, target, image, or QEMU build was started under current memory pressure.
- Next current-source chain: isolated Cranelift Stage2/3 refresh; at most one bounded Stage4 candidate; current-source validation, canonical redeploy, and `bootstrap_essential_tools_smoke=true`; then one stamped x86 CPL3 `emit-llvm` filesystem profile before LLC, LLD, Clang, Simple filesystem, or RV64 web/DB live gates.

### 2026-07-22 portability guard convergence

- Rebase brought in the ARM32/ARM64/x86_32 bare-metal text-index ABI repair. The low-resource portability contract initially failed because its July 19 assertion still expected hand-written `MirLowering(...)` field maps after July 20 collapsed both driver copies into `MirLowering.new_for_target`.
- The guard now rejects every non-comment direct driver constructor, requires both active driver paths to use the canonical constructor, and pins both enum runtime-ID maps in that owner. The final bounded portability check passes, shell syntax/diff whitespace pass, and the stale struct-construction bug record now describes the canonical-owner contract.
- This is static current-source evidence only. The LLVM/Cranelift cross-module text ABI execution gate and all Stage2/3, Stage4, target, image, and QEMU gates remain pending while the unrelated stale-source Stage4 process consumes roughly 35 GiB RSS with swap exhausted.

### 2026-07-22 current Stage2/3 incremental recovery

- The focused cross-module u8/text ABI gate never reached its assertion in three bounded attempts: the isolated worktree had no `bin/simple`, the base `bin/release` candidate identified itself as a Rust seed and was rejected, and the external pure Stage3 lacked its companion core-C runtime path. The retained diagnostic failed at runtime archive selection, not at ABI behavior. Do not retry this gate again in this session.
- The first isolated current-source Stage2 attempt reused the Rust seed, disabled fallback, and failed honestly at link on only `rt_heap_registry_count` and `rt_cranelift_new_aot_module_triple`. Both owners existed in current source but were absent from stale `libsimple_native_all.a`; two independent small-model reviews and final higher-model source/symbol review rejected a source shim.
- Only `simple-native-all` was rebuilt with the Cranelift bootstrap profile; the seed executable, seed stamp, and full bootstrap were untouched. The aggregate archive now defines both symbols, and `test_aot_target_triple_controls_object_format` passes 1/1.
- The cache-preserving Stage2/3 retry then passed Stage2 sanity, Stage3 self-host sanity, and Stage2 native-build capability. Stage2 SHA-256: `73df1f604f172a339b619db7fb8f6a10e2172d19b8b43222550288edd21dae79`; Stage3 SHA-256: `7066582ad639cba497adac15d5e5e71a5e29fa5d39161fed01c3207f73f134b6`. Full CLI/Stage4 was explicitly skipped.
- Next fresh session must first run the focused ABI gate once with `SIMPLE_BINARY=$PWD/build/bootstrap/hir-param-repair/stage3/x86_64-unknown-linux-gnu/simple` and `SIMPLE_RUNTIME_PATH=$PWD/src/compiler_rust/target/bootstrap`. Only after it passes may one bounded Stage4 current-source admission attempt start from this verified Stage3/cache.

### 2026-07-22 post-sync current Stage2/3 correction

- A sync after the first green refresh brought current MIR/seed-HIR fixes through `8d822dbabe`, so the earlier Stage2/3 hashes were immediately classified stale rather than promoted. `simple-native-all` was incrementally refreshed again; the seed executable and seed stamp remained untouched.
- The third and final Stage2/3 cycle rebuilt from rebased HEAD `5b4b6c7d4c`, passed Stage2 sanity, Stage3 self-host sanity, and Stage2 native-build capability, and explicitly skipped full CLI/Stage4. Current Stage2 SHA-256: `a6cf4c2d64e2dc622b4ecc4b72e465682ac11d87a2fb5a8df6277b98f007a779`; current Stage3 SHA-256: `5043b40b0b2329131a55ed51ca3ff84b26967593ffa2d173a28da0fd50de607d`.
- The Stage2/3 three-cycle cap is consumed. Do not rebuild or start Stage4 again this session. Next fresh session still begins with the focused ABI command recorded above against this exact Stage3/runtime pair; if it passes and source HEAD remains unchanged, permit at most one bounded Stage4 admission attempt.

### 2026-07-23 post-build sync invalidation

- The mandatory fetch after the final green build advanced `main` through `170de65f2c`, including self-hosted MIR locals resolution and entry-closure sibling-import compiler fixes. The `5b4b6c7d4c` Stage2/3 artifacts are retained evidence but are not current-tip admission artifacts.
- The three-cycle cap forbids another rebuild in this session. Next fresh session must first refresh Stage2/3 once from current `main`, then run the focused cross-module ABI gate against that exact Stage3/runtime pair, and only then permit one bounded Stage4 attempt if HEAD has not moved again.

### 2026-07-23 Core-C ABI completion and arithmetic handoff

- The focused cross-module gate initially failed at link because the default Core-C runtime lacked `rt_array_last`. The canonical owner now delegates to existing negative-index semantics with `rt_array_get(array, -1)`; the public header, core-required symbol manifest, archive inventory, runtime focus checks, and executable ABI probe cover nonempty and empty arrays.
- The archive inventory exposed a separate historical omission: `rt_getpid` was still declared and required but its Core-C provider had been lost. The prior platform implementation is restored in `runtime_legacy_core.c`. The executable probe's byte-array expectation was also corrected to the established raw-`u8` ABI instead of tagged `rt_value_int`.
- `simple-native-all` rebuilt incrementally in 3m44s; the Rust seed and full bootstrap were untouched. The final Cargo test cycle was blocked before execution by unrelated Rust test-harness hidden-symbol linker failures. Earlier compiled-harness evidence proved the new symbol was present and both `rt_array_last` checks executed before the stale byte assertion.
- The refreshed default-LLVM cross-module build now links three modules with zero compile failures, but its executable exits 5 in `cross_target_arithmetic_ok()` before printing `result-u8-ok`. The final diagnostic is retained under `/tmp/check-native-crossmodule-result-u8-final-2850000`; the concrete follow-up is `doc/08_tracking/bug/native_crossmodule_arithmetic_exit_5_2026-07-23.md`.
- The three-cycle focused cap is consumed. No Stage2/3, Stage4, full bootstrap, target/image, or QEMU run is permitted in this session. AC-1/2/4/5/6/8/9 remain unproven; no live server or filesystem-toolchain claim is made.

### 2026-07-23 bootstrap admission correction and emitted-key handoff

- Guided small-model history/source/artifact audits and final higher-model
  review identified an unrelated current-tip admission regression: commit
  `5b11528575` required the intentionally minimal Stage2/3 `bootstrap_main`
  binary to support full-CLI `-c`. The unchanged environment-ABI probe now
  runs only in `simple_binary_is_valid`; generic stage smoke remains version,
  unsupported-`run`, and native p2 build/execute. The portability contract
  passes. The broad host-GPU self-test was killed without its aggregate marker
  and is not evidence.
- A retained Stage2 diagnostic passed every corrected generic admission row.
  Direct self-host produced Stage3 SHA-256
  `d82ad2d3c7a0a2cd781267cca7f6709752367831dd68f9e982834847fffbad49`
  from Stage2 SHA-256
  `68520a4fc367af15c5126da3b996141ac176ca42aa188878f1821d94f761b7dc`;
  Stage3 also passed the four generic rows.
- The unchanged LLVM+Cranelift cross-module gate still exited `5`. Higher
  disassembly review proved the destination-preserving unsigned-copy patch was
  correct in source but the bootstrap seed emitted both dictionary keys as
  `src_id`, retaining the stale source-first overwrite. The static source test
  false-greened and was removed with the unaccepted code patch.
- The next fresh bounded patch must avoid the collapsed aliases by calling
  `self.local_id_value(dest)` and `self.local_id_value(src)` directly in the
  destination/source `has` and index operations, then rebuild Stage2/3 once and
  run the unchanged executable fixture once. Inspect emitted keys before any
  separate `translate_load` provenance change.
- The compiler/fix cap is exhausted. Stage4, target/image construction,
  filesystem Simple/LLVM/Clang execution, and RV64 web/DB QEMU remain blocked;
  AC-1/2/4/5/6/8/9 remain current-unproven.
- Mandatory fetch/rebase then advanced `main` from `74269ec415` to
  `448317ea5d`, including frontend/HIR, AOT-cache, and codegen changes. The
  Stage2/3 hashes above are therefore retained diagnostic evidence only. The
  cap forbids another rebuild in this session; the next fresh continuation
  must apply the direct-operand key fix on current main before rebuilding.

### 2026-07-23 current-tip unsigned arithmetic retry cap

- The dedicated lane fetched/rebased cleanly to `41131675a8`; tracked-file
  count remained `105715`. Three one-writer, no-MCP Stage2/3 cycles completed
  without fallback or full bootstrap.
- Disassembly of the first refreshed Stage3 proved the direct Copy/Move keys
  are no longer collapsed: destination `has`/set use `dest`, source `has`/get
  use `src`. The unchanged dual-backend fixture still exited `5`.
- A declared-U64 Let-cast experiment produced a byte-identical diagnostic
  executable and was removed. Independent sidecars then accepted per-operand
  signed-aware comparison coercion after rejecting a combined-unsigned form
  that could zero-extend a signed peer.
- Final Stage2 SHA-256:
  `db21a54ea3f4957ce0f635b1f90ed46117335c9117ad00b0b8cadced4d354cd1`;
  Stage3 SHA-256:
  `4f09caaa7dca8c7a18f818175dfc06b044087665b67cdf977f6fcf825967d64a`.
  Both passed generic bootstrap sanity, but the third fixture run still exited
  `5`; no Stage4, target/image, QEMU, filesystem toolchain, web, or DB claim is
  accepted.
- The mandatory three-cycle cap is exhausted. Next session must prove whether
  the failing cast operand crosses `translate_load` before changing it; its
  unknown-pointer signed default can overwrite a MIR-primed destination, but
  this remains a hypothesis. Do not rerun Stage2/3 or the fixture unchanged.

### 2026-07-23 post-sync backend-route diagnosis

- Three bounded one-writer Stage2/3 fix/verify cycles at `f2b493ec65` passed
  generic sanity; no full bootstrap or Stage4 was run. The final fetch/rebase
  then synced the lane to `2bc8052471`, matching `origin/main`, so those build
  artifacts are retained diagnostics rather than current-tip admission.
- Final Stage2 SHA-256 is
  `549ea9150c2408c5e0a2148f24d36d6b6da236e2cb3f26452beb53d55deee3cb`;
  final Stage3 SHA-256 is
  `f606033b493e5c526a8cf70caad7ea0aee310bad24540d86adb43b0ecb932986`.
  The focused native-build gate still exits `5`.
- Temporary marker instrumentation proved the exact failed arithmetic row is
  branch 6: `high > 0.0` / `0.0 < high`. The marker was removed; the fixture
  remains intact.
- Backend review corrected the route: Stage3 `native-build` calls Rust
  `native_all`, whose default is Cranelift when the optional LLVM feature is
  absent. Pure-Simple textual-LLVM provenance and typed-integer-literal
  experiments therefore could not affect the executable and were removed. A
  no-MIR-optimization diagnostic was byte-identical and still exited `5`.
- The three-cycle cap is exhausted. Do not rebuild or rerun the unchanged gate
  in this session. Stage4, image/QEMU, filesystem toolchain, web, and DB proof
  remain gated.

### 2026-07-23 Cranelift arithmetic admission and flat Option handoff

- The independent mixed `u64`/float Cranelift fix was higher-reviewed, rebased
  onto current `origin/main`, and pushed as `8671270ca4`. One bounded Stage2/3
  refresh passed generic sanity with Stage2 SHA-256
  `f56f86e90a68d2e20cab956ecd834e50df0eab18482920f1f13e94497609f1b2`
  and Stage3 SHA-256
  `f08774b6ec2a6321c67ed15a62d6bcf277d41f25f994bcc161afa6c727002167`.
  The focused fixture advanced beyond arithmetic and exposed unresolved flat
  `Option.map`/`unwrap_or` lowering; no Stage4 was run.
- `runtime_need`: none. Flat optional mapping is compiler-owned control flow;
  ordinary native programs must remain linkable against `core-c-bootstrap`.
- `facade_checked`: existing `rt_is_none`, MIR `IndirectCall`, and the canonical
  branch plus typed Store/Load merge pattern.
- `chosen_path`: `fix-codegen-runtime-owner`. Evaluate receiver and argument
  once, branch on `rt_is_none`, invoke the outlined mapper only on Some through
  its raw `ANY/ANY` closure ABI, and reinterpret bits through the result-typed
  merge local.
- `rejected_shortcuts`: Rust-only `rt_option_*_flat` symbols, removed hosted
  runtime bundles, duplicate Core-C helpers, untyped lambda parameters, and
  receiver self-casts. Those paths either fail the admitted runtime lane or
  break float closure ABI.
- The focused MIR regression now covers one receiver evaluation, changed
  `i64? -> text?` result typing, raw closure ABI, F64 contextual lambda typing,
  typed F64 merge, branch presence, and absence of rejected helper calls; its
  final bounded cycle passed 1/1. Incremental Stage2/3 and native fixture
  admission remain pending higher review.

### 2026-07-23 flat Option native admission cap

- Higher review accepted the contextual-lambda and raw closure ABI lowering.
  The first incremental Stage2/3 cycle accidentally embedded the stale
  `libsimple_native_all.a`; its native gate still emitted the removed helper
  symbols. Rebuilding `simple-native-all` fixed the artifact owner rather than
  changing source semantics.
- Cycle 2 Stage2 SHA-256:
  `8f899fa7afed294dc1b8f45285b93d24786d00bd6fe4b6befa0fd87aa45069bb`;
  Stage3 SHA-256:
  `e270b7adff3f205ccd1a4e0457a7fbf386a3cf9e5289c712ca9ce42d1f29b9c4`.
  Both passed bootstrap compiler sanity and Stage2 native-build capability.
- The refreshed native fixture links without any `rt_option_*_flat` symbol.
  Its mapped value equals the absolute oracle `"7"`; diagnostic exit `12`
  isolates the remaining failure to the module-global `receiver_calls`
  counter, not mapping output. Module-global mutation is a documented unsafe
  test oracle in this compiler lane.
- The three-attempt native-gate cap is exhausted. Do not rerun it this turn.
  Next continuation should replace all three module-global counters with the
  already-admitted array-held class-field pattern from
  `test/fixtures/compiler/native_class_array_param_field_mutation.spl`, then
  rerun the fixture once against the exact Stage3 above. No Stage2/3 rebuild is
  needed if compiler source and native bundle remain unchanged. Stage4, QEMU,
  filesystem Clang/Simple, web, and DB evidence remain gated.

### 2026-07-23 flat Option text-return blocker

- Replaced unsafe module-global fixture counters with the admitted array-held
  `Counter` pattern. Integer and float `Option.map` values, receiver-once,
  mapper-only-on-Some, and eager-default checks all pass before the text row.
- Added local and cross-module `text?` Some/None rows. The executable still
  exits `51` with `Simple runtime error: function not found: str.map`; the
  compiler is still losing optional provenance before text method dispatch.
- Rust boundary regression passed 1/1 and higher review passed the typed inline
  MIR lowering. Two HIR declared-return carrier hypotheses (direct and admitted
  one-element-array storage) survived Stage2/3 sanity but did not move the
  native gate, so the ineffective HIR changes were removed and tests retained.
- Final Stage2 SHA-256:
  `03e1f32ae3013cdc3dee934a422bf96861f867a20caa276519fdbeea69cdda0c`.
  Final Stage3 SHA-256:
  `edb5dd7e9dc4093e3a180826115e7472081bcb10b747b7a44a9098df7b02e176`.
- The three-cycle cap is exhausted. Do not rerun the unchanged build/gate in
  this session. Stage4/full bootstrap, QEMU, filesystem toolchains, web, and DB
  remain gated.

### 2026-07-23 flat Option and integer-global admission

- Small-model flow tracing found the exact `text?` loss: non-bootstrap native
  source selection replaced `text?` with `text` before parsing. Normal native
  parsing now preserves source; bootstrap-only compatibility rewriting is
  unchanged. Focused unit and native flat-Option gates pass, and higher review
  accepted the root fix.
- The wider cross-module fixture then exited `6`. Disassembly proved Option
  mapping and single receiver evaluation were correct; the unannotated integer
  module counter was declared `Any`, stored raw `1`, and compared with boxed
  `1`. Bare integer-literal module vars now infer `i64`. Its focused MIR test
  passed and higher re-review passed.
- The refreshed incremental build passed Stage2/3 sanity without full bootstrap.
  Stage2 SHA-256:
  `42391ee607aa8e243d9222afc1021e1f03f426c5701ea17591d63f4037662f78`;
  Stage3 SHA-256:
  `8641e1d637db3c8012a2b1a8b203f67f99ecce45a3c884cb8ed6cd9c1906aae8`.
- The unchanged cross-module fixture advanced beyond exit `6` and now exits
  `7` at `cross_target_nested_copy_ok()`. This is an independent value-copy
  blocker. The three-cycle cap is consumed; do not rebuild or rerun it in this
  session. Stage4, QEMU, filesystem Clang/Simple, web, and DB remain gated.
- Required broad checks could not provide evidence: the minimal Stage3 does
  not expose `check`/`test`, while the canonical `bin/release/simple` CLI
  segfaulted (exit `139`) on `src/compiler`, `src/lib`, MCP, LSP-MCP, and the
  MCP stdio integration spec. Direct-env working-tree guard, spec-layout zero,
  and `git diff --check` passed. This commit is a focused fix, not verify PASS.

## 2026-07-24 continuation status

Goal status: `implementation-blocked-stage4`.

Current evidence requires artifacts and transcripts in this checkout:

| Requirement | Current status | Authoritative boundary |
|---|---|---|
| Stage 4 prerequisite | BLOCKED | One guarded full-CLI build reached the 16 GiB cap after 103/1,314 files. |
| REQ-001/002 RV64 web+DB | HISTORICAL PASS; CURRENT UNVERIFIED | The July 11 real HTTP and `codex-41` query evidence is credible, but the current stamped ELF, serial log, and DB transcript are absent. |
| REQ-003 Clang | HISTORICAL PARTIAL; CURRENT FAIL | Filesystem Clang emitted a real x86-64 ELF object under OVMF; no in-guest link or linked-ELF execution passed. |
| REQ-004/005 Simple roles | HISTORICAL PARTIAL; CURRENT FAIL | Later ring-3 filesystem interpreter evidence supersedes the earlier `rt_string_join` fault, but current payload/media are absent and compiler/loader compile-link-run proof never passed. |
| REQ-006/007 loader provenance | SOURCE PASS; CURRENT LIVE UNVERIFIED | Source contracts reject preload/marker substitution; no current live image proves the complete goal. |

The selected Stage 4 ownership boundary is one compact
`ModuleSurfacesByName` index plus at most one ordinary full-body rich Module
and retained trait-default subtrees. Frozen interfaces:

- `ModuleSurface`
- `ModuleSurfacesByName`
- `module_surface_from_module`
- `hirlowering_for_module`
- `phase2:surface:file:released`

The low-memory entry-closure flow is:

1. Parse each source, install an independently owned compact surface, remove
   the rich Module from retained compiler state, and emit the post-scope
   release marker.
2. Parse each source again, lower HIR against the complete surface index, and
   remove its rich Module before continuing.
3. Retain HIR for the existing MIR layout prepass and later phases.

Required RED-to-GREEN gates before another Stage 4 build:

- Surface extraction omits ordinary executable bodies while retaining
  imports/exports, callable/type/enum/impl signatures, constant names, and
  trait defaults.
- A native forward-import fixture resolves a re-export, enum payload, and
  imported trait default without source-order dependence.
- The first 10 validated post-release real-closure markers average at most
  25,000 retained heap objects/file under a pre-calibrated guarded run.

After these pass: build incremental Stage 2/3, admit one guarded Stage 4, then
reproduce RV64 web/DB, filesystem Simple, and finally extend filesystem Clang
from object emission to in-guest link and execution. Do not start
target/media/QEMU work before Stage 4 admission; existing historical runs are
not current evidence.

Cooperative review for this continuation:

- Lower-model lanes: surface/resolver inventory, real-corpus slope gate,
  RV64 web/DB history, Clang filesystem history, and Simple role history.
- Merge owner: root Codex agent.
- Final reviewer: highest-capability Codex reviewer before each broad merge
  and any done mark.
- Manual steps remain:
  `step("Boot SimpleOS with filesystem-backed web and DB servers")`,
  `step("Compile and execute a filesystem C program with Clang")`, and
  `step("Launch the Simple compiler toolchain from the filesystem")`.
- Temporary helpers must call `fail(...)`; placeholder passes are forbidden.

### Stage 4 design freeze

Highest-capability review selected an explicit `ModuleSurface` contract and
rejected a body-stripped `Module`. Frozen helper types are
`ModuleSurfaceCallable`, `ModuleSurfaceComposite`, `ModuleSurfaceEnum`,
`ModuleSurfaceTrait`, `ModuleSurfaceImpl`, and `ModuleSurfaceConst`.

Only imported trait default bodies and enum struct-field default expressions
retain executable AST. Imported traits are canonically keyed by
`module_name::trait_name`, independent of local aliases; identical imports are
idempotent and conflicting metadata fails. Each unique physical source owns one
surface and its aliases reference it. Composite surfaces retain identity only.
Every surface binds source index/path/module/content length/content hash, and
the second parse fails closed on mismatch. `ModuleSurfacesByName` is the single
resolver contract across all HIR paths; non-streaming paths derive it from
retained rich modules without reparsing.

`driver_streaming_surface_enabled` is true only for Stage4 AOT +
entry-closure + low-memory + `SIMPLE_BOOTSTRAP_STAGE4=1` and a non-VHDL
backend. All other execution modes retain current behavior.

The bounded-memory `NFR-001` gate computes from the first 10 unique ordered
post-release markers, requests process-group termination at marker 10, and
requires average retained growth at most 25,000 objects/file. A raced later
marker is diagnostic. This gate is prerequisite to current `REQ-001` through
`REQ-005` evidence.
