# Verification: SimpleOS filesystem toolchain and servers

Date: 2026-07-11  
Reviewer: normal/highest-capability Codex merge owner

- [PASS] REQ-001: a current zero-weak pure compiler built the stamped RV64
  kernel (`788a224c...`). One QEMU boot returned HTTP 200 for `/health` and `/`,
  with the expected JSON and HTML content types.
- [PASS] REQ-002: the same current QEMU boot attached storage, verified NVFS,
  and passed real DB CREATE/INSERT/SELECT with the inserted value `codex-41`.
  The retained-evidence checker passed `serial_live_request_path_ready`,
  `db_create_insert_select_ok`, and `simpleos_rv64_db_server_connected`.
- [FAIL] REQ-003: exact-path PT_LOAD streaming and the complete guest
  compile/link/execute wrapper are present. Embedded LLD rebuilt and the static
  guest Clang relink has `_start`, zero undefined symbols, and SHA-256
  `f5bb5e75f5b8bc7abb25c7b0b8baf49aa817381799490b0b3a2ccb4d667aa22b`.
  The current pure compiler now reaches QEMU: CPU-v1 forwarding removes the
  BMI2 fault, PMM/VMM and a real user address space initialize, and the exact
  ELF is parsed. The capped final run fails on a backward FAT stream read at
  file offset 4096, so no guest-produced object/link/run transcript exists.
- [FAIL] REQ-004: install-image staging rejects marker payloads and checks target
  provenance, but no complete target-native Simple CLI payload exists.
- [FAIL] REQ-005: no in-guest filesystem `/usr/bin/simple --version`,
  interpreter hello, or native compile/run transcript exists.
- [PASS] REQ-006/007 source contract: the x86_64 path opens the requested FAT32
  path, streams bounded PT_LOAD ranges, builds SysV argv/envp, and keeps legacy
  blob input explicit. Fake/stale payload and malformed DB/Clang evidence gates
  fail closed.
- [PASS] Cooperative review: parallel runtime/archive, loader, DB ABI, Clang
  object, artifact, and source-gate audits were merged by the highest-capability
  reviewer. Two incorrect diagnoses (DB state loss and the Clang 0x4bf672 fault)
  were rejected from retained evidence.
- [PASS] Focused source evidence: the runtime archive selector regression test
  passed before the shared checkout reset; scoped diff checks passed. A newer
  external stage3 timed out on `-c 'print(1 + 1)'` and was correctly rejected.
- [FAIL] Build/runtime: follow-up diagnostics fixed the nil bootstrap-HIR Option
  extraction and missing shared `local_is_float` MIR predicate. Cache-preserving
  dynload then completed stage2/stage3 with zero weak/undefined symbols. The
  capped full-CLI cycle exposed three dedented terminal operands in
  `access_cli_grammar.spl`; the minimal indentation-only fix passes the Rust
  bootstrap-seed module check. A post-fix full CLI and live QEMU evidence still
  do not exist, and no additional build cycle was started this turn. See
  `doc/08_tracking/bug/simpleos_clang_fs_pure_compiler_native_build_2026-07-11.md`.
- [PASS] Focused pure compiler/kernel build: cache recovery produced a fresh
  stage2 compiler with zero uppercase weak definitions and `native-build
  --target`; it compiled all 257 modules of the current x86_64 filesystem-exec
  kernel with zero failures. Kernel SHA-256 is
  `d247013b1c07036350ed15b4b3d9b3f5e70a0b3d8a7066be489b5ad593897626`.
- [FAIL] Full CLI and Clang runtime: strict stage4 rejects real unresolved
  optional-runtime/entry-closure symbols instead of emitting thousands of weak
  fallbacks. The corrected native writer now produces a valid FAT32 image, and
  QEMU streams and validates the exact 122,233,168-byte Clang ELF. CPU policy
  now reaches both Rust and pure native-build entrypoints; the final kernel
  (`7995a823...`) reaches PMM/VMM, user-AS creation, and PT_LOAD mapping before
  the first backward stream read fails. The source now serves the retained
  64-KiB prefix from memory and keeps later disk reads forward-only, but the
  attempt cap prevents another live run this session.
- [PASS] Native file-byte ABI: core-C read now returns a tagged packed byte
  array and write matches codegen's four-argument path/data ABI. The native
  writer executed successfully and its BPB/signature passed the guest reader.
- [WARN] Integration state: a concurrent session bulk-reset the shared checkout
  at 06:08:13 UTC. Reviewed restoration is preserved in detached worktree
  `build/worktrees/simpleos-filesystem-goal`; it is not yet integrated into the
  unstable shared checkout.
- [PASS] Guided sidecar review: three focused Spark lanes audited the target
  entry, SMF execution, and image producer. The primary high-capability review
  accepted the focused compiler-driver entry and exact provenance changes, and
  rejected the compatibility SMF path because it synthesizes code/address and
  never calls `main`.
- [FAIL] Simple filesystem compile/run: the full desktop CLI closure is proven
  overbroad (942 unresolved target symbols), while the focused tool source check
  was CPU-bound and terminated at 120 seconds. More importantly, no production
  filesystem SMF executor currently reaches real executable memory and invokes
  the entrypoint. No target ELF or QEMU PASS is claimed.
- [PASS] Native tool prerequisites: reviewed static SimpleOS Clang, LLC, and
  LLD each have `_start` and zero undefined symbols. The focused compiler now
  uses mounted source, direct guest processes, the staged target sysroot, and
  native ELF output; the rejected SMF compatibility path is gone.
- [FAIL] Focused target closure: the single final strict build reached LLD but
  retained 397 external missing symbols. Required filesystem ABI functions are
  mixed with unused generic backend/JIT/CUDA/SQLite surfaces because the driver
  is still linked at broad module granularity. No target Simple ELF or QEMU
  evidence exists; weak/zero stubs were not accepted.
- [WARN] Closure root fix: Cranelift now emits one discardable section per
  function/data object, matching the existing strict LLD GC design. The focused
  regression did not run: an overbroad Cargo invocation exhausted disk, and the
  corrected lib-only invocation then lost output directories to concurrent
  workspace cleanup. Source review passes; runtime verification is pending.
- [FAIL] Target runtime correctness: reviewed live-call traversal found 32 real
  ABI gaps after optional backend branches are removed. Dictionary text-key
  dispatch and enum discriminant checks are also currently incorrect. Only the
  real libc-backed `rt_getpid` fix is complete; no live compiler claim is made.
- [PASS] Section/root diagnosis follow-up: the discardable-section unit test
  passed, and fresh section-aware stage2/stage3 compilers built successfully.
  Relocation review proved live dispatch branches, not section emission, were
  retaining the optional backend families.
- [WARN] Simple-core follow-up: target archive ABI completeness passes after
  Dict/enum, string-builder, FS/path/time/process, and exec argv/PATH work. The
  corrected combined behavior probe was not rerun after its three-cycle cap.
- [FAIL] Focused-dispatch link: replacing `CompilerDriver` with a standalone
  concrete interpreter and parse/HIR/MIR/LLVM facade reduced 397/500 unresolved
  symbols to 15. The final objects are `/tmp/.tmpffD0yH`; no target ELF or QEMU
  evidence exists.
- [PASS] Focused target ELF: the remaining owner defects were repaired without
  weak stubs. A strict fresh build compiled 616 modules with zero failures and
  produced a static x86-64 SimpleOS ELF (SHA-256 `10d52ba...`).
- [WARN] Filesystem launch: current QEMU resolves `/USR/BIN/SIMPLE`, streams and
  maps all PT_LOAD segments, builds `argc=2`, and enters ring 3. Guarded CRT0
  fixed the first live BSS overrun; a subsequent run reached `--version` and
  exited zero, but did not emit the version because string allocation lacked a
  registered standalone heap.
- [FAIL] Production user heap: the third capped run attempted the existing
  64 MiB standalone heap contract but exhausted page mappings at page 5065 and
  failed before entry. No version text, interpreter, native compile, or compiled
  ELF execution PASS is claimed.
- [PASS] Heap root-cause review: three guided audits plus highest-capability ELF
  accounting proved page 5065 was PMM self-corruption, not capacity exhaustion.
  The stale `0x14000000` bound let allocation overwrite `g_pmm`/`g_vmm`; actual
  linked `_kernel_end` is `0x16f51000`.
- [WARN] Heap root fix: production now uses linker-derived kernel bounds and the
  real 512 MiB QEMU default while retaining the proven 64 MiB heap. The focused
  source regression exists, but its stage2 interpreter run was stopped after
  90 seconds without diagnostics and the capped QEMU proof was not repeated.
- [PASS] Live heap/loader follow-up: a fresh QEMU cycle maps the real Simple ELF,
  all PT_LOAD pages, 64 MiB heap, 32 stack pages, and an argc=2 startup frame,
  then enters ring 3. Raw linker-boundary ABI is fixed at the shared C owner.
- [WARN] CLI argv follow-up: the live CLI still printed usage because mutable
  SimpleCore module globals compiled to a no-op setter/constant-zero getter.
  Argument state now resides in SimpleOS libc; the rebuilt target ELF calls the
  setter/getters and links cleanly, but the three-run cap prevents a fourth boot.
- [FAIL] CLI dispatch follow-up: after moving full argv conversion into libc,
  the final capped boot enters ring 3 with an exact argc=2 startup frame but
  treats `--version` as a source path. It performs null-argument filesystem
  syscalls, prints an empty `error:`, and exits 1. Frame construction and libc
  array creation are live-proven; runtime text identity/dispatch is not.
- [PASS] Filesystem Simple version: the canonical FAT `/USR/BIN/SIMPLE` now
  prints exact `Simple v1.0.0-beta`, exits 0, and produces expected QEMU rc 3.
  The root fix aligns the shared kernel `RuntimeString` ABI at data offset 16.
- [FAIL] Filesystem Simple interpreter: the guest opens and reads the real
  `/HELLO.SPL`, but the first boot faulted in generic string indexing. The
  shared index dispatch and safe zero-state parser-length boundary are now
  implemented; the capped final target link preceded the rebuilt libc archive,
  so post-fix host/QEMU evidence is pending.
- [WARN] Interpreter host follow-up: the rebuilt focused target advances past
  filesystem text, string indexing, lexer token offsets, and raw token equality.
  Its final bounded smoke exposed zero-BSS declaration arenas; reset owners now
  create fresh AST/expr/stmt containers, but this newest source is not rebuilt.
  No interpreter PASS is claimed.
- [WARN] Interpreter host follow-up 2: reset-owned arenas and newline tokenizing
  now pass the bounded host path; the target parses the hello source and exits 0.
  It produced no output because interpreter dispatch required a redundant symbol
  table `main` before examining valid HIR functions. Source now invokes the HIR
  function named `main` directly; post-fix runtime evidence is pending.
- [WARN] Interpreter host follow-up 3: breakpoints prove direct HIR `main` and
  builtin print execution. `rt_println_value` receives nil because nested
  `Ok(Value.String(...))` drops the payload in stage4 AOT. String literal enum
  construction is now hoisted, but the capped artifact predates this fix.
- [PASS] Interpreter host follow-up 4: explicit typed `Result<Value,
  BackendError>` extraction at the call-argument boundary rebuilt cleanly (616
  modules, zero failed). The target ELF prints exact `Hello from SimpleOS` and
  exits 0 on the host; SHA-256 is
  `95f2dc26b00f47f83e097fc4f4be1d3fee76cef8de9eaf2ae38a885e0378409d`.
- [FAIL] Filesystem interpreter follow-up: the fresh production QEMU attempt
  streamed `/USR/BIN/SIMPLE`, mapped its PT_LOADs, built argc=2, and entered
  ring 3, but timed out after a first-stack-read page fault. Higher review of
  the complete serial order found the causal earlier `ud2` at
  `_alloc_table_page`: stage4 loses the `Option<PageFrame>` payload, and the
  recovering fault hook then continues with corrupt page tables. The shared
  raw-scalar `pmm_alloc_page_raw()` path is the next bounded fix; NX/W^X remains
  correct and must not be weakened. Kernel SHA-256
  `b3686b3d8c045b925a6c6577ba52e736c9e2d68413a4029fbfb2ba010e55bdd4`.
- [PASS] Filesystem interpreter: `_alloc_table_page` now uses the existing raw
  PMM scalar path. A fresh kernel (SHA-256
  `ee07b61044a8f3afd96c44b4b07be42c4cb4aec1a014a170a353d577c20856ab`)
  streamed `/USR/BIN/SIMPLE`, read `/HELLO.SPL`, printed exact
  `Hello from SimpleOS`, exited 0, and returned expected QEMU rc 3.
- [WARN] Filesystem Simple emit-object: the CLI and filesystem profiles now
  expose `compile --emit-object`, a staged Simple entry shim, direct
  `/USR/BIN/LD.LLD` linking, and `/FSEXEC.ELF` execution. The first live emit
  attempt opened the real source but exited 1 before LLVM/LLC: stage4 corrupts
  `mir_lowering.errors[0]`, masking the real MIR diagnostic. The final capped
  rebuild hoists `CompiledModule` before `Result.Ok`; no post-build QEMU PASS is
  claimed. See the focused bug report.
- [WARN] Emit-object root fix/build: GDB proved no MIR diagnostic was produced;
  inline composite empty literals created Dicts for `loop_stack`/`errors`.
  `MirLowering.new` now installs typed empty arrays, and `CompiledModule` is
  hoisted before `Result.Ok`. Three bounded build attempts did not produce a
  new target: one broad 98-file timeout storm and two zero-cache Btrfs-contention
  runs while 14+ concurrent native builds occupied the 99%-full filesystem.
- [FAIL] Ring-3 provenance: higher review proved the LSTAR return heuristic
  classified user RIP `0x20xxxx` inside `[0x100000,_kernel_end)` and returned
  via a CPL0 jump. Kernel-internal `rt_x86_syscall` now calls the existing
  dispatcher directly and LSTAR always constructs CS `0x2b`/`iretq`, but this
  security fix is not yet rebuilt/live-proven. Earlier interpreter output is
  behavior evidence, not valid ring-3 isolation evidence.
- [PASS] Ring-3 interpreter revalidation: cache-backed target rebuild compiled
  616 modules with zero failures (SHA-256
  `e27d5e534cbdc8a23693c9b4a8af7ba3fee49d1d0bd20442687419980c0567bd`).
  Fresh kernel SHA-256
  `0c6f70972ddcc6eeea686da0e0901827894b2bca272ca05739a771b9bd19cc81`
  enters at CS0x2b, reads mounted `/HELLO.SPL`, reports exact post-read
  `cs=0x2b cpl=3`, prints `Hello from SimpleOS`, exits 0, and returns QEMU rc3.
  Kernel-internal calls now bypass LSTAR, eliminating the low-user-RIP
  privilege escalation.
- [FAIL] Direct emit-object boundary: a fresh CPL3 boot read `/HELLO.SPL`, then
  `compile_ir_to_object` attempted fork/wait syscalls 57/61, received ENOSYS,
  faulted in user mode, and timed out without `/HELLO.O`. Implementing fork or
  multi-output RAMFS was rejected as unnecessary scope.
- [WARN] Staged compiler pipeline: Simple now supports in-process
  `--emit-llvm`; images can stage `/HELLO.LL`; a dedicated profile launches
  filesystem `/USR/BIN/LLC` with the existing release flags; subsequent LLD
  and `/FSEXEC.ELF` profiles remain. LLVM headers now honor `self.target`, the
  Simple entry shim no longer requires nonexistent `spl_init_args`, and the
  staged runtime owns raw `rt_print`/`rt_println`. The cache-backed target
  rebuilt with 3 compiled/613 cached, zero failed (SHA-256
  `63b362e327b58ba7718e8f42e446a4ec73e6d058313ff53639bf1d433345e71b`),
  but the new staged profiles are not live-proven yet.

STATUS: FAIL (REQ-003 through REQ-005 remain release blockers)

Next proof order: run guest emit-LLVM with CPL3 markers, reconstruct and stage
the named IR, run filesystem LLC and validate the named ELF REL object, then
run LLD/reconstruct/restage/execute; continue Clang afterward.
