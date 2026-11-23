# Phase-2 Cross-Compile Progress: lint + test runner (2026-11-23)

Goal: cross-compile Simple's lint and the test runner with the phase-2 builder
for every OS/CPU, with both the native linker (lld) and the Pure Simple linker.
Toolchain: clang + lld, llvm-mingw UCRT on Windows. No GCC, libgcc or MSVC.
Base matrix: `cross_compile_linker_matrix_2026-11-17.md`.

Legend: ✅ done · 🔧 WIP branch pushed · ⏳ not started · ❌ blocked

## Windows continuation (2026-11-23, implementation pending runtime admission)

### Independent prerequisite collection

Run `45126119817` passed resolver qualification and reached Phase-2 planning
(`selected=1623`), then refused the mandatory worker pool because the CI build
prefix set `SIMPLE_PARSE_SHARDING=0` (`hir_workers=0`). The next-phase,
essentials and seed-native prefixes now enable ordinary sharding, retaining
the thread budget and admission checks. The old policy fails its wrapper
contract; the corrected policy passes. Manual `max_rung=1` now bounds a
dispatch to one next-phase attempt; the existing default remains four.
The new budget contract covers 270 event/input/dependency combinations.
These are wrapper contracts; real P2/P3 proof is still pending.

The checker correction landed as PR #11009; the native-long and independent
`size_t` limits correction landed as PR #11014. The remaining compiler PR is
#11010 and stays draft. Astra's preliminary review found ARM32 LLVM layout and
pointer-width omissions, missing ARM float-ABI attribute admission, and an
ELF32 physical-load extent check. Those repairs and focused regressions are
authored; runtime execution and final exact-head Astra admission are pending.

GitHub run `45117792074` produced only `linux-x86_64-p1/PHASE=1`, with CLI/test
essentials explicitly `not-built` below Phase 3. Its attempt receipt says
`admission: none`; the retained seed SHA-256 is
`43b5261fc229f57e5e20dd64b08b6c6bf89a103f78f244fe858960c9704f8295`.
Do not use this Rust seed for SSpec or tool acceptance. Rungs 2, 3 and 4 failed
before Phase-2 compilation because the resolver staged Hello outside the
checkout and SCV rejected its source inventory. The resolver repair stages
unique source probes inside the caller checkout, retains separate unique
outputs/cache/logs, and requires a zero exit plus an exact stdout marker.
Mock wrapper contracts cover the security boundary and rejection cases only;
actual compiler qualification must be repeated by the canonical owner on the
changed implementation. Preserve the Phase-1 handoff instead of rebuilding it.

All three `simpleos-sysroot-32.shs` rows (i686, arm32, riscv32) built with
Scoop LLVM. The builds exposed undefined native-word arithmetic in
`simpleos_cxxabi.c`: two shifts by 33 on a 32-bit unsigned long. The repair
keeps the 64-bit mixer and ABI unchanged and uses a 16-bit shift for ELF32;
the matching Simple helper has explicit width/truncation regressions.
All six target C compilation rows passed `-Werror=shift-count-overflow`.
The original and repaired optimized x86_64 `.text` both hash to
`5013826d6f3d77412a7a6299bb10d05dd892b7d3c96293fcae2bef99101d0867`.
Local evidence: `build/verify/xc-sysroot-*.log` and
`build/verify/cxxabi-canary-width/`. These are prerequisite C builds, not
Simple runtime test or lint/test-runner acceptance.

The same ELF32 builds exposed hardcoded LP64 `LONG_MIN`/`LONG_MAX` values in
`limits.h`, narrowing `strtol` overflow clamps to 0/-1. Bounds now follow
Clang's native-long type. A C interoperability fixture checks compiler-evaluated
types and ranges, driven by `simpleos_native_long_limits_spec.spl`; seven
direct ABI compilation rows (including LLP64) passed, and all six SimpleOS
`simpleos_stdlib_ext.c` rows passed narrowing/overflow-as-error compilation.
The old header fails the i686 fixture. Local evidence is under
`build/verify/native-long-limits/`; the Simple spec itself remains TEST_BLOCKED.
The static RV32 user linker now also invokes the width-aware ALIGN normalizer
instead of retaining its former ELF64-only rejection; the real internal-link
regression is authored, with its instruction/data oracles independently linked
by LLD. Source review found no remaining proven P0/P1 in these repairs.

The real guest audit found no current six-CPU tool execution adapter.
`run-simpleos-qemu-guest-evidence.shs` is contract-only; Linux-target
qemu-user framebuffer probes do not establish SimpleOS tool execution.
Filesystem-exec routes must bind the exact tool ELF and authenticated media,
pass arguments, and collect stdout/exit results. The 32-bit sysroot archive
currently provides libc/CRT only; Simple runtime closure remains required.
The manual kernel gates are explicitly registered outside fast push gates,
with their compiler/tool prerequisites; this is not an admission exemption.

The isolated continuation workspace is `C:/dev/simple-xc-handover`; unrelated
changes in `C:/dev/simple` are preserved. The remote handover was fetched at
`cbfc51393ef`. The compiler changes below are authored, not admitted results.

- The matrix now requests both `lld` and `internal`, separates engine caches,
  archives and outputs, includes all six SimpleOS CPU rows, and uses LLVM for
  ELF32. Its 37 checker self-tests passed with MSYS2. BLOCKED rows and missing
  execution adapters prevent PASS, including in dry runs.
- The arm64 comparison gate rejects failed reference builds and reused
  `_stubs_freestanding.o` providers. Both negative paths were exercised.
- Compiler work connects i686/arm32/RV32 user sysroots and LLVM ELF targets,
  internal ELF32 module-init wrapping, boot ELF32 headers/ABI/range checks,
  and RV32 ALIGN normalization. A review found ALIGN reparsing discarded
  wrapped symbol names; the repair and RV32/RV64 regressions are authored.
- Independent LLVM fixture links establish instruction/ABI/layout oracles;
  they do not execute the modified Simple linker or the requested tools.

`TEST_BLOCKED`: this host has no deployed self-hosted compiler under
`bin/release/<triple>/simple`, and WSL is not installed. The historical Windows
seed path is absent. Do not use `bin/simple.exe` as substitute acceptance.
GitHub bootstrap run [45115433408](https://github.com/ormastes/simple/actions/runs/45115433408)
requests the Linux lane from the original handover with `publish=false` and
was queued at the last observation. It does not test the unpushed compiler
edits. Disk space is no longer a blocker on this host (over 2 TB free).

Completion still requires an admitted compiler, execution of changed and
existing linker/target specs plus mandatory core/MCP checks, actual lint and
test-runner builds with each linker, target execution evidence, x86_64 kernel
closure, and reviewed merged PRs. None of the original kernel/Hello table
marks below should be read as Phase-2 lint/test-runner acceptance.

## Follow-up evidence snapshot (2026-11-23)

This snapshot supersedes the original handover tables and remaining-work list
below where they differ. Those sections are retained as Claude's original cut.
Checked the remote handover ref, local cross-compile worktrees, retained build
logs, and GitHub PR state. No running Claude process was visible on this host;
this does not establish the state of a session on Windows or another host.
No new compiler builds or test runs were performed for this documentation update.

| Lane | Observed progress | Remaining / admission limit |
|------|-------------------|-----------------------------|
| SimpleOS riscv64, lld | [#10972](https://github.com/ormastes/simple/pull/10972) merged into `release/1.0.0`; PR records link-only PASS, 0 undefined, 209940392-byte ELF, and soft-float tests 7/7. Retained `/private/tmp/xc-out-rv64-link/kernel-build.log` confirms 32 compiled, 0 failed and successful link. | Link-only evidence with LLVM 23.1.1 bootstrap seed; no boot/runtime or phase-2 lint/test-runner claim. The fixes are not incorporated into this handover branch by this docs-only commit. |
| SimpleOS x86_64, lld | [#10994](https://github.com/ormastes/simple/pull/10994) is open, non-draft; branch `work/ssos-x64-kernel-link-fix-20261123`, commit `80d7a8eabfb`. PR records 926 modules compiled, 0 compile failures and 9 OS unit specs passed. | Link still fails: 52 entries in retained `xc-out-x64-link/undefined.txt`, including runtime/GPU symbols and `RenderBackend.read_pixels_region`. Review and resolve before claiming gate PASS. |
| SimpleOS arm64, Pure Simple linker | Uncommitted staged/unstaged work in `/private/tmp/wt-xc-a64-simple-link` on `work/a64-simple-link-gate-verify-20261123`; gate, CLI, linker scripts, linker implementation and fixtures are being changed. | Retained `/private/tmp/xc-out-a64-simple/simple-link.log` ends with orphan section `,.text.simple.0` in `object3.o`. The lld comparison built an ELF, but its retained object list includes `_stubs_freestanding.o`; this does not admit a strict no-stub Pure Simple link. |
| Windows i686 PE layout | [#10992](https://github.com/ormastes/simple/pull/10992) merged; PR records all 19 `coff_*` / `pe_*` unit specs passing with LLVM 23.1.1 seed. | Section merge/order parity fix landed; no new evidence here that lint/test runner cross-link and run. |
| Windows GNU compiler selection | [#10995](https://github.com/ormastes/simple/pull/10995) merged; arch-matching llvm-mingw selection rejects an MSVC-target clang ahead on PATH. | Compiler-selection defect addressed; target-width process/image owner ABI work remains unverified. |
| Bootstrap seed section/cfg fixes | `/private/tmp/wt-xc-seed-fixes`, branch `work/seed-xcompile-section-and-cfg-20261123`, has dirty `backend_core.rs` and `cond_compile.rs`. | Uncommitted work; no admission or completion inferred. Preserve this lane separately. |

Next actions: resolve the arm64 orphan-section failure and verify the strict
no-stub gate; finish x86_64 runtime closure/link defects and review #10994;
verify Windows i686 owner ABI and actual lint/test-runner execution; then resume
the outstanding Linux/FreeBSD and SimpleOS userland phase-2 matrix. The original
Linux/Windows matrix marks below were not independently reverified in this pass.
Local `/private/tmp` evidence paths are host-local and may later be removed;
the linked merged PRs retain the reported validation provenance.

## Native linker (lld)

| OS | x86_64 | i686 | arm64 | arm32 | riscv64 | riscv32 |
|----|--------|------|-------|-------|---------|---------|
| Linux | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Windows | ✅ | 🔧 hello ✅; lint/test runner blocked (PR2) | ✅ | — | — | — |
| SimpleOS kernel (0 undefined) | ❌ source defects | ✅ #10905 | ✅ #10923 | ✅ #10882 | 🔧 8 → ~1 left | ✅ #10905 |

## Pure Simple linker

| OS | x86_64 | i686 | arm64 | arm32 | riscv64 | riscv32 |
|----|--------|------|-------|-------|---------|---------|
| Linux | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Windows | ✅ | 🔧 hello links + runs; lint/test runner ⏳ | ✅ | — | — | — |
| SimpleOS kernel | ✅ | ✅ (#10841 i386 boot link) | 🔧 gate WIP (#10912 aarch64 support) | ⏳ | ⏳ | ⏳ |

## Landed this round (release/1.0.0)

- #10853 `rt_interp_call` argv is `const uint64_t*`
- #10882 arm32 kernel shims → 0 undefined
- #10886 shared `arch/common/rt_value.spl`
- #10895, #10911 i686 Windows pointer-as-i64 codegen fix (hello prints)
- #10899 arm64 `rt_string_free`
- #10905 shared scalar shims; riscv32 + i686 → 0 undefined
- #10912 aarch64 in the Pure Simple kernel linker (`elf_boot_link.spl`)
- #10923 arm64 `rt_unwrap_or_value` → 0 undefined
- #10939 (`cc26757109c`) `@abi("system")` = stdcall on i686 Windows

## WIP branches on origin (unverified, continue from these)

| Branch | Content | Next step |
|--------|---------|-----------|
| `work/ssos-x64-rv64-link` | riscv64/x86_64 kernel link gates, soft-float `__fixdfdi`/`__floatdidf` (`arch/common/soft_float_conv64.spl`), PMM page export, `os_entry` keepalive imports, x86_64 bug doc | Run riscv64 gate with the LLVM seed, `--link-only`, `SIMPLE_NO_STUB_FALLBACK=1` → 0; check `rt_pci_is_virtio_gpu` export; x86_64 gate must report ERROR; Opus review; PR |
| `work/a64-simple-link-gate-20261123` | `check-simpleos-arm64-simple-link.shs`, `elf/boot_link_cli.spl`, aarch64 fixtures; `boot_link_cli_spec` 7/7 pass | Run gate for the real undefined count; fix leftovers; Opus review; PR |

## Remaining

1. **Windows i686 PR2:** target-width pointer slots in `windows_process_owner_abi.spl`
   and `windows_image_owner` (currently x86_64-only). After that, cross-link lint and
   the test runner with lld and the Pure Simple linker, and run them.
2. **Windows i686 todos:** the seed picks MSVC clang for i686; differences between the
   PE writer and lld.
3. **SimpleOS riscv64:** finish the gate (branch above).
4. **SimpleOS x86_64:** missing `x86_64_auth_trust_config` and `os.drivers.framebuffer.fb_font`,
   HIR errors, `--entry-closure` does not narrow the build. Bug doc is on the WIP branch.
5. **SimpleOS Pure Simple linker:** arm64 gate (branch above); `elf_boot_link` support for
   arm32, riscv64 and riscv32.
6. **Linux / FreeBSD lint + test-runner phase-2 runs** on WSL for every CPU (32/64-bit),
   and the SimpleOS 32/64-bit userland runs.
7. **Fable common-rt/HAL plan:** hal_iface, hal_impl per arch, then the families.
8. **Infra:** C: free space (keep ≥15 GB; about 19 GB at the cut); WSL `ext4.vhdx` needs an
   admin `diskpart compact`.

LLVM seed used by the gates: `C:/dev/wt/rtval-target-ut/release/simple.exe` (built from e0fc6622375).

## Continuation: terminal P2 attempt and release sync (2026-11-23 08:32 UTC)

- Run `45128297579`, Linux job `137537650345`, finished **FAILURE**; source was frozen at `3b51e37a2c1322c644ccaaae3c6c6e3d928ede19`. Receipt records `role: planning`, `exit_status: 1`, `admission: none`. No P2 handoff exists, so P3 has not started.
- First concrete parse failure: `src/compiler/10.frontend/core/parser_identifiers.spl` has supplied surface identity `compiler.core.parser_identifiers` but path-derived identity `compiler.frontend.core.parser_identifiers`. Later worker ledger failures do not establish independent causes; naming/provider diagnosis is in progress.
- Retained diagnostics and native cache: `build/verify/p2-sharded-attempt-45128297579/diagnostics/`; receipts in sibling `receipts/`. Preserve compatible successful artifacts; do not repeat the unchanged failed attempt.
- Release fixes through `660c538d7c77` integrated into this isolated work branch. Rebased capture commit is `34b91752708`; pre-sync history is retained at `refs/codex/xc-before-release-sync/bacd37855de`. Tracked count increased 151229 to 151251, with no tracked deletions. New release x64 link gate/report retained over older copies; it still reports 52 unresolved symbols, not a linked kernel.
- Authenticated installed-tool probe and canonical serial capture are implemented and source-reviewed by Astra with no remaining P0-P2 findings. New/updated specs remain **UNEXECUTED**, with runtime qualification blocked. Source review is not final merge admission.
- Genuine guest adapter additionally requires the currently unavailable measured-boot/entropy capability owner (`src/os/kernel/boot/boot_measurement_entropy_capability_v1.spl`). A configured kernel hash alone cannot prove the running kernel identity. No unavailable-only wrapper or fabricated identity was added.
- Full six-CPU, two-tool, two-linker execution matrix remains 24 unverified combinations. Final runtime checks, P2-to-P3 evidence, exact-head review and PR merge remain pending.
- Independent follow-up diagnostic: MIR lowering also reports `enum match retained Result/Optional has no complete declaration ownership` at `src/compiler/10.frontend/core/_AstExpr/nodes.spl:503:19` (nested `store.get(3)` match). Treat this as a second concrete error family until dependency/ownership diagnosis proves otherwise; do not describe all failed worker rows as a naming cascade.
- Producer boundary confirmed: artifact run `45117792074` is source `5a2f91bde27568dab2fabfced5a8cdda3078f34f`; compiled bootstrap dispatch directly calls parse-shard/native-worker functions. Checkout updates are compiler inputs, not hot-reloaded worker implementation. A fresh Stage-1 producer is required to execute the parse-shard repair. The retained artifact is still preserved with digest `43b5261fc229f57e5e20dd64b08b6c6bf89a103f78f244fe858960c9704f8295`.
- Evidence precision: namespace and MIR ownership messages are two distinct compile-failure signatures, not yet two proven independent root causes. The 18 failed MIR members share a worker batch; only `nodes.spl` carries an individually named MIR failure. A bounded three-fixture bootstrap diagnostic is being prepared before any full P2 retry.
- Exact-producer diagnostic run `45143576150` on `0abba1510a913300a9e8c0bed67e8dde07ebea41` completed successfully. All three controls recorded native compile/link exit 0 and artifact publication, with emitted programs explicitly NOT_RUN and admission none. Each selected only one source module; these results do not verify the real imported AttributeStore/mutable set-get closure or resolve the full-graph MIR failure.
- Fresh producer run `45145173990` started on the same repaired source (`fresh=true`, one rung, four workers, publication disabled). Its actual phase, producer identity and qualification remain pending terminal receipts.
- Scope correction after Astra audit: measured boot/entropy and online per-open reattestation are not required to establish the 24 functional tool/linker executions. The earlier unavailable online owner blocks that chosen admission method, not the entire functional goal. Existing x64 signature/trusted-open/authority-token/authenticated-adoption invariants remain mandatory. The separate pinned-key signed boot-media owner is a viable adapter starting point; no lint/test guest execution has yet been verified through it. RV64 path-only compatibility helpers return -13 and are not qualifying alternatives.
- Independent 64-bit C-provider preparation completed under `build/verify/simpleos-provider-prep-0abba1510a91/`: x86_64 12/12 owned translation units, aarch64 11/11, riscv64 11/11 compile exits 0. Deterministic archives contain separate members with correct ELF64 machines and no duplicate strong globals; non-x86 archives contain no port-I/O member. Per-TU commands, source/tool/archive hashes and symbol inventories are retained. Admission remains none; this is not a complete Simple core-runtime link or guest execution.
- The canonical 32-bit sysroot script currently assembles only libc/CRT and has no architecture-owned C-provider composition equivalent to the 64-bit recipe. A producer-derived symbol/ABI receipt is needed before a complete 32-bit runtime can be claimed. No guessed x86 provider list was copied to another CPU.
- Astra source-reviewed the one real AttributeStore fixture and its 13-file projection: the production factory, mutable set/get sequence and explicit imports are represented. It remains unexecuted. Any later result must retain selected provider module names/source paths as well as module count; a successful projection compile would not resolve the original full-graph failure by itself.
- Fresh P1 handoff from run `45145173990` is verified: exact PHASE `1\n`, compiler 58490592 bytes, SHA-256 `e551d794b3e1f90b920930fc34680d3839945d3b9c352ee2d1dfeab5306fb420`. Retained Hello exit 0, exact `phase-ladder-1-ok\n` stdout, empty stderr. The new authoritative-row planner has a defined native symbol in this compiler. Observation is provisional bootstrap Hello only; worker-pool repair execution and full suite remain pending.
- Commit `c93080d22c4` addresses the two failed structural rows without threshold changes. Official primitive-api and nil-outside-unsafe range checks each PASS for 24 source files. Unchanged green gates were not rerun locally.
- The one real-factory diagnostic workflow is now pinned to the verified fresh P1 and source-reviewed by Astra. It runs only the imported mutable AttributeStore case, not the three already-green controls. Compiler module/path/hash identity, nonempty artifact, raw SCV key versus derived projection path, and incomplete-record outcomes are checked. Execution remains pending.
- Offline guest adapter review repaired source-level VFS handoff ownership, scalar IOPL permissions and independent COM2 completion framing. A remaining P1 is the actual libc/bare-exec write route: syscall 60 discards stdout/stderr descriptor identity and bypasses canonical capture. Guest qualification must fail closed until the actual linked provider and trap path preserve and certify both streams. No guest execution or freshness/online-attestation claim is made.
