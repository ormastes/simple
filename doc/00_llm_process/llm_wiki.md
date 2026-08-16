# LLM Repository Wiki

Short, canonical term resolution for coding agents. Read this index when a user
names a repository capability whose implementation owner is ambiguous.

## StarFive JH7110 software reset over Tigard JTAG

- **Canonical command:** `scripts/os/starfive-jtag-sbi-reset.shs`.
- **Meaning:** load a fixed, reviewed SBI SRST cold-reboot trampoline into an
  allowlisted RAM scratch address through Tigard JTAG, select the proven U74
  hart, and execute the supervisor-mode `ecall`.
- **Why:** generic OpenOCD `reset run` controls a debug hart but did not restore
  the complete JH7110 firmware/SoC state on the tested VisionFive 2.
- **PASS evidence:** a retained UART transcript shows a fresh BootROM, OpenSBI,
  peripheral initialization, and U-Boot sequence; Tigard channel B's kernel
  driver is restored. The `ecall` or OpenOCD exit status alone is not proof.
- **Safety boundary:** never accept arbitrary instructions, payload files, or
  RAM addresses. Use the reviewed fixed trampoline and scratch address; do not
  write QSPI, eMMC, environment, or other persistent storage.
- **Primary guide:**
  `doc/07_guide/platform/simpleos/starfive_visionfive2_simpleos.md`.

### Agent lookup rule

When asked to software-reset or reboot a StarFive JH7110 through Tigard, use
the SBI SRST helper and capture UART concurrently. Do not substitute OpenOCD
`reset run`, a direct PC write, or hardware-reset claims. If the expected fresh
firmware sequence is absent, report reset as failed or blocked rather than
PASS.

## Simple embedded DB / Simple SQLite

- **Canonical meaning:** `std.database.pure_sql.{PureDatabase}`.
- **Implementation:** `src/lib/nogc_sync_mut/database/pure_sql/`.
- **Nature:** SQLite-compatible DDL/DML/query/transaction engine implemented in
  Simple, with memory and disk-backed operation.
- **Use for:** application-owned embedded SQL persistence that must remain pure
  Simple and work without the C SQLite library.
- **Do not substitute:** `app.io.sqlite_sffi`, `std.io.sqlite_sffi`, or another
  `sqlite_*` SFFI facade; those call C SQLite.
- **Do not confuse with:** `std.database.core.SdnDatabase`, the SDN table/row
  persistence layer rather than the SQLite-compatible SQL engine.
- **Primary guide:** `doc/07_guide/lib/database/sqlite_counterparts.md`.
- **Expert note:** `doc/00_llm_process/feature_expert/database_sql/skill.md`.

### Agent lookup rule

When a request says “Simple embedded DB,” “SQLite in Simple,” or “Simple
SQLite,” search `PureDatabase` and `pure_sql` first. Only choose an SFFI SQLite
surface when the user explicitly requests the host C SQLite implementation.

### Execution rule

The caller's mode does not choose the database execution mode. In normal use,
including an interpreter-hosted CLI, MCP, test harness, or plugin, run
PureDatabase through a cached `.smf`/`.lsm` artifact or native database worker.
Direct interpretation of the database hot path is an explicit diagnostic
fallback only. A carrier *plan* or readiness probe is not proof of offloading;
verify that the caller actually crosses the worker/library boundary.

## Bootstrap multi-error recovery

- **Fail-fast:** normal CI/release mode, or one hard blocker prevents later work.
- **Inventory-to-end:** use when a bootstrap exposes many errors, fails one file
  at a time, or the request is to find as many bugs as possible.
- **Inventory rule:** freeze executable/runtime/source identities and a
  deterministic scoped manifest; continue every isolated task to success,
  failure, crash, or timeout before editing. Persist counts, logs, and resume
  state. Prefer `scripts/check/compiled-check-tree.py` with a compiled checker,
  bounded batches, and durable batch/file results; the legacy shell sweep's
  temporary rows are not resumable evidence. If compiled batching is still
  prohibitive, use coarser module/root tasks that cover the complete scope.
- **Fix rule:** normalize first real diagnostics, collapse cascades/duplicates,
  claim unique categories in the bug database, and assign one category per
  parallel agent with isolated caches and non-overlapping owner files. Fix the
  shared root cause across all affected instances, with exact and similar-case
  regression tests.
- **Evidence rule:** retry failed shards first, then one authoritative build and
  produced-CLI feature sweep. Always name compiler, mode, target, host, and
  manifest; seed/static evidence is not a self-hosted Stage-4 pass.
- **Stop rule:** at most three verify/fix cycles. Finish when the manifest ends,
  all categories are fixed or explicitly blocked/unavailable, failed shards are
  green, and the requested artifact passes sanity. Do not rerun green gates.
- **Detailed workflow:** `.codex/skills/unstable-build-fixes/SKILL.md` and
  `doc/07_guide/compiler/build.md#bootstrap-diagnostic-sweep`.

## Bootstrap debug/test observability

- Normal builds are `off`: never add deep HIR/MIR/LLVM scans or AOP traversal
  to the default path merely to improve diagnostics.
- Use `--diagnostics=test` for progress and coarse phase timing without parser
  trace. `simple check --phase-profile <path>` exposes read/parse/lint totals;
  JSON mode suppresses phase records to preserve stdout purity.
- Use `--diagnostics=debug` (bare `--diagnostics`) when detailed trace,
  successful LLVM IR, and memory snapshots are needed. Both modes imply the
  progress watcher; the environment equivalent is
  `SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE=debug|test`.
- AOP call/assignment tracing is a separate, scoped opt-in. Prefer
  `SIMPLE_AOP_DEBUG=<pattern>` and add `SIMPLE_AOP_LOG_CALLS=1` only when the
  weave is the suspected owner.
- Bind isolated sweeps with
  `--diagnostic-child-compiler=/absolute/path/to/simple`; record that child
  identity separately from the seed/driver.
- Guide: `doc/07_guide/compiler/build.md#bootstrap-debug-and-test-modes`.

## Spec run verdict / "did the tests pass?"

- **Canonical verdict for one spec FILE:** the `SPEC FILE VERDICT: <path>
  declared>=N executed=N passed=N failed=N dropped=N` line, emitted on stdout,
  last, by `report_spec_file_verdict`
  (`src/compiler_rust/driver/src/cli/basic.rs:144`, landed `5b57a79f8ba`).
- **Canonical verdict for a `bin/simple test` run:** `Results: N total, M
  passed, K failed` (`src/app/test_runner_new/test_runner_single.spl:225`).
- **`bin/simple run` speaks a DIFFERENT grammar:** `N examples, M failures`
  (`src/compiler_rust/driver/src/cli/test_output.rs:164`), singular `1 failure`
  at `:251`, and it is **ANSI-colour-wrapped**. `test` and `run` summaries are
  not interchangeable and neither pattern matches the other's output.
- **Do not substitute:** `tail -1` of a spec log (that is the last `describe`'s
  count, not the file's), the process exit status (fail-open: an unresolved
  `use` is only a WARN and still exits 0), or a green stdout while the real
  failure line went to stderr.
- **Do not confuse with:** exit 143 (≈60s CPU guard, SIGTERM) and exit 255 +
  `Process timed out` (600s daemon request cap). Neither is a test result. Also
  not a real regression: a `FAIL` whose example count doesn't match any
  visible `✗` assertion, or with stray CLI usage/help text (e.g.
  `Usage: simple_lint ...`) interleaved in the log — that shape is test-runner
  plumbing (session-daemon stale-result cache, or a `fn main` name collision
  between the spec's synthesized entry point and an unrelated tool's own
  `main`), not a code defect. Re-run with `--no-session-daemon` first.
- **Detailed traps:** `.claude/skills/spipe.md` §"Reading the verdict — how a
  spec run lies to you".
- **Layer note:** `doc/00_llm_process/layer_expert/test_runner/skill.md`.

### Agent lookup rule

When a request asks whether a spec, suite, or corpus passes, resolve the answer
from the verdict line named above — never from the exit code alone, never from
the last line of a log, and never from a summary grammar belonging to the other
command. Strip ANSI before anchoring any pattern. Compare `executed` counts
across runs, not only `failed`: a module-load failure drops whole `describe`
blocks at exit 0.

### Vacuity rule

A bare `assert` is inert (`assert 1 == 2` has reported `7 passed`). `check()`
is a real assertion (`.../cli/test_runner/execution.rs:989`), so an
`expect(`-only vacuity scan both misses `check()` specs and mis-scores
`check(true)`. A failing `expect` does not abort the example body and only the
last failure per example prints, so the count of printed failures is a lower
bound on defects, never the defect count.

### Engine-divergence rule: a green interpreter run does not clear the JIT

`bin/simple test` hard-defaults to the tree-walk interpreter and has no JIT
variant, so the whole spec suite is structurally blind to a real, recurring
bug class: an unregistered or mis-dispatched `extern fn` — or an unbox/marshal
fallback with a silent default — returns a wrong-but-plausible value (empty
digest, `0`, `nil`) under **the JIT only**, with no error and exit 0. Confirmed
independently three times in one session (`rt_tls13_sha256` returning an
empty digest and manufacturing a false "JIT is 4x faster" claim since
`"" == ""`; `rt_simd_*_i32x8` misaligned-pointer UB; unbacked `rt_ssh_*`
externs reading as `connected=false`). A digest/hash/checksum comparison that
"passes" via `bin/simple test` alone has not exercised the engine ordinary
`bin/simple run` uses — re-verify with `SIMPLE_EXECUTION_MODE=jit` (or plain
`bin/simple run`) before trusting a cross-engine equality claim.

## Evidence discipline: census, sabotage, and size

- **Census:** raw false-positive rates measured here ran 83.9% (arity), 74% (a
  constant scan actually counting deliberate `FAILMARK`s), 46.2% (dead code),
  and 31.5% (tautology). Bare-name collisions are the recurring cause; `ugrep`
  is the default `grep`, so pin `/usr/bin/grep` and anchor on qualified names.
  Validate a census against known ground truth **before** believing any of its
  other output.
- **Sabotage:** an arm that does not bite is a fact about the arm, not the code.
  Disclose it in the commit and escalate to the broader arm (all 33 increments,
  all 227 constants), and sabotage the implementation rather than a shim.
- **Unanimity:** when every call site disagrees with a declaration in the same
  way, that is evidence against the declaration **only** when the declaration
  independently shows stub signs. Two counterexamples here had unanimous call
  sites and a correct declaration. Ask which side is internally consistent.
- **Size:** never indicts a module on its own. A file at 38% of its historical
  size was a legitimate split; a 294-byte file was a deliberate facade over a
  123 KB core. Size opens an investigation, never closes one.
- **Detail:** `.claude/skills/spipe.md` §"Sabotage discipline" / §"Census
  discipline".

## Maintenance

Add a compact entry here when repeated ambiguity causes an agent to choose the
wrong repository subsystem. Link detailed guides instead of duplicating them.

## Compiler loader and packed-byte performance

- **Canonical plan:** `doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md`.
- **Executable/manual:** `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl`
  and `doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md`.
- **Feature/layer knowledge:**
  `doc/00_llm_process/feature_expert/compiler_loader_script_crosslang_perf/skill.md`
  and `doc/00_llm_process/layer_expert/compiler_driver/skill.md`.
- **Open verification records:**
  `doc/08_tracking/bug/module_loader_negative_cache_stat_storm_2026-08-11.md`
  and packed-byte history in
  `doc/08_tracking/bug/interpreter_byte_array_len_widening_spin_2026-08-13.md`.
- **Status:** plan complete, feature verification blocked. The deployed
  self-hosted candidate currently fails its wrapper ABI/help probe; never
  substitute the Rust seed or detached-tree helper names.

## Simple 2D primitive lane / host-first UI work

- **Canonical map:** `doc/07_guide/app/llm/simple2d_primitive_lane_inventory.md`.
- **Architecture/design/test plan:** `doc/04_architecture/simple2d_primitive_lane.md`,
  `doc/05_design/simple2d_primitive_lane.md`, and
  `doc/03_plan/sys_test/simple2d_primitive_lane.md`.
- **Shared path:** host input -> common event normalization -> semantic hit/layout
  owner -> `DrawIrComposition` -> Engine2D. Web, GUI, WM, and 2D must not fork
  button, drag, scroll, layout, font, or Vulkan logic.
- **Primitive acceptance:** click is one matched press/release action; drag owns
  pointer capture and deterministic release; layout separates clipping from
  scrolling; scroll clamps and invalidates; text remains semantic and lowers
  through `FontRenderer`/transient `FontRenderBatch`.
- **QEMU rule:** use the canonical host-GPU wrapper and require an admitted
  pure-Simple compiler, exact argv, event/frame correlation, fenced device
  completion, device-origin readback, exact CPU parity, font receipt, and 20
  warm p95/RSS samples. TCG, screenshots, source checks, and phase-2 are not
  native Vulkan proof.
- **Deferrals:** macOS is implementation/test-only under TODO 660; UNO Q needs
  physical enumeration and a SimpleOS-native Adreno lifecycle. Report these as
  blocked/unsupported, never as fallback passes.
- **Handoff:** small sidecars may inventory Web/CSS, GUI/button/key, WM/drag/scroll,
  or 2D/font/QEMU independently. `/root` is merge owner; Sol reviews before
  done/release claims.

## Robust lifecycle persistence

- **Canonical owner:** `std.lifecycle_persistence`, implemented under
  `src/lib/common/lifecycle_persistence/`.
- **Representation:** ordinary Simple structs, enums, constructors, functions,
  annotations, and SDN metadata.
- **No dedicated grammar:** do not invent `life`, `virtual life`, `transition`,
  or `recovery ... for ...` declarations for this feature.
- **Boundary:** graph, transition, and recovery-registration validation does
  not prove durable storage, restart recovery, boot restoration, power-cut
  safety, or formal correctness; those claims need separate evidence.
- **Identity:** persist durable keys such as the existing `EntityKey` owner,
  never direct pointers, runtime `+T` handles, or snapshot-local references.
- **Guide:** `doc/07_guide/lib/lifecycle_persistence.md`.
- **Executable evidence:**
  `test/03_system/feature/language/robust_lifecycle_persistence_spec.spl`.

### Agent lookup rule

When a request mentions robust lifecycle persistence, search
`std.lifecycle_persistence` and the guide first. Propose new grammar only after
accepted requirements demonstrate that existing Simple forms cannot express
the required semantics.

## SimpleOS I/O and audio

- **Canonical event owner:** `std.common.io.simple_device_event`.
- **Audio contracts:** `std.common.engine.audio.simple_audio_*`.
- **Guest drivers:** `os.drivers.virtio.virtio_input_*`,
  `os.drivers.virtio.virtio_snd_*`, and the retained x86 HDA service.
- **Hosted event backends:** GLFW and SDL3 are distinct dynamic adapters; one
  must never silently substitute for the other.
- **CUDA audio:** the guest submits bounded Q15 work through a second QEMU
  `ivshmem-plain` device to the pure-Simple host daemon. This is host-driver
  offload, not an in-guest CUDA runtime claim.
- **Two-wire rule:** render/host-GPU owns ivshmem ordinal `0`; audio owns ordinal
  `1`. A first-match or shared mapper aliases the protocols and is invalid.
- **Mapper owner:** `os.kernel.ipc.host_gpu_ivshmem_map` exports
  `map_qemu_host_gpu_ivshmem_bar2` for ordinal `0` and
  `map_qemu_audio_ivshmem_bar2` for ordinal `1`.
- **Primary guide:** `doc/07_guide/platform/simpleos/io_audio.md`.

### Verification rule

Run `test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl`
after changing PCI/ivshmem ownership. A source check or QEMU preflight does not
replace a live device-origin readback receipt. Non-native platform rows must
report unavailable or pending, never fabricated PASS.

## SimpleOS device process / CXL / "driver in device"

- **Canonical architecture:** isolated user-space hardware drivers with kernel-
  enforced capabilities, IRQ routing, DMA/IOMMU, reset, and revocation.
- **Default placement:** `HostIsolated`; colocation is profiling-driven.
- **CXL Type 3:** host-visible memory, not a processor and not proof of a
  device-local driver.
- **Host queues in Type 3 memory:** call these `CxlHostMapped`.
- **Device-local execution:** use `DeviceResident` only for a programmable,
  securely loadable endpoint with watchdog/reset and a defined transport.
- **UNO Q:** distributed MPU/MCU device graph with `NoCxl` under currently
  published interfaces.
- **Guide:** `doc/07_guide/platform/simpleos/cxl_device_process_architecture.md`.
- **Expert note:** `doc/00_llm_process/feature_expert/simpleos_cxl_device_process/skill.md`.

### Evidence lookup rule

Research and selected requirements are available, but executable CXL/device-
process specs and implementation are not yet present. Do not treat a QEMU job
skipped after an upstream bootstrap failure as PASS. Keep documentation,
executable-spec, QEMU-functional, real-IOMMU, and physical-device evidence as
separate claim levels.

## SimpleOS toolchain self-host / "clang on SimpleOS" / clang+Simple migration

- **Cross-layer POSIX/startup lookup:**
  `doc/07_guide/app/llm/simpleos_posix_host_interface_index.md` maps the
  existing pure-Simple POSIX facade, host mmap helpers, SimpleOS VFS prewarm,
  startup argv policy, and LLVM/Clang port owners. It explicitly separates
  recovered/current code from the planned dedicated-host provider and marks
  Clang-consumer integration as unverified until evidence exists.

- **Canonical meaning:** building an `x86_64-unknown-simpleos` LLVM/clang/lld
  cross toolchain whose outputs are *guest-runnable*, plus a Simple payload that
  links and runs in-guest. Campaign lane:
  `.spipe/simpleos_clang_simple_migration/state.md` (10 ACs). Plan of record:
  `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`.
- **Expert notes:**
  `doc/00_llm_process/feature_expert/simpleos_toolchain_selfhost/skill.md`,
  `doc/00_llm_process/layer_expert/llvm_toolchain_port/skill.md` (fork, cross
  CMake toolchain, sysroot, libc/crt0),
  `doc/00_llm_process/layer_expert/os_kernel_exec/skill.md` (VMM, FS-exec ring-3
  loader, FAT32, image builder).
- **Guide:** `doc/07_guide/os/simpleos_llvm_toolchain.md`.
- **Guest-runnable contract:** `Type=EXEC`, entry `0x40000000`, **zero INTERP
  segments**, static. Produced by `-static` + `-Wl,-T,<sysroot>/share/simpleos/
  simpleos.ld` in `src/os/toolchain/llvm/simpleos_cross_toolchain.cmake`.
  `src/os/port/llvm/clang_static.shs` is **DEPRECATED** — it existed only because
  those flags were missing, which let the host clang driver defer the link to gcc
  and emit a Linux-dynamic ELF.
- **LLVM fork:** `github.com/ormastes/llvm-project` branch `simpleos` (Clang 20),
  pinned by `LLVM_REVISION` in `src/os/port/llvm/build.spl`.

### Status rule — do not overstate

In-guest **COMPILE** is proven under real OVMF-pflash firmware
(`[ok] L4 in-guest clang compiled /hello.o under OVMF`,
`[oo-nvme] persist /hello.o -> OK`, `[syscall] exit status=0`). **Not** proven:
byte-exactness of that object (host-side `getfile` retrieval returns empty),
in-guest LINK+RUN, the install-image live gate, and the physical board. The
`bin/release/x86_64-unknown-simpleos/simple` payload is **seed-built staging
evidence**, not self-hosted evidence — it was produced by the Rust bootstrap seed
as the D1 route-around and has been **linked, not run**.

### Evidence rule — positive markers only

Never accept an **absence** condition ("the failure line is gone") as proof a
kernel fix worked: `config/freestanding_fabricated_stub_baseline.sdn` has zero
rows for `simpleos_ssh_ring3_uefi128.elf` and `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:299-314` only WARNS for
an unbaselined entry, so the channel can fabricate weak no-op bodies and still
build green. Require the positive marker, `nm` for `T` (not `W`), and a
`FABRICATED-NEW` diff across the change.

### Diagnostic rules for this area

- A CMake `check_*_compiles` FATAL_ERROR names the **probe**, not the cause —
  read `CMakeFiles/CMakeConfigureLog.yaml` (observed: two false "libstdc++ too
  old"/"needs libatomic" reports hiding an undefined `rt_array_len`).
- Derived archive copies reproduce fixed errors: `libm.a` is a `cp` of
  `libsimpleos_c.a` (`sysroot.shs:266`). When a fix "doesn't take", `cmp` them.
- Archive members link **per object**, so a bridge sharing a TU with core libc
  makes its dependency mandatory. Localise with `nm -u` per member, not per
  archive. One `.o` per source, never `ld -r`.
- A log marker that does not identify its **writer** cannot distinguish two
  implementations — two VMM paths printed byte-identical `[VMM]` banners while
  the consumer read a never-written global whose `vmm_init` had zero callers.
- `file(1)` reports "dynamically linked" for a `--export-dynamic` static binary.
  Use `readelf -l <bin> | grep -c INTERP` (must be 0) plus `readelf -h`.

## PostgreSQL mimic / Simple DB server

- **Protocol/session owner:** `std.database.postgres_mimic`.
- **Execution engine:** `std.database.pure_sql.PureDatabase`.
- **Compatibility claim:** PostgreSQL-like startup, session, simple-query,
  transaction-status, row-set, command, and error semantics; do not claim full
  PostgreSQL wire or SQL parity without corresponding contract evidence.
- **Production execution:** cached `build/database/postgres_mimic_server.smf`,
  `.lsm` library, or native executable. An interpreter-mode caller should use
  that compiled artifact rather than interpreting the database hot path.

## LLM Caret messaging

- **Bounded context:** `src/app/llm_caret/messaging/`.
- **Authoritative semantics:** the primitive Simple room; external transports
  publish capability levels and use primitive sidecars for missing behavior.
- **Database:** `std.database.pure_sql.PureDatabase`, never C `sqlite_sffi`.
- **Compiled carriers:** `messaging/{mcp,hook,bridge,database}_worker.spl`; an
  interpreter-hosted launcher still selects a fresh SMF/native worker.
- **Plugin:** `plugins/llm_caret_messaging/` packages Claude, Codex, Gemini,
  MCP, skills, migrations, and guarded ownership metadata.
- **Entry guide:** `doc/07_guide/app/llm/llm_caret_messaging.md`.
- **Evidence:** `doc/09_report/llm_caret_messaging_traceability.md` and
  `.spipe/llm-caret-messaging/state.md`.
- **Development fallback:** direct source/interpreter mode must be explicit and
  is not production evidence.

### CLI/TUI hardening status (bootstrap-gated)

- The typed terminal lifecycle boundary, cached Claude PTY fixture, and plain
  hidden-command admission coverage are committed source/test changes; their
  contract is recorded in `doc/05_design/llm_caret_claude_cli_harden.md`.
- Runtime-required Caret verification is **postponed**, not passed, until a
  provenance-qualified pure-Simple bootstrap deploys an executable containing
  the canonical SSpec colon-block parser. The deployment defect is tracked in
  `doc/08_tracking/bug/self_hosted_sspec_describe_colon_parser_2026-08-08.md`.
- After bootstrap success, execute the focused runtime unit spec first, then
  the CLI/default-alias-disabled and plain-hidden scenarios, then the cached
  offline-Claude PTY scenario; retain the resulting evidence in the task plan
  at `doc/03_plan/agent_tasks/llm_caret_claude_cli_harden.md` before making a
  success claim.

## GLM and Kimi coding agents

- **GLM through Claude Code:** run `bin/glm`; flagship/main and subagents use
  `glm-5.2`, while Haiku/background work uses efficient `glm-4.5-air`.
- **Two Kimi credential systems:** Kimi Code subscription keys come from the
  Kimi Code Console and use `api.kimi.com`; Moonshot Open Platform keys come
  from `platform.kimi.ai` and use `api.moonshot.ai`. They are not
  interchangeable. Select by issuing console, not key prefix.
- **Kimi Code subscription through Claude Code:** use
  `https://api.kimi.com/coding/`, model `k3[1m]`, and a 1M context window. The
  bracketed model spelling is for Claude Code environment variables.
- **Moonshot Open Platform through Claude Code:** run repo `bin/k3`; all Claude
  tiers and subagents map to `kimi-k3[1m]` on
  `https://api.moonshot.ai/anthropic` with a 1M window and max effort.
- **Kimi native harness:** install `@moonshot-ai/kimi-code`; run `kimi`,
  `kimi --yolo` for auto-approved ordinary tools, or `kimi --auto` for fully
  autonomous permissions. Native Kimi Code subscription configuration uses
  `https://api.kimi.com/coding/v1` and model `k3`.
- **Kimi MCP lookup:** the native harness auto-discovers project `.mcp.json`.
  Resolve stale absolute checkout paths first. The Simple LSP MCP source command
  must include `bin/simple run` and the stdio bridge; a merely `connecting`
  server is not ready.
- **tmux warning:** `extended-keys` off affects modified Enter combinations,
  not ordinary Enter. Use `tmux set -g extended-keys on` and persist the option.
- **Credentials:** launchers read environment variables or user-private token
  files/configs with mode `600`. Never put keys in a repo file, shell alias,
  command history, or wiki.
- **Guides:** `doc/07_guide/infra/model_providers/glm.md` and
  `doc/07_guide/infra/model_providers/kimi.md`.

### Database lookup and execution rule

For database work, search `src/lib/std/database/` first. `PureDatabase` in
`std.database.pure_sql` is the SQLite-compatible implementation rewritten in
Simple; `sqlite_sffi` is the foreign C wrapper. Prefer `PureDatabase`, but run
production hot paths in a cached SMF library or native executable even when the
top-level tool is launched in interpreter mode. LLM Caret's server, MCP, hook,
bridge, and database workers are examples of this carrier pattern.

## SOSIX/QEMU matrix ownership

All agents testing SimpleOS filesystem execution must reuse
`scripts/qemu/simple-qemu-settings.shs` and
`scripts/qemu/simple-big-storage-root.shs`, and must create a closed pre-run
receipt with `scripts/qemu/simple-qemu-host-admission.shs`; do not copy QEMU
argv or invent a private artifact root. Storage resolves in this order:
`SIMPLE_BIG_STORAGE_ROOT`, the workspace-local config selected by
`SIMPLE_BIG_STORAGE_CONFIG`, then `$HOME/.simple`. This host selects
`/mnt/data/.simple`.

The release matrix is exactly four actual hosts (Linux, Windows, macOS, and
FreeBSD) by six guests (x86_32, x86_64, ARM32, ARM64, RISC-V32, and RISC-V64).
Unix agents use `scripts/check/check-sosix-qemu-matrix.shs`; Windows agents use
the PowerShell peer. `--all-guests --parallel`/`-AllGuests -Parallel` runs six
isolated rows and waits for every result. Never relabel the current host.

Every PASS needs boot, mount, target-side directory listing, one
filesystem-loaded target-native program, clean commit/tree identity, exact
argv and hashes, resolved firmware identity/mode with boot-stage correlation,
and a collector run nonce literally correlated exactly once with the retained
serial transcript. When the workload nonce is echoed by both kernel and child,
it must be a separate media slot and cannot serve as the collector nonce.
Compiler-bearing media additionally needs target-native
`simple --version` plus nonce-bound hello compile/run artifacts. Import cross-
host bundles only through `produce-sosix-qemu-native-pass-bundle.shs` followed
by `collect-sosix-qemu-evidence.shs`; missing hosts or media remain owned
`blocked` rows with exact resume commands. TCG proves correctness only, and
macOS postponement is not PASS. Before a native-host attempt, run
`sh scripts/check/produce-sosix-qemu-native-pass-bundle.shs --self-test`; its
temporary fixture checks producer closure but is not host admission and cannot
be published as a row.
The current PASS/blocked ledger is
`doc/03_plan/sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md`.

The 32-bit lifecycle source gates are no longer sufficient admission by
themselves. Run the x86_32 or ARM32 contract with `--admit KERNEL_ELF`; the
gate checks ELF identity, nonzero entry, and strong linked lifecycle symbols.
The retained ARM32 ELF passes, while the retained x86_32 ELF is rejected until
the task/generation-bound `rt_x86_32_tss_set_esp0` and
`rt_x86_32_tss_bind_task` owners are linked strongly through the broad rebuild
profile.
RV64 has a real result-boundary spec but still requires a provenance-admitted
Stage-4 runner and fresh producer bundle. Do not use Stage 3 or the Rust seed.

Canonical operator detail is
`doc/07_guide/platform/simpleos/sosix_qemu_shared_settings.md`.

## SSpec documentization maintenance

Treat `simple sspec-maintain` as the SSpec/manual peer of lint and
duplicate-check. Start with `scan`, review all seven explainable scores—not
only the aggregate—and inspect stable `SSDOC-*` findings. A blocker caps the
aggregate at 49. File and directory scopes are supported; a missing/stale
mirror, an empty directory scope, machine-output contamination, or a configured
score/severity failure is not a clean result.

For SPipe rule-level authoring guidance, use `doc/07_guide/infra/testing.md`
as the canonical workflow source (matchers, docstring style, hooks, generated
manual flow).

MCP callers use read-only `simple_sspec_scan` for scoring. Reserve the
conservative write-capable `simple_sspec_maintain` surface for an explicitly
approved preview/apply, scaffold, or documentize workflow.

Use `improve` only as a preview until a human or calling agent confirms the
exact `--apply` patch. Applied changes retain rollback material and must not
rewrite behavioral meaning, assertions, REQ bindings, evidence claims, or
authored narrative. A reviewed `--suppressions` file uses
`RULE_ID|owner|reason|optional-fingerprint`; blockers cannot be suppressed.
Use `--baseline` for the reviewed fingerprint ledger and never hide a finding.

For reference Markdown, use `scaffold`; preserve explicit REQ IDs and source
hashes, and leave every unresolved oracle as executable
`fail("TODO: replace generated placeholder with an executable assertion")`.
Use the `spec-to-spipe`/compatibility `spec-to-sspec` research architecture for
full external standards that require byte coverage, source ledgers, adapters,
or official conformance bindings. Its generated SSpec must pass the same
maintenance scoring and must never upgrade an unresolved oracle into a pass.
The canonical research entries are
`doc/01_research/domain/spec_to_spipe_toolchain.md` and its repository audit at
`doc/01_research/local/spec_to_spipe_toolchain.md`; `spec-to-sspec` is a
planned compatibility command/name, not a second semantic importer. Phase 0
contracts exist, but neither name is a production external-standard CLI yet.
Never fabricate outcomes, generate skips, or use tautologies. Use literal
`step("...")` calls, not bare `@step "..."` decorators.

`documentize` invokes SPipe, the canonical complete-manual generator, then adds
scorecard and provenance. Read the generated Markdown as an operator manual:
verify purpose/audience, preconditions, visible workflow, narratives,
requirement-test traceability, score/remediation, evidence/provenance,
compatibility/limitations, and folded executable detail. Optional LLM
suggestions must cite source evidence; they are preview-only, excluded from the
score, never self-approved, and never self-applied. See
`doc/07_guide/infra/sspec_documentization_maintenance.md`.

Core maintenance is offline: it must not call an LLM or transmit source.
`--debug-timings` writes separate scan parse/mirror/rule/render/cache and
improve preview/conflict/reparse/write diagnostics to stderr; machine report
stdout stays serialization-only. Do not infer documentation-quality acceptance
from timing output or a zero-stub count alone.

## Minimal-bootstrap feature development

Normal feature work starts with the smallest named target, provider artifact,
and composition-image projection. A compiler source path is not itself a full
bootstrap reason. Compatibility receipts control reuse and escalation;
`Unknown` rebuilds conservatively and never authorizes reuse. Full self-host
convergence and DDC remain explicit release/trust targets. Canonical guide:
`doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`; expert:
`doc/00_llm_process/feature_expert/minimal_bootstrap_configuration_composed_dynamic_architecture/skill.md`.

## Post-bootstrap Stage 4 SSpec acceptance

- Canonical spec: `test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl`.
- Runner/input: exact full candidate plus adjacent absolute provenance.
- Meaning: current content/lineage and unchanged retained tool-smoke evidence.
- Never substitute a seed, wrapper, stale path, repeated smoke, or platform evidence.

## rules.sdl (LLM fraud prevention)

- **Canonical meaning:** root-level registry of counts/files/lists/lanes that may grow
  but never shrink without a reviewed, recorded decision.
- **Implementation:** `rules.sdl`; `scripts/check/check-rules-sdl.shs` (gates, `--group
  quick|full`, `--ref`, `--selftest`); `scripts/check/check-rules-sdl-integrity.shs`
  (the registry may not shrink to escape the registry).
- **Use for:** deciding whether a change may reduce test/script/lane coverage, and
  proving it did not. Wired to pre-push (quick) and bootstrap (full).
- **Do not substitute:** not a replacement for the four mandatory pre-push guards —
  those prove the tree is structurally sound, none notices a tree that is intact but
  contains fewer tests.
- **Primary guide:** `doc/07_guide/infra/llm_fraud_prevention.md`
- **Expert note:** baseline a gate with the gate's OWN command at a commit; a working-copy
  census compares a different population and reads as a phantom shrink. Zero evaluated
  gates is `ERROR`, never `PASS`. `status: planned` lanes report `SKIPPED — NOT VERIFIED`
  and may never report PASS.
