# LLM Repository Wiki

Short, canonical term resolution for coding agents. Read this index when a user
names a repository capability whose implementation owner is ambiguous.

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
  `Process timed out` (600s daemon request cap). Neither is a test result.
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
