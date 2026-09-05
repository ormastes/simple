<!-- codex-research -->
# Simple Unified Debugging & Evidence — Research, Design, and Implementation Plan

**Date:** 2026-08-14

## Goal

Unify Simple debugging across embedded firmware, desktop/mobile/server
applications, SQL/databases, browser JavaScript, WebAssembly, Simple browser
scripts, and common-language runtimes. Reuse existing Simple infrastructure
instead of creating parallel debugger stacks.

## 1. Architecture Decision

Expose one versioned `DebugServiceV1`:

```text
CLI / IDE-DAP / SPipe-MCP / Lab
              |
        DebugServiceV1
              |
   Target Graph + Evidence + Policy
              |
 Simple | Native | Browser | SQL/Runtime | Embedded
```

DAP remains IDE-facing. Existing `DebugTarget`, `ProfileTarget`, and legacy
`DebugBackend` become migration adapters. Mutable adapters are centrally owned
and clients use `DebugSessionId`.

Keep the root operations small: `Observe`, `Inspect`, `Control`, `Probe`,
`Profile`, `Evidence`, and versioned `Domain` operations.

## 2. Shared Contracts

### DebugTargetGraphV1

Represent real topology:

- desktop: host → WebView/renderer → GPU → workers → DB;
- mobile: host → Simple runtime → WebView → GPU → SQLite;
- server: process → task → actor → queue → RPC → SQL;
- browser: frame → worker → JS → Wasm → Simple script;
- embedded: board → cores → RTOS tasks/ISRs → runtime → peripherals.

### DebugCapabilityV1

```text
support: Native | Emulated | Unavailable
verification: LiveVerified | FixtureVerified | Unverified | Blocked
perturbation: Passive | Cooperative | Stopping | Mutating
```

### DebugEventV1

Carry build ID, `SourceAnchor`, `SymbolId`, execution/trace/span/task/actor/
connection/transaction/query IDs, clocks, privacy labels, typed payload, and
`Observed | Caused` provenance.

## 3. Evidence and Dumps

Retain native artifacts and add a normalized index:

```text
bundle/
  manifest.sdn
  receipts.sdn
  normalized/{targets,events,stacks,query_plans}.sdn
  raw/{core,minidump,tombstone,crash,t32,trace,renderdoc,browser,logs}
  media/{screenshots,reproduction}
  EVIDENCE_SHOWCASE.md
```

Support Simple CrashBundle, ELF core, Windows minidump, Apple crash/core,
SimpleOS dump, bare-metal dump, JTAG snapshots, OpenOCD/GDB snapshots,
T32/TRACE32 dumps, vendor/product custom dumps, UART dumps, and semantic
replay. Product-specific dump formats remain native.

## 4. Probe and AOP Model

```text
Probe = Stop | Log | Trace | Watch | Count | Snapshot | Dump
```

Map probes to interpreter hooks, JIT patchpoints, GDB/LLDB logpoints, eBPF
uprobes/USDT, ETW, CDP, Wasm breakpoints, SQL trace callbacks, embedded
tracepoints/HW breakpoints/JTAG, or Simple AOP.

Preferred escalation:

```text
existing telemetry
→ dynamic probe
→ watchpoint
→ interpreter inspection
→ AOP debug aspect
→ source instrumentation
```

AOP debug aspects must be read-only by default, contain no business logic, use
typed fields/stable callsite IDs, support sampling/rate limits/TTL, generate
receipts, obey MDSOC scope, and fail mission-critical validation if mutating.

## 5. Embedded

Reuse existing Simple JTAG TAP/debug-chain, DMI/OBS tunnels, GDB remote,
OpenOCD and T32 support.

```text
retained dump/trace
→ event ring/logpoint
→ HW watchpoint
→ halt/inspect
→ source step
→ mutation/fault injection/flash
```

Provide a tiny target debug agent for interpreter/SMF/JIT control, dump
capture, event-ring drain, memory/register access, and JIT registration. Bind
source breakpoints to `SymbolId + SourceAnchor`. Add RTOS task/ISR/queue
awareness and hardware-trace adapters.

## 6. Desktop Apps

Model native processes, tasks, UI/event queues, WebView/Electron/Tauri targets,
GPU, network and local DB. Use GDB/LLDB/core/`coredumpctl`/optional rr on Linux;
DbgEng/PDB/minidump/ETW on Windows; LLDB/dSYM/crash reports/Instruments on
macOS; SimpleOS native bundles.

Add lifecycle, window/UI tree, focus/hit-test, input trace/replay,
screenshot/video, frame timing, network and storage operations. Reuse
RenderDoc/GUI evidence infrastructure.

## 7. Mobile Apps

Android adapters: JDWP, native LLDB, logcat, tombstones, ANR, Perfetto, WebView
CDP, UI snapshot and SQLite. Apple adapters: LLDB/debugserver, exact dSYM
symbolization, crash reports, MetricKit, os_log/signposts, Instruments,
watchdog diagnostics, WKWebView and SQLite.

`AppLifecycleSnapshotV1` records lifecycle transitions, activity/scene
identity, memory pressure, configuration/orientation, background leases, last
input/network event, trace/span, DB transaction, UI responsiveness and
watchdog/ANR evidence.

## 8. Server Apps

Default escalation:

```text
trace → dump/profile → dynamic probe → stopping debugger
```

Propagate Simple `ObserveContext` through HTTP/RPC → task/coroutine →
actor/message → queue → downstream RPC → SFFI → SQL → response.

Production policy normally denies arbitrary evaluation, memory writes and
stop-the-world breakpoints; restricts payload capture; and requires TTL, rate
limits and receipts.

## 9. SQL Debugging

Treat SQL debugging as causality + query plan + execution statistics +
transaction/lock analysis.

`QueryDebugV1` contains engine/dialect, DB/schema, connection/pool,
transaction/savepoint, application `SourceAnchor`, trace/task/actor IDs,
statement digest, sanitized SQL template, bind types/shapes, estimated/actual
plans, timing, rows, cache/buffer statistics, waits/locks, errors/retries and
raw engine evidence. Do not retain bind values by default.

```text
estimated EXPLAIN             Observe
EXPLAIN ANALYZE               Control
query replay                  Control
lock cancellation/rollback    Control
schema/plan forcing           Mutating
```

Implement SQLite first with `sqlite3_trace_v2`, `sqlite3_stmt_scanstatus_v2`,
EXPLAIN/EQP, busy/timeout state, extended errors, statement counters,
WAL/checkpoint and transaction/savepoint events. Then add PostgreSQL, MySQL and
SQL Server adapters.

## 10. Browser, JS, Wasm, Simple Scripts

Use CDP target discovery for pages, frames, workers, service workers, worklets
and Wasm modules.

For Simple → JS, emit standard source maps carrying source revision/range,
`SymbolId`, macro/AOP/desugaring origin and generated locations. For Simple →
Wasm, emit DWARF with files, functions, scopes, parameters/locals, Simple types,
value locations, inline sites and `SourceAnchor` provenance; support
split/external debug information.

For native Simple browser scripts, expose semantic breakpoints, stepping,
logical stacks, structured locals, pure evaluation, task/promise state, DOM/UI
references, WebGPU references and replay events.

Represent JS→Wasm, Wasm→JS, JS→Simple, Simple→browser API and Simple→WebGPU
transitions with `BoundaryFrameV1` to build one logical cross-language stack.

## 11. Common-Language Adapters

| Runtime | Control | Evidence |
|---|---|---|
| Simple interpreter | semantic backend | tasks/objects/replay |
| Simple SMF/JIT | Simple debug agent | code maps/event ring |
| C/C++/Rust/native Simple | GDB/LLDB/DbgEng | dumps/sanitizers/eBPF/ETW/rr |
| Java/Kotlin | JDWP/JDI | JFR/OTel/dumps |
| .NET | runtime debugger | Diagnostic Port/EventPipe/dumps |
| JS/Node | V8 Inspector/CDP | profiles/heap/events |
| Python | pdb/DAP | faulthandler/profiles |
| Go | Delve | pprof/runtime trace/core |
| SQL | engine adapters | plans/waits/locks/history |

Prefer out-of-process adapters speaking stable `DebugWireV1`.

## 12. Minimal CLI

```text
simple debug <profile.sdn>
simple debug doctor [profile.sdn]
simple debug inspect <bundle>
simple debug probe <apply|remove|list> <profile.sdn>
simple debug reproduce <bundle>
simple debug replay <bundle>
```

Keep rich options in SDN config rather than proliferating CLI flags.

## 13. Modern SSpec / TDD Decision Process

A system-test failure is only one entry point. Start from the observed problem:
crash, hang, wrong result, race, performance, UI, network, SQL, lifecycle,
hardware, or existing test failure. **Preserve evidence before modifying the
program.**

- deterministic existing system failure → rerun exact scenario;
- externally visible/multiprocess behavior → Modern System SSpec;
- subsystem/protocol boundary → Integration SSpec;
- local invariant/algorithm → Unit/property SSpec;
- timing/race → passive trace/replay/watchpoint first;
- production crash → retained dump first;
- SQL issue → trace/plan/lock graph;
- embedded → dump/JTAG/trace before halt;
- browser/Wasm → CDP target graph/source mapping;
- mobile ANR/watchdog → system trace/lifecycle evidence.

After root cause, add only test levels justified by the defect.

For externally visible defects, the default reproduction ladder is a
production-shaped System SSpec followed by the smallest Integration SSpec at
the suspected owning boundary, then Unit/property coverage after ownership is
known. Each level must reproduce the same mechanism. If System reproduction
cannot be made faithful, resume environment/target/evidence debugging; if
Integration reproduction fails, resume boundary/hypothesis debugging. Do not
substitute unrelated green tests or an expanding matrix for a missing
reproducer. Once both levels are faithful, adjacent tests may expose the full
shared bug class and guide one owner-level fix.

## 14. SPipe Debug Skill Update

Add an **Evidence-Driven Debug Investigation** workflow:

1. **D0 Intake** — symptom, target/domain, environment, build, input/config,
   frequency, impact, evidence.
2. **D1 Preserve** — dumps, logs, traces, device/query/browser/mobile state,
   binaries and symbols.
3. **D2 Doctor** — live capabilities, verification, privilege, perturbation,
   tool versions and blocked rows.
4. **D3 Classify** — crash/hang/wrong-result/race/performance/resource/UI/
   network/SQL/lifecycle/hardware.
5. **D4 Budgets** — perturbation, privacy, downtime, environment, permissions
   and retention.
6. **D5 Cheapest decisive observation** — evidence → passive telemetry → probe
   → watch/snapshot → AOP → interpreter → native debugger → JTAG → mutation.
7. **D6 Reproduce** — reuse or create a production-shaped Modern SSpec and
   prove the same failure mechanism.
8. **D7 Hypothesis** — claim, evidence, disconfirming evidence, next
   observation, expected result and fallback.
9. **D8 Probe/Attach** — every action emits `DebugReceiptV1` and records whether
   execution changed.
10. **D9 Root cause/owner** — app/library/runtime/compiler/adapter/OS/DB/
    browser/mobile/hardware/test.
11. **D10 Test decision** — System, Integration, Unit/property, Evidence or
    Physical-target.
12. **D11 Fix/verify** — exact reproducer, root-cause regression, subsystem
    suite, real evidence, privacy/build-ID gates.
13. **D12 Cleanup** — remove temporary probes/aspects, close endpoints, restore
    levels, retain useful observability, update docs/skills, and extract new
    feature/layer knowledge when the completed investigation discovered it.

Mandatory rules: do not start with print statements; do not count unavailable
rows as pass; do not infer live support from source presence; retain raw
evidence; obey Observe/Control policy; redact SQL/browser/mobile/memory
evidence; require real source-breakpoint tests for source-map/DWARF claims;
require doctor reachability; forbid AOP semantic changes; and do not confuse
successful dump parsing with fixing the original defect.

Every debugged defect has one bug-database record. Completion records
provider-reported input/output/cache token usage (or `unavailable`) and compares
it with the rolling average of comparable completed bugs. Investigations above
2× average must add a reusable lesson to the owning knowledge/skill and link it
from the bug record; prompts, secrets, and unrelated context are never stored.

## 15. Parallel-Agent Plan

Freeze shared contracts first. Only the contract lead edits the service/wire/
target/capability/event/evidence/probe/receipt/policy schemas.

Suggested ownership: A0 contracts/interface lock; A1 provenance/build identity/
evidence; A2 service/adapter host/doctor/CLI/DAP/MCP; A3 interpreter/SMF/JIT/
native debug metadata; A4 browser/JS/Wasm/Simple scripts; A5 server/
`ObserveContext`/OTel/eBPF; A6 SQL; A7 desktop/UI/GPU; A8 Android; A9 Apple;
A10 embedded/JTAG/T32/OpenOCD/dumps; A11 security/redaction/production policy;
A12 Modern SSpec/evidence/showcase/docs; plus independent architecture,
adversarial and documentation reviewers.

Each child agent returns scope, owned files, interface-lock hash, dependencies,
changes, tests, live evidence, privacy implications, blocked rows, risks and
rollback.

## 16. Implementation Waves

1. **Wave 0 — Contract convergence:** freeze `DebugServiceV1`, `DebugWireV1`,
   target/capability/event/evidence/probe/receipt/policy schemas; adapt existing
   interfaces rather than creating a third API.
2. **Wave 1 — Provenance and evidence:** complete `SourceAnchor`/origin,
   `BuildManifest`/build IDs, symbol bundles, evidence bundles, receipts,
   redaction and offline symbolization.
3. **Wave 2 — Core service and doctor:** implement session registry, adapter
   host, legacy bridges, live doctor, DAP/MCP clients and minimal CLI; isolate
   adapter crashes.
4. **Wave 3 — Simple-native debugging:** complete interpreter structured
   values/frames/scopes/evaluation/tasks/replay; real SMF/JIT attach/launch,
   neutral breakpoints/stack/locals/evaluation/JIT registration; native
   parameters/locals/types/ranges/scopes/inlining/optimized-out/coroutine points
   and production symbol packaging.
5. **Wave 4 — Domain slices:** Simple interpreter; SQLite; Chrome JS/Wasm/
   Simple script; embedded custom dump + OpenOCD/T32; then server, desktop and
   mobile.
6. **Wave 5 — Cross-domain causality/replay:** connect source/build/trace/task/
   actor/JS/Wasm/RPC/message/SQL/device/log/crash, logical async stacks,
   ownership/message history, first-divergence, semantic/rr/UI/input/request/SQL
   replay.
7. **Wave 6 — System evidence/release gates:** require live scenarios for
   native/interpreter/SMF/JIT/browser/SQL/server/desktop/mobile/embedded rows and
   truthful blocked-host matrices.

## 17. Approval Boundary

Freeze before implementation:

1. one `DebugServiceV1` owns mutable sessions;
2. clients use session IDs;
3. existing debug interfaces are adapted;
4. legacy backend gets one migration adapter/retirement gate;
5. DAP stays outward-facing;
6. domain features use versioned registered commands;
7. raw native evidence is retained;
8. Observe, Control and Policy stay separate;
9. support and verification stay separate;
10. external adapters default to stable out-of-process protocol;
11. AOP debugging remains read-only instrumentation;
12. every action has a receipt and every evidence claim binds to an exact build.

Recommended order:

```text
contract convergence
→ evidence/build identity
→ live doctor + adapter host
→ structured interpreter debugger
→ SQLite debugging
→ browser CDP + JS source maps + Wasm DWARF
→ embedded dump/JTAG
→ server causality
→ desktop/mobile target graphs
```

## 18. Research Basis

The plan builds on established mechanisms: DAP; GDB tracepoints/dynamic printf;
RISC-V/JTAG and hardware trace; Android tombstones/Perfetto; Apple LLDB/dSYM/
MetricKit/Instruments; W3C Trace Context/OpenTelemetry; SQLite/PostgreSQL/MySQL/
SQL Server diagnostic facilities; CDP/source maps/Wasm DWARF; JDWP/JFR; .NET
Diagnostic Port/EventPipe; V8 Inspector; Python pdb/faulthandler; and Go
Delve/pprof.

The Simple-specific goal is to make these mechanisms share stable source/build/
runtime identities, target graphs, evidence receipts, security policy, probes
and SPipe investigation rules rather than exposing them as unrelated tools.

## Repository Reconciliation Note

This proposal extends the landed `DebugTarget`/`ProfileTarget` capability layer
and the legacy `DebugBackend` coordinator. It does not authorize a third
parallel mutable debugger stack. Wave 0 must prove adapter boundaries and
value-semantics safety before domain implementation.

## 19. Existing Tool Harmony Inventory (2026-08-14)

The repository already has substantial debugger infrastructure. The unified
service is a control/evidence envelope around these owners, not their
replacement.

| Existing owner | Current concrete surface | `DebugServiceV1` bridge status |
|---|---|---|
| DAP | `src/lib/nogc_sync_mut/dap/` owns protocol, transport, server, breakpoints and adapters for local, remote, GDB/MI, LLDB-DAP, OpenOCD, ST-Link, TRACE32/T32-GDB and DbgEng. Editor DAP session services live under `src/lib/editor/services/`. | DAP remains the outward IDE protocol. Its transport/backend implementations must be adapted, not copied into a new DAP implementation. |
| Main Simple MCP DAP tools | `src/app/mcp/main_lazy_debug_tools.spl` exposes session, breakpoint, continue/step, stack, variables, evaluation, watch/data-breakpoint and hardware-plan tools; `src/app/mcp/dap_bridge.spl` owns their in-process session list and DAP daemon/file-IPC binding. | **Partly bridged:** session creation maps the selected target into the central service, control operations request receipts, and close records/ends the central session. The MCP-local `DapSession` remains a transport/view model; remaining handlers must consistently authorize and record real outcomes rather than becoming another mutable authority. Several hardware operations currently return bootstrap plans, not proof of execution. |
| `mcpgdb` | `src/app/mcpgdb/` owns its MCP protocol, GDB/LLDB process lifecycle, workspace/session selection and command-policy surface. | **Not yet bridged:** it still owns `MCPGDB_SESSIONS` and has no `DebugServiceV1` reference. Preserve its GDB/LLDB runner and command rules, but register each live session with the central service and route policy/receipts through the common contract. |
| Canonical remote model and catalog | `src/lib/nogc_sync_mut/debug/remote/session_model.spl` defines target descriptors, transports, execution modes, capabilities, backend registrations, `debug_backend_catalog`, selection and bootstrap plans. Registered entries cover OpenOCD, Intel JTAG, TRACE32, T32-GDB and remote GDB-RSP. | **Used by the MCP DAP bridge.** This is the canonical discovery/bootstrap catalog; `DebugTargetGraphV1` and `DebugCapabilityV1` describe its live result. Do not introduce a second backend catalog in the unified service. |
| TRACE32 CLI and MCP | `simple t32` is routed to `src/app/t32_cli/`, whose bridge exposes sessions/cores, commands/CMM/eval, windows/capture/describe/screenshots, actions/fields, resources, history, jobs and dialogs. `src/app/mcp_t32/` owns the matching MCP handlers, catalogs and session state. `src/app/t32_mcp_server/main.spl` is presently a startup-light packaged entrypoint. | **Adapter exists but is not wired into either frontend:** `t32_debug_service_adapter_v1.spl` binds an already-connected `t32_session_registry` entry to a central session and gates window capture, PRACTICE, reset and flash. No production caller uses it yet. The CLI/MCP catalogs, Windows-like access interface, action confirmation and existing device session remain authoritative. |
| TRACE32 transport/session owner | `t32_session_registry.spl` tracks multiple connected sessions, selected session, cores and InterCom. Protocol modules own PowerView commands, window capture, dialogs, PRACTICE, direct/SFFI access and T32-GDB. | The bridge deliberately owns no TRACE32 connection. It must bind/unbind registry IDs to `DebugSessionId`; central close must never silently replace device-session close semantics. |
| OpenOCD, GDB-RSP and JTAG | `debug/remote/protocol/{openocd,gdb_rsp}.spl`, DAP adapters, the remote feature registry, `src/lib/hardware/debug/` JTAG/DMI modules and live integration scenarios already own these paths. | Reuse the remote catalog and existing protocol/device owners. The unified layer adds target topology, truthful capability verification, policy and receipts; it must not fork an OpenOCD launcher, RSP engine or JTAG state machine. |
| Windows DbgEng and dumps | `debug/remote/protocol/dbgeng.spl` and `dap/adapter/dbgeng.spl` provide live/process and crash-dump loading plus frames, memory, registers and control; PDB/MSF/CodeView parsers are under `debug/formats/`. | Adapt DbgEng and native dump artifacts into common sessions/evidence while retaining the raw dump. Source presence and parser tests are only fixture verification, not a live Windows support claim. |
| ETW | No owned ETW adapter or live ETW test exists in `src/` or `test/`; references are plans/research only. | Report **Unavailable/Unverified**, never infer support from the DbgEng or Windows rows. Add a separately registered adapter only when doctor reachability and live evidence exist. |

### Adaptation invariant

There is exactly one mutable debugger owner per real resource. Existing DAP,
MCP, `mcpgdb`, TRACE32, OpenOCD/RSP/JTAG and DbgEng components continue to own
their transports, processes, device connections, catalogs and native artifacts.
`DebugServiceV1` centrally owns only unified session identity, target/evidence
graphs, authorization and receipts. A frontend holds its native handle plus a
`DebugSessionId`; adapters translate calls and outcomes in both directions.
They must not duplicate backend catalogs, session registries, breakpoint state,
window/action catalogs or dump formats. A bridge is complete only when live
attach/reachability, authorization, outcome receipt, cleanup and raw-evidence
retention are tested through the real owner.
