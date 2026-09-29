# Simple slim TUI / GUI
## Kernel–plugin reuse, performance audit, library comparison, and parallel implementation plan

**Date:** 2026-09-05  
**Repository:** `ormastes/simple`  
**Inspected revision:** `e0432cd7be29668138a4c47bf270cb5243ead8e4`  
**Status:** Research and proposed implementation plan. Source inspection completed for the paths identified below. No production patch, current-binary benchmark, or GUI presentation test was executed for this report. Historical results are explicitly separated from new targets.

---

## 1. Decision

**Keep Simple’s UI architecture and public behavior. Reduce the code, data, providers, and initialization work reachable from each application. Reuse the existing composition/provider foundation rather than build a second plugin runtime.**

Make a minimal TUI application load a TUI closure, and a minimal GUI application load a GUI closure. The full products must retain their current features, either in the required startup closure or in correctly declared, demand-loaded feature packs. A small application must not pay for unrelated products just because they share a repository or an umbrella import.

The first optimization wave should fix demonstrated work amplification in existing code, before changing any default backend. Source inspection found repeated whole-row-table copies in the normal TUI, repeated parent/sibling scans in Tiny layout, fresh Tiny TUI buffers on each render, and periodic polling in the normal async TUI. These are better initial targets than assuming a C library will automatically be faster. [R03] [R04] [R05] [R06]

### Recommended external comparison set

Use **termbox2 and ncursesw** for the primary C terminal comparisons; **Nuklear and microui** for C widget-core comparisons; **FLTK** for a complete lightweight desktop toolkit comparison; and **LVGL** for an embedded GUI comparison. Use **FTXUI** as a richer TUI toolkit comparison and **Clay** only as a layout-engine reference. None becomes a mandatory Simple dependency merely by appearing in this list. [W01] [W02] [W03] [W04] [W05] [W06] [W07] [W08]

“Kernel” here means the **application composition kernel**, not the SimpleOS privileged kernel. Widgets, parsers, fonts, terminal emulation, GPU drivers, and desktop window management do not belong in that generic kernel.

## 2. Scope and invariants

| ID | Required invariant |
|---|---|
| UI-SLIM-001 | Existing application-visible widgets, events, themes, layout, clipping, scrolling, keyboard behavior, and error behavior remain available. |
| UI-SLIM-002 | Preserve existing state authority, TinyPane relationships, TinyDrawStream boundaries, and full-IR compatibility adapters. No competing public UI model or IR. |
| UI-SLIM-003 | Reuse composition/provider discovery and admission; do not create a second loader, manifest language, or provider lifecycle. |
| UI-SLIM-004 | A no-watch TUI hello must not initialize a GUI window, GPU, browser, full compositor, or file watcher. |
| UI-SLIM-005 | A GUI hello initializes only its selected presentation path and required text/widgets. It must not initialize every available backend. |
| UI-SLIM-006 | Static products use static composition where supported. Dynamic placement is optional, not an automatic requirement for every feature. |
| UI-SLIM-007 | No-GC and bounded-memory operation must be explicit profiles with executable allocation tests, not conclusions drawn from directory names. |
| UI-SLIM-008 | Every performance claim identifies the executable, build lane, features, platform, cache state, and measurement boundary. |
| UI-SLIM-009 | Loading less cannot silently remove required features, skip rendering, bypass validation, or substitute a headless counter for a visible GUI. |
| UI-SLIM-010 | An optimization preserves value/COW semantics. A new private reusable buffer must not mutate an earlier public snapshot. |
| UI-SLIM-011 | Old/new routes remain differentially testable until parity and performance gates pass. |
| UI-SLIM-012 | Optional feature first-use time and peak memory are measured, so startup improvements cannot simply hide unacceptable later costs. |

Out of scope: a new language grammar, a replacement window manager, rewriting all UI in C, converting retained semantics to immediate mode, implementing the whole SOSIX unification project, full browser replacement, GPU scheduler redesign, or proving an unmeasured global size/speed record.

## 3. Existing architecture: reuse versus proposal

The recovered September 3 kernel/plugin plan recommends a façade over `nogc_sync_mut.composition`, retention of `SimpleProviderQueryV1`, static-first dispatch, and a separate async layer. The earlier Tiny UI plan preserves shared Tiny GUI/Pane semantics and TinyDrawStream, with full DrawIR/WebIR/WM integration through adapters. This document continues those decisions. See prior-artifact register P01–P03.

| Area | Evidence at inspected revision | Use in this plan |
|---|---|---|
| `src/lib/nogc_sync_mut/composition/provider_contract.spl` | Actual fixed-width provider-query records and arena-offset boundaries exist. [R01] | Reuse discovery/version/capability contract; do not export private Simple objects through a C ABI. |
| `src/lib/nogc_sync_mut/tiny/common/static_registry.spl` | Actual bounded Tiny module/class registry; duplicate checks and linear lookup exist. [R02] | Keep Tiny compatibility; adapt module admission to the common provider authority. Resolve hot interfaces once. |
| Proposed `src/lib/nogc_async_mut/kernel_plugin` | The exact proposed directory was not found at this revision. | Do not claim the reusable async façade is already shipped. Add only the minimum adapter needed, or use the shared implementation when it lands. |
| `src/app/ui.tui/**` | Normal screen renderer, UI session, parser integration, channel/thread event loop exist. [R03] [R04] | Optimize the current normal TUI, not only the separate Tiny path. |
| `src/lib/nogc_sync_mut/tiny/{gui,pane,tui,draw,engine2d}` | Actual Tiny implementations exist. [R05] [R06] [R07] | Preserve their model and port boundaries; minimize their selected closure. |
| `src/lib/gui/pure_core.spl` | Value-level event/command core deliberately excludes native presentation; timing field is caller-supplied. [R08] | Keep as a command-core microbenchmark only; add real GUI presentation measurements elsewhere. |
| `examples/06_io/ui/hello_gui.spl` | Its description identifies an interactive TUI demonstration. [R09] | Keep the example; do not misclassify it as a native GUI benchmark. |
| `doc/09_report/startup_size_performance_audit_2026-05-27.md` | Body dated May 29; historical stripped-size and average process-runtime table. [R10] | Reproduce as history only; not current RSS or time-to-first-frame evidence. |

The exact GUI host-entry owner and current provider-factory import closure must be established in Phase 0. The software rendering leaf was inspected; this report does not pretend that every native GUI startup path has already been traced.

## 4. Library research and fit

The libraries below solve different portions of the stack. Their source size, a fixed allocation strategy, or a thin C binding is not a measurement of total application RAM or startup latency.

| Library | Language and supplied layer | Fit to Simple | Kernel versus additional load | Qualification |
|---|---|---|---|---|
| **termbox2** | C terminal I/O: cells, presentation, input; no widget/layout system; libc dependency. | First small C terminal provider candidate. Keep Simple widget/layout ownership. | Terminal backend provider, statically selected or loaded on demand; never generic kernel. | Project documents actual downstream applications, including editors and a display manager. Feature flags must match across the binding. [W01] |
| **ncursesw** | C curses/terminfo screen and input foundation; associated forms/menu/panel libraries. | Mature terminal compatibility baseline, particularly outside a narrow terminal set. | Selected curses backend; do not link form/menu/panel extras unless needed. | Compare equivalent terminal behavior and Unicode configuration, not a feature-disabled narrow build. [W02] |
| **FTXUI** | C++ screen/DOM/component toolkit, widgets, layout, and interactions. | Richer toolkit reference; useful decomposition example. | Optional comparison or adapter, not default TUI dependency. | Upstream lists downstream use. Compare the necessary sublibraries, not an arbitrarily broad bundle. [W03] |
| **microui** | Small ANSI C immediate-mode widget/command core with fixed working memory; caller supplies platform/render integration. | Lower-bound widget-core reference. | Experimental adapter or benchmark fixture only in the first release. | Small reference is not proof of full desktop feature parity or broad industry adoption. Include its entire context and host costs. [W04] |
| **Nuklear** | Configurable ANSI C widget toolkit; input state and draw commands, without a default OS window or renderer. | Primary practical C widget-core comparator. | Optional provider only after semantics and text capability checks. | Account for the selected demo/backend, fonts, allocations, and identical compile-time flags. [W05] |
| **LVGL** | Configurable C embedded GUI with widgets, display/input integration, styles, and text facilities. | Embedded/SimpleOS comparison; possible device-specific optional integration. | Embedded GUI provider/profile, not host hello kernel. | Match widget/font/display configuration and memory capacity to the test product. [W06] |
| **FLTK** | Lightweight C++ desktop widget/window toolkit. | Complete desktop application comparison, despite not being C. | Reference product or optional native toolkit adapter. | Its complete-window result is a different category from a headless C widget-core result. [W07] |
| **Clay** | C layout engine with caller-managed arena and renderer-independent commands. | Compare layout algorithms and capacity planning. | Optional experiment, not a replacement for TinyPane. | Configure capacities before allocating its arena. No dynamic allocation does not imply negligible reserved memory. [W08] |

### 4.1 Adoption and selection policy

Do not rank adoption by GitHub stars alone. Freeze the upstream revision, inspect documented consumers and maintenance/test activity, record platform support, and review the exact license and bundled font/backend notices in the dependency lock. A tiny niche implementation can be a useful performance reference without becoming the production default.

Start with reference executables and thin experimental adapters. Promote an adapter only if it offers measured value after including its transitive libraries, native resources, compatibility obligations, and maintenance cost. A foreign toolkit must not become a second authoritative copy of Simple’s widget state.

### 4.2 Minimal external implementation matrix

The required first matrix is deliberately small: existing Simple; termbox2 C; ncursesw C; Nuklear C; and FLTK C++. Add microui for a minimum-core diagnostic. Add FTXUI and LVGL after the common harness works; their jobs may develop in parallel but their timing runs must not overlap. Clay is an algorithm experiment, not another GUI hello contestant.

## 5. Kernel, UI essentials, and feature packs

### 5.1 Logical dependency structure

```text
Application's existing public API / current UI session
                      |
          generated product composition
                      |
        common composition kernel subset
                      |
        +-------------+------------------+
        |                                |
  shared UI essentials             selected providers
  state / IDs / events             terminal OR host window
  TinyPane / focus                 input / clock / wait
  damage / required widgets        text / presentation
        |                                |
        +--------- existing ports -------+
                      |
     TUI cells OR TinyDrawStream / existing GUI lane
                      |
          selected rendering/presentation path

Additional declared packs:
collections, rich text, image codecs, themes, dev reload,
inspector, shared WM, full DrawIR/WebIR compatibility, GPU backend
```

This is a composition view of existing components, not a new runtime or a mandate to move directories.

### 5.2 Placement table

| Component | Generic composition kernel | Minimal TUI | Minimal GUI | Additional/full product |
|---|---|---|---|---|
| IDs, typed statuses, version/capability checks | Minimal contracts only | Used | Used | Same authority |
| Provider lifecycle | Static fast path; dynamic engine only when selected | Usually static | Usually static | Dynamic demand loading when useful |
| Scheduler / event waiting | Port/contract, not a mandatory thread pool | Selected terminal event wait | Selected host event wait | Timers/workers only when required |
| UI state, TinyPane, focus, damage | No | Required subset | Required subset | Existing richer capabilities preserved |
| Labels and basic text | No | Required cells/width behavior | Required font/text implementation | Required internationalization remains available |
| Buttons, input fields, lists, tables | No | Only application-required set | Only application-required set | Coarse widget packs or statically linked selection |
| Terminal provider | No | Exactly selected backend | No | Optional TUI shell |
| Host window/presentation | No | No | Exactly selected host path | Other paths optional |
| Software/GPU renderer | No | No GPU for terminal hello | Selected renderer only | Additional renderers selected explicitly |
| SDN/HTML/CSS parser | No | Required for source-driven UI, absent for compiled UI description | Same rule | File-driven, web, and development products retain it |
| File watching / inspector | No | Only for a watch-enabled product | Same rule | Development pack; existing live reload remains functional |
| Full compositor / shared WM | No | Absent unless explicitly required | Host window does not imply full own compositor | Existing shared-WM profile |
| Full DrawIR/WebIR adapters | No | No | Only if current selected path requires them | Do not force Tiny path through full bridge |
| Compiler/JIT/IDE/browser/network | No | Absent from native hello | Absent from native hello | Only genuinely selected application features |

### 5.3 Two independent choices: requirement and placement

Each feature has a **requirement** state and a **placement** state.

Requirement: needed before ready, needed on a declared later action, or not part of the product. Placement: compiled static, prebuilt native shared library, SMF provider, or supported external worker. A required provider may be dynamically packaged but still must be admitted and ready before the application claims readiness. An optional feature may be statically linked but not initialized; that saves initialization, not necessarily mapped/deployed bytes.

For a sealed hello application, static composition is the starting candidate. Do not scan plugin directories, parse every manifest, allocate a general registry, or create a loader thread merely to call one known renderer. For a full tool, use a bounded generated index with exact artifact identities and load only its required subset.

### 5.4 Admission and hot calls

Reuse `SimpleProviderQueryV1` for discovery and version/capability admission, and adapt Tiny module/class identity rather than replacing its public contract. The existing provider wire records intentionally avoid private `text`, collection, and object layouts. Use the existing codec and explicit host-side C shims; serialized record sizes must not be assumed to equal an ABI compiler’s padded struct sizes. [R01] [R02]

Resolve provider interfaces during activation. Use direct calls for sealed static composition where the toolchain can prove the binding; otherwise use one cached function table per coarse provider. Batch input, terminal spans, and draw commands. Never introduce a cross-ABI call per pixel or ordinary layout node.

Dynamic providers remain pinned while any window, callback, future, command buffer, or returned surface refers to them. Stop/cancel, quiesce callbacks, release resources, and only then unload. Defaulting to process-lifetime pinning is preferable to unsafe eager unloading for this optimization project.

### 5.5 Async, no-GC, and SOSIX compatibility

Keep the current public sync routes and async event model. Async must not automatically mean one thread pool per widget library. Use caller-owned arenas/pools and the existing event authority; route waits, input, window and presentation services through existing ports, with a SOSIX adapter as the runtime-unification project becomes available.

Do not implement a separate UI OS abstraction in parallel with SOSIX. Keep legacy host/`rt_` details behind compatibility providers during this change; removal of those details belongs to the unified runtime owner. This UI work may consume a stabilized port without waiting for a complete OS/runtime migration.

“Bounded” and “no-GC” are distinct: a bounded array may still allocate at initialization or grow internally. Define initialization-only allocation, reusable fixed-scene hot paths, capacity failure, and dynamic growth separately. A full profile cannot silently inherit smaller tiny-profile capacity limits.

## 6. Source-grounded optimization backlog

The table distinguishes source-observed amplification from runtime hypotheses. Expected improvements are goals, not measured speedups.

| ID / priority | Source observation | Proposed semantics-preserving change | Proof required |
|---|---|---|---|
| P01 / first | `Screen.draw_hline` repeatedly calls `put_text`; each call parses/splices a row and `_screen_replace_row` copies the row table. [R03] | Batch a horizontal span; initially specialize only inputs proven equivalent to the current single-cell behavior. | Identical clipping, ANSI state, trailing reset, Unicode handling, and old-screen snapshot; general-input fallback. |
| P02 / first | `_screen_replace_row` explicitly allocates and copies an array for one row change. [R03] | Private exclusively owned frame builder; publish one value snapshot after a batch. Keep public value-returning API. | Alias/COW differential tests; allocation and row-copy counts. |
| P03 / first | `resolved_panes` scans prior panes for each parent and prior nodes for sibling offsets. [R05] | Validated parent-index lookup and per-parent running row/column offsets; reuse child metadata. | Same order, bounds, clip, scroll, generation checks; explicit handling of external node mutation. |
| P04 / first | `tiny_tui_render` makes a new cell buffer, computes panes, and converts each text to a character array. [R06] | Add an internal render-into route with reusable scratch; cache/iterate text without rebuilding arrays unnecessarily. | Preserve public returned snapshots; mutation-aware cache; allocation and copy-byte evidence. |
| P05 / next | List rendering scans all nodes; scroll extent also scans nodes. [R05] [R06] | Reuse per-parent child ordinal/count/extent from the same layout pass. | Child order, list selection, nested scroll, deleted/stale handles, and saturation behavior. |
| P06 / first | Async TUI drains `try_recv` then sleeps 16 ms; watcher polls contents every 500 ms. [R04] | Block on events/deadlines where supported; retain channel/producer model and cancellation. Preserve file-watching contract. | Idle wakeups and input latency; quit/unblock, resize, event ordering, no lost reload. |
| P07 / next | Normal file-based construction parses and separately reads content; watcher rereads it. [R04] | Share an immutable source snapshot when parser APIs permit; avoid redundant reads without weakening change detection. | Same parse errors, old-tree preservation, same-content and rapid rewrite behavior; no mtime-only assumption. |
| P08 / first | Normal TUI source imports shared host-compositor entry for a runtime-selected route. [R04] | Thin selected-route adapter/root; verify compile/link/load closure rather than assuming the import loads it. | Link map and process map/open/initialization receipts for ordinary and shared-WM modes. |
| P09 / next | Tiny registry queries scan modules/classes. [R02] | Resolve once and cache a validated interface handle; generated index only if scale warrants it. | A profile must first show repeated runtime lookup; preserve duplicates/version/admission failures. |
| P10 / next | Software fill calls `store_pixel` for every pixel; format/shape checks occur there; same solid color may be converted repeatedly. [R07] | Validated private span-fill path, hoist invariant format conversion/checks, preserve public safe pixel API. | Pixel-exact clipping, both formats, overflow edges; inspect generated code to verify checks were not already hoisted. |
| P11 / investigate | `surface_receipt` computes a full-surface checksum and exposes pixel data in the receipt. [R07] | Profile checksum/receipt cost; cache only if identical immutable frame identity and complete mutation tracking make it safe. | Keep validation/checksum semantics. No caching through untracked public pixel mutation; no removal to improve score. |
| P12 / evidence fix | Pure GUI hot probes count event kinds; elapsed time in a batch is supplied by its caller. [R08] | Keep the microbenchmark but name it correctly; add independent timed native first-presentation and input-response tests. | Real window, non-empty verified output, externally measured elapsed time, successful input response. |

### 6.1 Guardrails for the first two TUI changes

A `ch: text` argument is not necessarily one terminal cell. Repeating a multi-character or styled string in one call may differ from repeated overlapping `put_text` calls. The initial fast path should prove a one-cell case; unsupported cases continue through the old implementation until they have a proven equivalent batched algorithm.

The old screen is a value. Reusing storage that another reference still sees is not a valid optimization. Keep a private builder or proven unique ownership; publish a snapshot at the current API boundary. Do not “fix” a performance issue by changing the language’s mutation semantics.

### 6.2 Guardrails for linear Tiny layout

`add` validates an already-existing parent and gives an appended node its array index. That supports a fast indexed path, but public mutable node arrays require scrutiny before treating the invariant as universal. Validate index and generation; preserve a safe fallback or enforce the invariant at existing mutation boundaries. Use the same numerical overflow policy as the current contract and separately file any correctness issue discovered by adversarial tests. [R05]

Target linear construction for valid append-ordered trees, not a new layout language. Geometry, scroll offsets, hit testing, focus order, and rendering must continue using the same resolved result.

### 6.3 Guardrails for GUI memory and validation

Tiny software rendering stores `pixels: [i32]` for both ARGB8888 and RGB565. The latter describes pixel values but does not prove two-byte storage. Packing that public representation into a new array type would be a separate ABI/data-contract change, not an automatic safe performance patch in this project. Measure the actual generated representation. [R07]

Every untrusted draw stream keeps its required envelope/capability/command validation. Once a stream and destination span are validated, a private fill loop may avoid redundant per-pixel work only with a checked bounds proof. Do not disable stream checks, receipts, or error handling for a benchmark.

### 6.4 Hypotheses that still need profiling

Array `push` may have spare capacity or may trigger costly copies; source syntax alone does not establish its complexity. Text concatenation may or may not be optimized by the selected compiler lane. An import may disappear during linking. GPU/font initialization may dominate native GUI startup, but that path has not been traced here. Mark these `INVESTIGATE`, attach profiles, and then promote verified issues to implementation tickets.

## 7. Product profiles and loading behavior

The following are **proposed composition recipes**, not new language syntax or claims that matching CLI flags already exist.

| Recipe | Required startup closure | Later loading |
|---|---|---|
| `tui-hello-static` | Existing minimal runtime, composition subset, required label/event semantics, one terminal provider | None for the declared fixture |
| `gui-hello-static` | Minimal runtime, shared required state/panes, one host window/input provider, one existing rendering route, required font/text | None needed to make the declared fixture truly ready |
| `tui-file-watch` | Existing `.ui.sdn` parse path and live-reload semantics plus TUI | Watch implementation remains active as required; it is not omitted to win startup |
| `ui-full-static` | Current complete application semantics, selected platform path, existing full capabilities | Static availability may avoid loading, but unused services still should not initialize |
| `ui-full-demand` | Exact required closure from generated index | Coarse optional packs on declared actions; first-use time recorded |
| `ui-embedded-pool` | Validated fixed arenas, selected SimpleOS/device ports, required widgets and text | Only permitted prebuilt packs; deterministic failure when resources are insufficient |

No profile has permission to change a user-selected GPU renderer to software merely because software starts faster. Report each backend separately. Likewise, a production internationalized editor cannot be compared as if its only requirement were an ASCII label.

### 7.1 Resource planning

Derive capacities from a compiled UI description where possible and accept explicit budgets for dynamic content. Account separately for node slots, resolved panes, event queue, terminal cells, draw words, text/glyph data, image caches, frame surfaces, and provider metadata. Reuse the existing generic allocation-planning direction; do not invent UI-specific ownership rules.

For an analytical model, not a measurement:

```text
TUI working storage = cell_buffers × columns × rows × actual_cell_storage
                    + glyph/text storage + pane/state storage
                    + event/output queues + allocator overhead

GUI working storage = surfaces × actual_surface_stride × height
                    + font/glyph/image storage + UI state
                    + draw/event queues + driver/platform allocation
```

Report capacity/reserved bytes separately from touched/resident bytes. Small apps need proportionate initial capacities; full applications keep growth policies and explicit errors. Arbitrarily enormous fixed arenas can make an allocation-free core larger than an allocating one.

## 8. Benchmark design: what exactly is compared

### 8.1 Required workloads

| Lane | Work performed | Main comparison |
|---|---|---|
| H0 | Native empty process and output-only hello, without UI | Runtime/loader floor, not TUI or GUI performance |
| T0 | Initialize/restore terminal, no widgets | Terminal provider initialization overhead |
| T1 | 80×24 terminal, visible greeting, input-ready, deterministic quit | Existing Simple vs slim variants vs termbox2/ncursesw |
| T2 | Same selected panel, focus/navigation, input, resize, styled/Unicode corpus | Like-for-like richer TUI semantics; FTXUI reference |
| G0 | Real native window using the selected host route, blank presentation | Platform/window/renderer floor |
| G1 | Real window, visible greeting, input-ready and responsive quit | Existing GUI route vs slim variants; complete external applications |
| G2 | Same declared controls, text, layout, scrolling and input scenario | Feature parity and interaction/steady-state overhead |
| L0 | Identical valid Tiny tree, growing node counts | Layout scaling and allocation counts; optional Clay algorithm reference |
| X1 | Trigger an optional widget/image/backend pack after startup | Admission/load/first-use p50/p95 and peak memory |

T1 should be tested through a real PTY. A separate terminal-emulator integration run verifies visible rendering; bytes accepted by a PTY are not proof that the emulator has painted them. G1 must use a native displayed surface, not a checksum-only buffer or `gui_dynlib_hot_probe_tick`.

Keep the original `hello_gui.spl` as its actual TUI workload before and after. Adding a new one-label fixture is useful, but replacing its panel/progress/status features and claiming the difference as a refactor improvement is not acceptable. [R09]

### 8.2 Comparison dimensions

For each Simple workload, record current baseline, optimized same feature set, minimal static recipe, and demand-loaded recipe where relevant. Keep native, source/interpreter, cached module, and compiler startup lanes distinct. Comparing a C native executable to a full Simple compiler/interpreter process says little about UI-library overhead.

For foreign libraries, measure direct C/C++ application and a Simple wrapper around the **same** configured library when an adapter exists. This isolates binding cost more credibly than comparing unrelated implementations. Do not force FLTK’s native toolkit into the same renderer as a headless widget engine; publish both component-level and complete-product comparisons.

Freeze logical window size, pixel dimensions/DPI, terminal dimensions, font assets where comparable, text corpus, UI requirements, renderer, optimization flags, linkage mode, and warm/cold policy. Different visual/native-control semantics must be identified, not hidden behind the word “hello.”

### 8.3 Startup timestamps

An external native controller records a monotonic timestamp immediately before process creation. The child emits narrowly scoped milestones on a separate control channel: entry reached, provider admission complete, surface/terminal initialized, first frame submitted, and application input-ready. A presentation observer records visible output when the platform supports a trustworthy observation.

Publish these separately:

```text
launch_to_entry
launch_to_provider_ready
launch_to_first_submission
launch_to_observed_presentation
launch_to_input_ready
input_to_visible_response
optional_action_to_ready
```

The observer and child must share an established clock domain or explicitly calibrated offset. A parent’s receipt time includes IPC delivery and must be labeled as such. A successful submit, event counter, or window handle is not a display timestamp. Unsupported observation produces `NOT_MEASURED`, not a fabricated equality with submission time.

Do not time a script that exits immediately and call the result GUI startup. Also do not include the fixture’s deliberate observation hold or orderly exit in startup time.

### 8.4 Memory and resource metrics

Record executable file bytes, code/data/BSS sections, required deployed assets/libraries, loaded mappings, steady application RSS/PSS/private memory, startup peak, allocation counts and bytes, committed versus reserved arenas, threads, handles, page faults, and idle CPU/wakeups. Count relevant child processes rather than only a small launcher.

On Linux use `/proc/<pid>/smaps` or `smaps_rollup` for detailed process memory accounting. Shared mappings complicate RSS; PSS apportions shared resident memory. Loaded-library file size is not resident memory. Use platform-equivalent measurements on macOS and Windows and label metrics rather than treating unlike definitions as identical. [W09]

GPU device allocations and compositor/terminal-server costs are reported separately from application resident memory. A window-system process already running outside the test is not free, but its entire shared cost should not be attributed to one application without a stated experiment. Use incremental system/process measurements as a separate lane.

Hold the fixture after verified first frame to sample steady state. Measure peak memory independently of steady state. Do not subtract two unrelated peak values and call the difference exact UI overhead; use matched experiments and state the limitations.

### 8.5 Sampling protocol

Proposed initial protocol: 20 untimed warmups, then at least 100 warm launches per configuration in randomized interleaved order on an otherwise idle runner. Use a pilot to characterize noise and increase samples when it changes conclusions. Report median, p95, spread, and uncertainty for the comparison, not a best run.

A new process is not necessarily a cold-cache run. Cold runs require a controlled VM/session/cache-reset method and a recorded display-server/driver state. Thirty controlled cold samples can be exploratory; do not use an unstable tail estimate to certify a small p95 win. Gather sufficient samples for the claimed effect.

Collect tracing/allocation profiles in separate diagnostic runs from low-instrumentation timing runs. The benchmark owner holds an exclusive runner lock: agents may develop in parallel, but concurrent builds, other benchmarks, and driver compilation invalidate timing samples.

### 8.6 Historical numbers: evidence and limits

The repository report’s filename contains May 27, 2026, while its body is dated **May 29, 2026**. It describes stripped size and **mean total process runtime over 20 runs**. The following is an excerpt, not a rerun. [R10]

| Historical artifact | Stripped executable bytes | Mean process runtime |
|---|---:|---:|
| C termios TUI | 14,472 | 4.474 ms |
| Simple standalone TUI, core-C-bootstrap lane | 14,336 | 5.295 ms |
| Simple full TUI app, core-C-bootstrap lane | 14,368 | 6.510 ms |
| Simple hello, core-C-bootstrap lane | 14,336 | 3.129 ms |

Those rows demonstrate that narrow Simple artifacts existed, not that current full TUI/GUI memory or first-frame startup has been measured. They do not establish a startup victory over the C terminal row. The report’s 2,125,328 bytes of listed libc/loader files is a library-file total, **not RSS**. No native GUI measurement is supplied by that table.

### 8.7 New-result template

| Product / feature hash / backend | Before p50/p95 ready | After p50/p95 ready | Before/after steady PSS | Before/after peak | Optional first-use | Result |
|---|---|---|---|---|---|---|
| Normal Simple TUI | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | As applicable | Pending execution |
| Tiny/static Simple TUI | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | As applicable | Pending execution |
| Native Simple GUI, selected backend | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | As applicable | Pending execution |
| Matched C/C++ references | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | NOT_MEASURED | As applicable | Pending execution |

## 9. Tests and acceptance gates

### 9.1 Semantic differential corpus

Use old implementations as comparison oracles only where their behavior is intended. Cover ASCII, Korean text, combining sequences, wide characters, ANSI style/reset boundaries, negative coordinates, zero sizes, resize, overlapping text, retained snapshots, deep/wide layouts, scroll clipping, generation mismatches, focus order, event ordering, cancellation, and all existing widget demos. An existing correctness bug is separately tracked; do not hide it by blessing the old behavior forever or silently change it inside a performance-only patch.

For GUI software execution, compare pixels, bounds, stream status and required receipts. For actual windows, combine captures with semantic input/output assertions. Native OS text rendering may require carefully defined visual tolerances; a tolerance must not allow blank or missing controls.

### 9.2 Negative-load tests

For the relevant declared minimal recipes, prove no unrelated provider is opened, mapped or initialized, and no unrelated worker or compiler is started. Remove or corrupt an unrelated optional pack and confirm hello still works. Remove a required provider and confirm an explicit failure rather than silent fallback. Then exercise the optional feature and verify that it is admitted at that point and actually performs its function.

Static elimination requires link/section/symbol evidence; dynamic nonloading requires map/open/activation evidence. Absence of a log line proves neither.

### 9.3 Resource and lifecycle sabotage

Inject failed provider admission, incompatible ABI/capabilities, duplicate IDs, allocation exhaustion, a full event queue, partial terminal output, interrupted writes, a closed terminal, window destruction with a pending callback, cancellation during a wait, and attempted provider unload with live resources. Preserve cleanup and terminal restoration. Error paths must not hang or return success without output.

C-owned buffers are allocated/freed by the same provider; no foreign exception unwinds through Simple/C boundaries. Draw/input batches have explicit lengths and lifetimes. All capacity/offset multiplication and addition are checked at admission.

### 9.4 Performance gates

Freeze absolute budgets after the real baseline, not from guesses in this report. Apply these structural gates immediately: no unrelated startup providers, no newly introduced hot per-cell FFI, no unbounded event starvation, and no repeated initialization of a provider that is already ready.

Target zero steady-state allocations for the fixed, warmed minimal scene where its existing resource model permits it; report every exception. Target event/deadline-driven idle behavior, not an unrealistic guarantee that a host process never wakes. A change passes only with semantic parity and a measured improvement or a justified resource tradeoff. Differences within noise are `INCONCLUSIVE`, not wins.

## 10. Parallel-agent work division

Each agent owns a disjoint file set and pairs with a reviewer from the other dimension: UI-feature expertise plus runtime/layer expertise. Agents cannot approve their own evidence exceptions. All proposed new directories below are names to be confirmed by the integrator, not claims of existing paths.

| Agent | Ownership and objective | Dependencies | Acceptance evidence |
|---|---|---|---|
| A00 Integration/contracts | Baseline, public contract freeze, source ownership ledger, shared entry/import roots, recipe integration | None | Pinned source/artifact identities; no duplicate runtime or public model |
| A01 Benchmark harness | New `test/helpers/ui_slim/`, `test/05_perf/ui_slim/`, evidence schema and runner scripts | A00 fixture contract | Detects blank GUI, TUI/GUI mislabeling, missing readiness, stale binaries and concurrent runs |
| A02 Composition adapter | New narrow adapter under Tiny/common integration; existing generic provider wire read-only unless separately approved | A00 ABI decision | Static/direct route and dynamic-admission parity; no scan on sealed startup |
| A03 Normal TUI buffer | `src/app/ui.tui/screen.spl` and dedicated new buffer tests | A00 snapshots; A01 baseline | P01/P02; preserved ANSI/COW behavior; allocation/copy counts |
| A04 Tiny layout | `src/lib/nogc_sync_mut/tiny/gui/state.spl` and dedicated layout tests | A00 invariant review | P03/P05 shared metadata; geometry parity and scaling evidence |
| A05 Tiny terminal renderer | `tiny/tui/cell.spl`, `tiny/tui/render.spl`, dedicated tests | Frozen A04 result contract | P04/P05 consumption; stable snapshots; bounded reuse |
| A06 Async TUI/watch | `src/app/ui.tui/async_app.spl`, agreed private wait/watch helpers, dedicated tests | A00 event contract | P06/P07; no lost input/reload; idle and latency data |
| A07 GUI rendering/present | `tiny/engine2d/software.spl`; one confirmed host adapter assigned after inventory | A00 GUI owner map; A01 | P10/P11 with validation intact; actual displayed G1/G2 |
| A08 C terminal references | New reference-only termbox2/ncursesw fixtures and locked build configs | A01 fixture schema | Same terminal contract; correct restoration; direct-C and optional wrapped comparison |
| A09 GUI references | New reference-only Nuklear/microui/FLTK fixtures; optional LVGL lane | A01 fixture schema | Complete dependency accounting; core versus visible GUI categories kept separate |
| A10 Pack/load inventory | New pack metadata and dependency reports; proposes shared-root patches to A00 | A00 recipe schema; A02 | Required/later/absent inventory; no feature silently removed |
| A11 Independent certification | New cross-mode/system corpus and final reports, no production edits | Integrated work | Rebuild final SHA, run all mandatory lanes, certify or enumerate blockers |

A04 does not modify Tiny TUI files; A05 does not modify state/layout ownership. A10 does not independently edit the shared entry roots. A07 must not guess ownership of a platform factory. A00 publishes exact files before parallel edits start.

### 10.1 Dependency waves

```text
Wave 0: A00 baseline/ownership + A01 fixture and evidence contracts
            |
Wave 1: A03 normal TUI | A04 layout | A02 adapter | A08/A09 references
            |
Wave 2: A05 Tiny TUI | A06 wait/watch | A07 GUI | A10 pack closure
            |
Wave 3: A00 integrate -> A01 serialized measurements -> A11 certify
```

Reference fixture development can overlap with implementation. Measurement cannot overlap with other measurement or build activity. When a shared prerequisite changes, explicitly invalidate and rerun affected artifacts; do not mix baseline and integration binaries.

### 10.2 Branch, commit, and handoff rules

Use separate branches/worktrees, for example `perf/ui-slim/A03-screen-batching`, rooted at the pinned integration base. Keep mechanical moves, behavior-preserving refactors, optimization changes, and generated evidence in separate commits where practical. There is no required mass directory rename.

Every handoff includes baseline/head SHA; owned and changed paths; unchanged public contracts; exact commands and binary hashes; explicit pass/fail/skip counts; semantic and sabotage evidence; raw performance samples; loaded-provider inventory; known failures; and memory/parallelism limits. An exit code of zero without the expected assertions and a valid presented frame is not sufficient.

Agent-specific dispatch briefs are provided in the companion `simple_slim_ui_parallel_agent_briefs_2026-09-05.md`.

## 11. Landing sequence and rollback

**Phase 0 — establish truth.** Build or obtain qualified current native binaries, preserve them immutably, identify the real displayed GUI path, inventory current imports/providers, and freeze workloads and the evidence schema. A bootstrap-only binary that cannot exercise the product is `BLOCKED`, not a passing UI baseline.

**Phase 1 — local performance fixes.** Land normal TUI span batching, safe frame assembly, and Tiny layout optimization separately. Keep old routes for differential tests. Reuse the existing backend so the measured difference can be attributed to each change.

**Phase 2 — reusable buffers and waits.** Add private scratch reuse; improve event waiting and watcher reads without removing live reload. Validate idle, input latency and retained snapshots. Stop here to remeasure before adding foreign providers.

**Phase 3 — product closure.** Introduce exact composition recipes and coarse packs through existing contracts. Preserve old imports/APIs via façades. Show that unrelated products are absent from minimal artifacts and that every retained full feature still activates correctly.

**Phase 4 — optional foreign providers.** Benchmark qualified direct C/C++ references, then selected adapters. Keep the Simple backend default unless evidence and compatibility justify a change. Portability gaps produce an explicitly unavailable lane, not an unannounced backend substitution.

**Phase 5 — release qualification.** A11 rebuilds the integrated revision, runs platform and profile matrices, checks source/feature identity, and publishes the measured report. Roll back an individual optimization or recipe if parity fails; rollback must not require returning to a monolithic replacement architecture.

## 12. Definition of done

The project is complete only when a real minimal TUI and a real minimal GUI run through preserved Simple APIs; their required closures are documented and verified; unused providers are absent as intended; old/full products retain tested behavior; and before/after startup and memory results exist for pinned artifacts.

The report must show first-use costs, not only startup; include direct C/C++ references in their correct layer category; show no disabled validation or missing render path; and enumerate unsupported platforms and remaining performance hypotheses. The design is successful when removing unrelated work makes Simple smaller and faster **without making it a different or less capable product**.

---

## Source register

Repository sources below are pinned to the inspected revision. Symbols, not invented source-line numbers, identify findings.

| Ref | Source / relevant symbols |
|---|---|
| R01 | `src/lib/nogc_sync_mut/composition/provider_contract.spl` — provider query/result records, stable ABI comments |
| R02 | `src/lib/nogc_sync_mut/tiny/common/static_registry.spl` — register/query methods |
| R03 | `src/app/ui.tui/screen.spl` — `_screen_replace_row`, `put_text`, `draw_hline`, style helpers |
| R04 | `src/app/ui.tui/async_app.spl` — imports, constructor, run, watcher, render_frame |
| R05 | `src/lib/nogc_sync_mut/tiny/gui/state.spl` — add, resolved_panes, child scans |
| R06 | Tiny `tui/render.spl` and `tui/cell.spl` — fresh buffer, text conversion, cell creation/row text |
| R07 | `src/lib/nogc_sync_mut/tiny/engine2d/software.spl` — create, execute_stream, surface_receipt, fill_clipped, store_pixel |
| R08 | `src/lib/gui/pure_core.spl` — command batches, caller-supplied timing, hot probes |
| R09 | `examples/06_io/ui/hello_gui.spl` — example classification |
| R10 | `doc/09_report/startup_size_performance_audit_2026-05-27.md` — historical table, body dated May 29 |

### Recovered prior Library artifacts

- **P01:** `simple_lint_kernel_plugin_mdsocpp_research_design_parallel_plan_2026-09-03.md` — composition reuse, static dispatch, shared kernel façade, no rename-first migration.
- **P02:** `tiny_simple_ui_web_wm_research_design_plan.md` — TinyPane/TinyDrawStream, optional full-stack adapters, Tiny/host/SimpleOS separation.
- **P03:** `simple_startup_runtime_compiler_loader_performance_plan_2026-08-17.md` and its v2 — independent startup lanes, exact provider placement, agent evidence and release gates. Historical measurements were checked against R10 rather than treated as current results.

### Primary external sources, consulted September 5, 2026

[W01] termbox2 project and API description.  
[W02] ncurses project documentation.  
[W03] FTXUI project and component structure.  
[W04] microui project.  
[W05] Nuklear project, features and backend examples.  
[W06] LVGL project.  
[W07] FLTK project.  
[W08] Clay project and arena/capacity guidance.  
[W09] Linux kernel `/proc` documentation.

[R01]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/lib/nogc_sync_mut/composition/provider_contract.spl
[R02]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/lib/nogc_sync_mut/tiny/common/static_registry.spl
[R03]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/app/ui.tui/screen.spl
[R04]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/app/ui.tui/async_app.spl
[R05]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/lib/nogc_sync_mut/tiny/gui/state.spl
[R06]: https://github.com/ormastes/simple/tree/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/lib/nogc_sync_mut/tiny/tui
[R07]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/lib/nogc_sync_mut/tiny/engine2d/software.spl
[R08]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/src/lib/gui/pure_core.spl
[R09]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/examples/06_io/ui/hello_gui.spl
[R10]: https://github.com/ormastes/simple/blob/e0432cd7be29668138a4c47bf270cb5243ead8e4/doc/09_report/startup_size_performance_audit_2026-05-27.md
[W01]: https://github.com/termbox/termbox2
[W02]: https://invisible-island.net/ncurses/ncurses.html
[W03]: https://github.com/ArthurSonzogni/FTXUI
[W04]: https://github.com/rxi/microui
[W05]: https://github.com/Immediate-Mode-UI/Nuklear
[W06]: https://github.com/lvgl/lvgl
[W07]: https://www.fltk.org/
[W08]: https://github.com/nicbarker/clay
[W09]: https://docs.kernel.org/filesystems/proc.html
