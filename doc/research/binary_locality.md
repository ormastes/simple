Simple Spec Proposal: Scenario-Driven 4KB Code/Page Grouping for Faster Cold Start (TUI/GUI)

1) Motivation: why “4KB grouping” matters

Modern Linux/Windows loaders primarily map executable segments into memory and then rely on demand paging: the CPU faults in 4KB pages as instructions/data are first touched. Cold start time is often dominated by:

Instruction page faults (many distinct 4KB pages touched before “first frame” / event loop)

Relocation / dynamic linking work (especially with many DSOs/DLLs)

I/O locality (reading scattered pages from disk)


Therefore, a practical lever is code locality: pack “startup path” and “first-frame path” into as few 4KB pages as possible, and keep those pages early/contiguous in the binary and/or mapped segments.

In Simple, this fits the project direction because you already have a compiled artifact format (SMF) and a loader subsystem, and you support attributes (#[...]) and a testing ecosystem that can define “main scenarios.” 


---

2) Design goals

G1. Minimize the number of distinct 4KB pages touched from process start until:

event_loop() entry (TUI/GUI steady state), and

“first frame rendered” / “UI ready” marker.


G2. Use system tests as the source of truth for “main scenarios,” so layout optimizes what you actually validate.

G3. Keep the language surface small and parser-friendly: reuse Simple’s attribute style (#[...]) and indent blocks. 

G4. Support both:

SMF layout (Simple loader can exploit it directly), and

native toolchain layout (ELF on Linux, PE/COFF on Windows) via linker ordering features. 



---

3) Core concept: “Phases” and “Scenario groups”

We introduce a layout phase taxonomy:

startup: process entry → just before entering the TUI/GUI main loop

first_frame: main loop entry → first successful render / “ready”

steady: hot paths during the loop (input handling, rendering, hot commands)

cold: everything else (rare commands, help text, seldom-used features)


Each scenario defines:

entry: where it starts (usually main or a command handler)

stop marker: when measurement stops (e.g., “ui.ready”)

weight: importance in the final packing/order



---

4) Language additions (spec-level)

4.1 Attributes

Use Simple’s existing attribute form (as seen with #[gpu]). 

A) Phase annotation on functions

#[layout(phase="startup")]
fn parse_args(argv: []str) -> Args:
    ...

#[layout(phase="first_frame")]
fn render_first_frame(ui: Ui):
    ...

#[layout(phase="cold")]
fn open_help_modal(ui: Ui):
    ...

Semantics:

The compiler emits a function section tag (or SMF equivalent) encoding the phase.

If profile data contradicts annotations, the compiler may warn (policy-controlled).


B) Anchors to define “before loop” boundary

#[layout(anchor="event_loop")]
fn event_loop(ui: Ui):
    ...

Semantics:

Establishes a hard boundary: everything needed before this is a candidate for the tightest startup packing.


C) Explicit marker call (runtime-visible)

import std.layout

fn main():
    ...
    std.layout.mark("ui.ready")
    event_loop(ui)

Semantics:

mark("ui.ready") is used by the profiler/recorder to stop the “startup/first_frame” trace.


4.2 Scenario declaration in system tests (config-driven)

System tests define which flows matter. The test runner records symbol traces for each scenario.

A minimal file-based declaration (kept outside the parser-critical path) is recommended.


---

5) SDN-based layout plan (produced by tests, consumed by compiler)

A build produces a layout plan artifact, e.g. build/layout/layout.sdn.

5.1 SDN table sketch

(Names are illustrative; align with your SDN conventions.)

table LayoutScenario {
  name: Str
  entry: Symbol          # e.g., app.main, ui.commands.open_file
  stop_mark: Str         # e.g., "ui.ready"
  phase: Str             # "startup" | "first_frame" | "steady"
  weight: F64            # relative importance
}

table LayoutGroup {
  phase: Str             # startup | first_frame | steady | cold
  page_size: I64         # default 4096
  max_pages: I64         # budget (e.g., startup=8 pages)
  align_pages: Bool      # align group boundary to 4096
}

table LayoutSymbolHint {
  symbol: Symbol
  phase: Str
  pin: Bool              # if true, do not move out of phase group
}

5.2 Example plan (what the tool writes)

LayoutGroup:
  - { phase: "startup",     page_size: 4096, max_pages: 8,  align_pages: true }
    - { phase: "first_frame", page_size: 4096, max_pages: 12, align_pages: true }
      - { phase: "steady",      page_size: 4096, max_pages: 0,  align_pages: false }
        - { phase: "cold",        page_size: 4096, max_pages: 0,  align_pages: false }

        LayoutScenario:
          - { name: "tui_boot", entry: app.main, stop_mark: "ui.ready", phase: "startup", weight: 1.0 }
            - { name: "open_file", entry: ui.commands.open_file, stop_mark: "cmd.done", phase: "steady", weight: 0.3 }

            LayoutSymbolHint:
              - { symbol: ui.render.draw_frame, phase: "first_frame", pin: true }


              ---

              6) Tooling workflow: record → solve → apply

              6.1 Record (system tests drive truth)

              Add a test-mode flag:

              simple test --layout-record

              Runs selected system scenarios

              Records executed function symbols between:

              scenario entry → mark(stop_mark)


              Emits layout.sdn with per-scenario symbol frequency + call edges (if available)



              6.2 Solve (pack into 4KB “pages”)

              The compiler (or a dedicated simple layout solve) computes an ordering:

              Inputs

              (A) profile weights per symbol per scenario

              (B) optional static call graph (fallback)

              (C) function sizes (from codegen)

              (D) phase budgets (max_pages)


              Outputs

              An ordered list of symbols, partitioned into “page groups”

              Optional “alignment boundaries” at group transitions


              Heuristic that works well in practice:

              1. Build a hotness score H(f) = Σ scenario_weight × freq(f, scenario)


              2. Cluster by call edges (keep callers + callees near)


              3. Greedy pack into 4096-byte bins (First-Fit Decreasing by H(f) with adjacency bias)


              4. Emit final order: startup bins → first_frame bins → steady → cold



              6.3 Apply (SMF + native)

              For SMF: rewrite SMF’s code section order physically, and align group boundaries to 4096 bytes (see §7).

              For native ELF: emit linker ordering directives (see §8.1).

              For native Windows PE/COFF: emit an /ORDER:@file list (see §8.2).



              ---

              7) SMF format support (recommended, because Simple controls the loader)

              Simple’s SMF goal (“compile once, run anywhere”) plus a dedicated loader makes SMF the ideal place to guarantee layout. 

              7.1 SMF additions

              Add optional chunks:

              LAYOUT_HDR:

              page_size (4096)

              list of groups with offsets + lengths (startup/first_frame/…)


              LAYOUT_SYM:

              symbol → offset mapping (post-layout)


              LAYOUT_HINT:

              pinned symbols, phase tags (for debugging)



              7.2 Loader behavior

              When SMF is mmap’d:

              The loader can prefetch the startup group range (one sequential read) before jumping to entry.

              The loader can keep metadata needed before event_loop in the first few pages.


              This directly realizes your requirement: “code before main/event loop at front by 4KB block.”


              ---

              8) Native integration (Linux + Windows)

              8.1 Linux/ELF: section ordering files / linker scripts

              A robust path is:

              compile with per-function sections (or equivalent)

              apply a linker section ordering plan


              GNU ld documents --section-ordering-file=script, where the script uses linker-script SECTIONS placement syntax to map input sections into output sections. 
              In the LLVM ecosystem, lld also supports ordering mechanisms (including --symbol-ordering-file), and practical guidance for section ordering is widely used for layout experiments. 

              Simple output idea (ELF):

              emit functions into input sections named by phase, e.g.:

              .text.spl.startup.<fn>

              .text.spl.first_frame.<fn>

              .text.spl.cold.<fn>


              generate an ordering file/script that places:

              1. startup sections first, aligned


              2. first_frame next, aligned


              3. others later




              8.2 Windows/PE/COFF: linker ordering (/ORDER)

              MSVC’s linker supports /ORDER to specify placement ordering (via an order file).
              This can be used to bring startup symbols earlier and cluster scenario-hot code.

              Simple output idea (Windows):

              generate layout.order.txt listing decorated symbol names in desired order

              pass /ORDER:@layout.order.txt



              ---

              9) TUI/GUI example (what you asked for)

              9.1 App code: isolate the “pre-loop” path

              import std.layout
              import tui

              #[layout(phase="startup")]
              fn init_everything() -> App:
                  args = parse_args()
                  cfg  = load_config(args.config_path)
                  term = tui.init_terminal()
                  ui   = tui.build_ui(cfg, term)
                  return App(ui: ui, cfg: cfg)

              #[layout(phase="first_frame")]
              fn first_frame(app: App):
                  app.ui.render()
                  std.layout.mark("ui.ready")

              #[layout(anchor="event_loop")]
              fn event_loop(app: App):
                  loop:
                      ev = app.ui.next_event()
                      handle_event(app, ev)
                      app.ui.render()

              fn main() -> i64:
                  app = init_everything()
                  first_frame(app)
                  event_loop(app)
                  return 0

              9.2 System test defines the “main scenario”

              Your system test runner (BDD or otherwise) declares:

              entry: main

              stop mark: ui.ready

              scenario name: tui_boot


              Then simple test --layout-record generates layout.sdn, and simple compile --layout-apply layout.sdn reorders code pages accordingly.


              ---

              10) Rust perspective (how to get similar wins)

              Rust binaries are often “big” and cold start can suffer when many pages are touched early. The same playbook applies:

              PGO for call frequency

              function/section ordering via linker support

              post-link layout tools (BOLT / Propeller-style workflows) when available

              delay-load optional features (Windows) to move DLL costs out of startup


              Ordering support examples:

              ELF linkers support ordering files / scripts (binutils --section-ordering-file). 

              lld exposes symbol ordering (--symbol-ordering-file). 

              MSVC supports /ORDER.


              If you want “first frame” faster in Rust TUI apps, a pragmatic pattern is:

              keep initialization minimal before entering the event loop

              defer heavyweight features behind first user input

              cluster “boot path” code (order files) and avoid pulling large subsystems into the initial call graph



              ---

              11) Notes on PIC/relocations (your earlier question, condensed)

              “Reducing relocations” is not the same as “cannot use PIC.”

              PIC/PIE changes how addresses are formed; relocations still exist (especially with dynamic linking), just of different kinds.

              Layout optimization (4KB grouping / order files) is compatible with PIE/PIC; it’s primarily about where code lands, not whether it relocates.



              ---

              12) Practical trade-offs and guardrails

              Padding/aligning to 4096 can increase file size; use budgets (max_pages) to cap damage.

              LTO/inlining can erase or merge symbols; apply layout late (post-LTO) or use a stable symbol identity scheme in SMF.

              Always keep a “debug build ignores layout” policy to preserve developer ergonomics.



              ---

              If you want, I can also turn this into a drop-in doc/spec/layout_startup_pages.md style page with:

              a formal grammar snippet for #[layout(...)],

              SDN schema exactly matching your SDN conventions,

              and CLI spec for simple test --layout-record / simple compile --layout-apply.</fn>
}
}
}
