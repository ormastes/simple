# 4KB Page Locality Implementation Plan

**Date:** 2025-12-28
**Status:** Planned
**Feature Range:** #2000-#2049 (50 features)
**Goal:** Minimize page faults during startup by grouping code into 4KB blocks

## Overview

Implement scenario-driven 4KB code/page grouping to minimize cold start time for TUI/GUI applications. This involves:

1. Language additions for phase annotations (`#[layout]` attributes)
2. System test integration for scenario recording
3. Layout solver to pack functions into 4KB pages
4. SMF format extensions for layout metadata
5. Native linker integration (ELF/PE ordering)
6. Profiling infrastructure for main scenarios

## Design Goals

| Goal | Description |
|------|-------------|
| G1 | Minimize distinct 4KB pages touched from process start to event_loop entry |
| G2 | Use system tests as source of truth for "main scenarios" |
| G3 | Keep language surface small - reuse `#[...]` attribute style |
| G4 | Support both SMF layout and native toolchain (ELF/PE) |
| G5 | Startup code fits in ≤8 pages (32KB) for optimal cache utilization |

## Phase Taxonomy

| Phase | Description | Budget |
|-------|-------------|--------|
| `startup` | Process entry → before main loop | 8 pages (32KB) |
| `first_frame` | Main loop entry → first render | 12 pages (48KB) |
| `steady` | Hot paths during event loop | No limit |
| `cold` | Rarely used code | No limit |

## Feature Breakdown

### Phase 1: Language & Parser (#2000-#2009)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2000 | `#[layout(phase="...")]` attribute | 3 | S+R | Phase annotation on functions |
| #2001 | `#[layout(anchor="...")]` attribute | 2 | S+R | Event loop boundary marker |
| #2002 | `std.layout.mark()` function | 2 | S+R | Runtime phase marker |
| #2003 | Parse layout attributes in AST | 3 | R | Parser support for layout |
| #2004 | Store layout hints in HIR | 2 | R | Preserve through lowering |
| #2005 | Emit layout metadata to MIR | 2 | R | Function-level phase tags |
| #2006 | Layout phase enum in compiler | 1 | R | Phase type definitions |
| #2007 | Validate layout annotations | 2 | R | Check phase/anchor values |
| #2008 | Layout attribute in SMF symbols | 2 | R | Store phase in symbol table |
| #2009 | Reserved for future use | - | - | - |

**Total: 9 features**

### Phase 2: Profiling & Recording (#2010-#2019)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2010 | `--layout-record` test flag | 2 | R | Enable scenario recording |
| #2011 | Symbol trace recorder | 4 | R | Track executed functions |
| #2012 | Scenario entry/stop detection | 3 | R | Detect mark() boundaries |
| #2013 | Call graph extraction | 3 | R | Build caller→callee edges |
| #2014 | Function size measurement | 2 | R | Get code size per function |
| #2015 | Frequency counter per scenario | 2 | R | Count function calls |
| #2016 | Profile data persistence | 2 | R | Save to layout.sdn |
| #2017 | Profile merge (multi-scenario) | 3 | R | Combine scenario profiles |
| #2018 | Profile validation | 2 | R | Check data consistency |
| #2019 | Reserved for future use | - | - | - |

**Total: 9 features**

### Phase 3: SDN Layout Schema (#2020-#2024)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2020 | LayoutScenario SDN table | 2 | S | Scenario definitions |
| #2021 | LayoutGroup SDN table | 2 | S | Phase group config |
| #2022 | LayoutSymbolHint SDN table | 2 | S | Per-symbol hints |
| #2023 | LayoutProfile SDN table | 2 | S | Profile data storage |
| #2024 | SDN schema validation | 2 | R | Validate layout.sdn |

**Total: 5 features**

### Phase 4: Layout Solver (#2025-#2034)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2025 | Hotness score calculator | 3 | R | H(f) = Σ weight × freq |
| #2026 | Call graph clustering | 4 | R | Group callers/callees |
| #2027 | First-Fit Decreasing packer | 4 | R | Pack into 4KB bins |
| #2028 | Phase budget enforcement | 2 | R | Respect max_pages |
| #2029 | Alignment boundary insertion | 2 | R | 4KB align at phase transition |
| #2030 | Symbol ordering output | 2 | R | Generate final order |
| #2031 | `simple layout solve` command | 2 | R | CLI for solver |
| #2032 | Layout plan visualization | 3 | R | ASCII/graphical output |
| #2033 | Layout diff tool | 2 | R | Compare layouts |
| #2034 | Layout statistics | 2 | R | Report page counts |

**Total: 10 features**

### Phase 5: SMF Layout Support (#2035-#2039)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2035 | LAYOUT_HDR SMF section | 3 | R | Group offsets/lengths |
| #2036 | LAYOUT_SYM SMF section | 2 | R | Symbol→offset mapping |
| #2037 | LAYOUT_HINT SMF section | 2 | R | Pinned symbols, phase tags |
| #2038 | SMF rewriter for layout | 4 | R | Reorder code sections |
| #2039 | Loader prefetch by group | 3 | R | Prefetch startup pages |

**Total: 5 features**

### Phase 6: Native Linker Integration (#2040-#2044)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2040 | ELF section naming by phase | 3 | R | .text.spl.startup.<fn> |
| #2041 | Linker ordering script gen | 4 | R | GNU ld script output |
| #2042 | LLD symbol ordering file | 3 | R | --symbol-ordering-file |
| #2043 | MSVC /ORDER file generation | 3 | R | Windows PE ordering |
| #2044 | Custom linker wrapper | 4 | R | simple-ld with layout |

**Total: 5 features**

### Phase 7: Test Framework Integration (#2045-#2049)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #2045 | Scenario tag in BDD tests | 2 | S+R | `@layout_scenario` tag |
| #2046 | Main scenario auto-detection | 3 | R | Detect entry/stop |
| #2047 | Profile-guided test ordering | 3 | R | Run hot scenarios first |
| #2048 | Layout coverage report | 3 | R | % of startup in 8 pages |
| #2049 | CI layout regression check | 3 | R | Fail if pages exceed budget |

**Total: 5 features**

## Implementation Summary

| Phase | Features | Description |
|-------|----------|-------------|
| Phase 1 | 9 | Language & Parser |
| Phase 2 | 9 | Profiling & Recording |
| Phase 3 | 5 | SDN Layout Schema |
| Phase 4 | 10 | Layout Solver |
| Phase 5 | 5 | SMF Layout Support |
| Phase 6 | 5 | Native Linker Integration |
| Phase 7 | 5 | Test Framework Integration |
| **Total** | **48** | (2 reserved) |

## Language Syntax

### Phase Annotations

```simple
#[layout(phase="startup")]
fn parse_args(argv: []str) -> Args:
    ...

#[layout(phase="first_frame")]
fn render_first_frame(ui: Ui):
    ...

#[layout(phase="cold")]
fn open_help_modal(ui: Ui):
    ...
```

### Event Loop Anchor

```simple
#[layout(anchor="event_loop")]
fn event_loop(ui: Ui):
    loop:
        ev = ui.next_event()
        handle_event(ev)
        ui.render()
```

### Runtime Marker

```simple
import std.layout

fn main():
    app = init_everything()
    first_frame(app)
    std.layout.mark("ui.ready")  # Stop startup measurement
    event_loop(app)
```

## SDN Schema

### layout.sdn

```sdn
# Layout configuration
LayoutGroup:
  - { phase: "startup",     page_size: 4096, max_pages: 8,  align_pages: true }
  - { phase: "first_frame", page_size: 4096, max_pages: 12, align_pages: true }
  - { phase: "steady",      page_size: 4096, max_pages: 0,  align_pages: false }
  - { phase: "cold",        page_size: 4096, max_pages: 0,  align_pages: false }

# Scenario definitions
LayoutScenario:
  - { name: "tui_boot",   entry: app.main,            stop_mark: "ui.ready", phase: "startup",  weight: 1.0 }
  - { name: "gui_boot",   entry: gui.main,            stop_mark: "ui.ready", phase: "startup",  weight: 1.0 }
  - { name: "open_file",  entry: ui.commands.open,    stop_mark: "cmd.done", phase: "steady",   weight: 0.5 }

# Symbol hints (override profile)
LayoutSymbolHint:
  - { symbol: ui.render.draw_frame, phase: "first_frame", pin: true }
  - { symbol: std.io.write,         phase: "startup",     pin: true }

# Profile data (generated by --layout-record)
LayoutProfile:
  - { symbol: main,           scenario: "tui_boot", calls: 1,    size: 256 }
  - { symbol: parse_args,     scenario: "tui_boot", calls: 1,    size: 512 }
  - { symbol: init_terminal,  scenario: "tui_boot", calls: 1,    size: 1024 }
  - { symbol: build_ui,       scenario: "tui_boot", calls: 1,    size: 2048 }
```

## CLI Commands

### Recording

```bash
# Record symbol traces during system tests
simple test --layout-record tests/system/

# Record specific scenario
simple test --layout-record --scenario=tui_boot tests/system/tui_spec.spl

# Output: build/layout/layout.sdn
```

### Solving

```bash
# Solve layout ordering
simple layout solve build/layout/layout.sdn -o build/layout/order.txt

# With visualization
simple layout solve --visualize build/layout/layout.sdn

# Check budget compliance
simple layout check build/layout/order.txt --max-startup-pages=8
```

### Applying

```bash
# Apply to SMF
simple compile --layout-apply build/layout/order.txt src/main.spl -o app.smf

# Apply to native ELF
simple compile --layout-apply build/layout/order.txt --native src/main.spl -o app

# Generate linker script only
simple layout emit-linker-script build/layout/order.txt -o layout.ld
```

## SMF Format Extensions

### LAYOUT_HDR Section

```
Offset  Size  Field
0       4     magic ("LHDR")
4       4     version (1)
8       4     page_size (4096)
12      4     group_count
16      N*16  groups[]:
              - phase (4 bytes, enum)
              - offset (4 bytes)
              - length (4 bytes)
              - flags (4 bytes)
```

### LAYOUT_SYM Section

```
Offset  Size  Field
0       4     magic ("LSYM")
4       4     symbol_count
8       N*12  symbols[]:
              - symbol_id (4 bytes)
              - offset (4 bytes, relative to code section)
              - size (4 bytes)
```

## Linker Integration

### ELF Section Naming

```
.text.spl.startup.main
.text.spl.startup.parse_args
.text.spl.startup.init_terminal
.text.spl.first_frame.render_first_frame
.text.spl.first_frame.draw_widgets
.text.spl.steady.handle_input
.text.spl.cold.show_help
```

### GNU ld Script

```ld
SECTIONS {
  .text : {
    /* Startup phase - first 8 pages */
    . = ALIGN(4096);
    __startup_start = .;
    *(.text.spl.startup.*)
    . = ALIGN(4096);
    __startup_end = .;

    /* First frame phase - next 12 pages */
    __first_frame_start = .;
    *(.text.spl.first_frame.*)
    . = ALIGN(4096);
    __first_frame_end = .;

    /* Steady phase */
    *(.text.spl.steady.*)

    /* Cold phase */
    *(.text.spl.cold.*)

    /* Everything else */
    *(.text*)
  }
}
```

### LLD Symbol Ordering File

```
# Generated by: simple layout emit-lld-order
main
parse_args
init_terminal
build_ui
render_first_frame
# --- first_frame boundary ---
draw_widgets
handle_input
# --- steady boundary ---
show_help
```

### MSVC /ORDER File

```
# Generated by: simple layout emit-msvc-order
?main@@YAHXZ
?parse_args@@YA...
?init_terminal@@YA...
```

## Test Framework Integration

### BDD Scenario Tags

```simple
# tests/system/tui_spec.spl

@layout_scenario(name="tui_boot", stop_mark="ui.ready", weight=1.0)
describe "TUI Application":
    context "startup":
        it "boots within 8 pages":
            app = App.new()
            app.run()
            expect(app.ui_ready).to_be_true()
```

### Profile-Guided Test Ordering

```bash
# Run tests with layout profiling
simple test --layout-record --profile-order tests/system/

# Tests are reordered based on scenario weights:
# 1. tui_boot (weight=1.0)
# 2. gui_boot (weight=1.0)
# 3. open_file (weight=0.5)
# ...
```

### Layout Coverage Report

```
=== Layout Coverage Report ===

Startup Phase (budget: 8 pages = 32KB):
  Actual: 6 pages (24KB) ✅
  Functions: 12
  Hottest: init_terminal (1024 bytes, 100% coverage)

First Frame Phase (budget: 12 pages = 48KB):
  Actual: 8 pages (32KB) ✅
  Functions: 18
  Hottest: draw_widgets (2048 bytes, 100% coverage)

Uncovered Functions in Startup Path: 0 ✅

=== PASS: Within budget ===
```

## Custom Linker Architecture

### simple-ld Wrapper

```
┌─────────────────────────────────────────────────────────┐
│                     simple-ld                           │
├─────────────────────────────────────────────────────────┤
│  1. Parse layout.sdn                                    │
│  2. Generate linker script / ordering file              │
│  3. Invoke system linker (ld/lld/link.exe)              │
│  4. Verify output layout                                │
│  5. Report page statistics                              │
└─────────────────────────────────────────────────────────┘
         │                    │                    │
         ▼                    ▼                    ▼
    ┌─────────┐         ┌─────────┐         ┌─────────┐
    │ GNU ld  │         │  LLD    │         │MSVC link│
    └─────────┘         └─────────┘         └─────────┘
```

### Workflow

```bash
# Full workflow
simple test --layout-record tests/system/    # Record profiles
simple layout solve build/layout/layout.sdn  # Compute ordering
simple compile --layout-apply build/layout/order.txt src/main.spl

# Or single command
simple build --optimize-layout src/main.spl
```

## Performance Targets

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| Startup pages touched | 50+ | ≤8 | 84% fewer |
| First frame pages | 80+ | ≤20 | 75% fewer |
| Page faults (cold) | 100+ | ≤25 | 75% fewer |
| Time to event loop | 150ms | 50ms | 67% faster |
| Time to first frame | 250ms | 100ms | 60% faster |

## Dependencies

- **Existing:** SMF loader, compiler pipeline, BDD test framework
- **New:** Profile recording infrastructure, layout solver algorithm
- **External:** System linker (ld/lld/link.exe) for native builds

## Testing Strategy

1. **Unit Tests:** Layout solver algorithm, SDN parsing
2. **Integration Tests:** Full record→solve→apply pipeline
3. **Benchmark Tests:** Measure actual page fault reduction
4. **Regression Tests:** Ensure layout doesn't exceed budget

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| LTO may inline/merge symbols | Apply layout post-LTO or use stable symbol IDs |
| Padding wastes space | Use budgets (max_pages) to cap damage |
| Profile data staleness | Re-record periodically, add CI check |
| Linker compatibility | Support multiple linkers, test on CI |

## Implementation Priority

1. **MVP (2 weeks):** Phase annotations, basic profiling, SMF rewriter
2. **Full (4 weeks):** Layout solver, native linker support
3. **Polish (2 weeks):** Test integration, CI checks, visualization

## Related Documentation

- [binary_locality.md](../research/binary_locality.md) - Research document
- [startup_optimization_implementation.md](startup_optimization_implementation.md) - Previous optimization work
- [feature.md](../features/feature.md) - Feature tracking

## Next Steps

1. Add #2000-#2049 to feature.md
2. Implement Phase 1: Language & Parser
3. Build profiling infrastructure
4. Create layout solver
5. Integrate with SMF and native linkers
