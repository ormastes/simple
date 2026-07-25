# 4KB Page Locality - Phase 1 Complete

**Date:** 2025-12-28
**Features:** #2000-#2008 (Language & Parser + Compiler IR)
**Status:** Complete

## Summary

Implemented the foundation for 4KB page locality optimization, enabling code layout hints to minimize page faults during startup. Functions can now be annotated with execution phases (startup, first_frame, steady, cold) and anchor points (event_loop) to guide optimal code placement.

## Features Implemented

### Language & Parser (#2000-#2002)

1. **#[layout(phase="...")] attribute (#2000)** - Functions can be annotated with layout phases:
   ```simple
   #[layout(phase="startup")]
   fn parse_args(argv: []str) -> Args:
       ...
   ```

2. **#[layout(anchor="...")] attribute (#2001)** - Functions can be marked as anchor points:
   ```simple
   #[layout(anchor="event_loop")]
   fn event_loop(app: App):
       ...
   ```

3. **std.layout.mark() function (#2002)** - Runtime markers for profiling:
   ```simple
   import std.layout

   fn main():
       ...
       std.layout.mark("ui.ready")
       event_loop(app)
   ```

### Compiler IR (#2003-#2008)

4. **Parse layout attributes in AST (#2003)** - Extract layout hints from `#[layout(...)]`:
   - Supports `phase="startup|first_frame|steady|cold"`
   - Supports `anchor="event_loop|custom_name"`
   - Supports `pin` flag for pinned layout

5. **Store layout hints in HIR (#2004)** - `HirFunction.layout_hint` field with:
   - `layout_phase()` method
   - `is_event_loop_anchor()` method
   - `is_layout_pinned()` method

6. **Emit layout metadata to MIR (#2005)** - `MirFunction` fields:
   - `layout_phase: LayoutPhase`
   - `is_event_loop_anchor: bool`

7. **LayoutPhase enum in compiler (#2006)** - Phase taxonomy:
   - `Startup` - Process entry → main loop
   - `FirstFrame` - Main loop → first render
   - `Steady` - Normal execution (default)
   - `Cold` - Rarely executed code

8. **Validate layout annotations (#2007)** - Attribute validation in lowerer

9. **Store layout in SMF symbols (#2008)** - Symbol flags encoding:
   - Bits 0-1: Layout phase (0=startup, 1=first_frame, 2=steady, 3=cold)
   - Bit 2: Event loop anchor flag
   - Bit 3: Layout pinned flag

## Files Created

- `src/compiler/src/hir/types/code_layout.rs` - LayoutPhase, LayoutAnchor, FunctionLayoutHint, PageBudget
- `simple/std_lib/src/layout/__init__.spl` - Layout module manifest
- `simple/std_lib/src/layout/markers.spl` - mark() function and convenience wrappers

## Files Modified

- `src/compiler/src/hir/types/mod.rs` - Added code_layout module
- `src/compiler/src/hir/types/functions.rs` - Added layout_hint field to HirFunction
- `src/compiler/src/hir/lower/module_lowering.rs` - Added extract_layout_hint method
- `src/compiler/src/mir/function.rs` - Added layout_phase and is_event_loop_anchor fields
- `src/compiler/src/mir/lower/lowering_core.rs` - Propagate layout from HIR to MIR
- `src/compiler/src/interpreter_extern.rs` - Added simple_layout_mark FFI handler
- `src/compiler/src/linker/smf_writer.rs` - Added layout fields to SmfSymbol
- `src/loader/src/smf/symbol.rs` - Added LayoutPhaseFlag enum and symbol_flags module
- `src/compiler/src/arch_rules.rs` - Updated test for new HirFunction field

## Test Coverage

- Unit tests in `code_layout.rs` for phase parsing and priority
- Layout attribute extraction tested via existing lowering tests
- SMF writer tests updated with layout fields

## Next Steps (Phase 2-7)

- Phase 2 (#2010-#2019): SDN schema for layout configuration
- Phase 3 (#2020-#2029): Test framework layout recording
- Phase 4 (#2030-#2039): Layout solver (bin packing)
- Phase 5 (#2040-#2049): SMF format extensions
- Phase 6: Native linker integration (ELF/PE)
- Phase 7: CLI commands (--layout-record, --layout-apply)

## Build Verification

```bash
cargo build -p simple-compiler  # Success
cargo build -p simple-loader    # Success
```
