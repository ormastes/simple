# 4KB Page Locality - Phase 2 Complete

**Date:** 2025-12-28
**Features:** #2010-#2019 (SDN Schema + Layout Config Loader)
**Status:** Complete

## Summary

Implemented SDN schema for layout configuration and integrated it into the compiler's project context. This enables projects to define code locality settings in `layout.sdn` files, including page budgets, function pattern matching, and anchor definitions.

## Features Implemented

### SDN Schema (#2010-#2014)

1. **LayoutConfig struct (#2010)** - Main configuration container with:
   - `page_size: u32` - Page size in bytes (default 4096)
   - `budgets: PhaseBudgets` - Page limits per phase
   - `patterns: PhasePatterns` - Glob-style function pattern matching
   - `anchor_patterns: AnchorPatterns` - Event loop and custom anchor detection
   - `recorded: Vec<RecordedFunction>` - Profiling data
   - `overrides: HashMap<String, LayoutPhase>` - Per-function overrides

2. **PhaseBudgets (#2011)** - Page budget per phase:
   - `startup: 8` - Default 32KB for startup code
   - `first_frame: 4` - Default 16KB for first frame
   - `steady: 0` - Unlimited
   - `cold: 0` - Unlimited

3. **PhasePatterns (#2012)** - Pattern-based phase assignment:
   - Supports `prefix_*`, `*_suffix`, `*contains*` patterns
   - Priority: startup → first_frame → cold → steady

4. **AnchorPatterns (#2013)** - Anchor function detection:
   - Built-in `event_loop` anchor
   - Custom anchors with pattern matching

5. **RecordedFunction (#2014)** - Profiling data structure:
   - Function name, phase, size, call count
   - Optional module path

### SDN Parser Support (#2015-#2017)

6. **SDN parsing (#2015)** - Parse layout configuration from SDN:
   - `LayoutConfig::from_file()` - Load from path
   - `LayoutConfig::from_str()` - Parse from string
   - `LayoutConfig::from_sdn_value()` - Parse from SdnValue

7. **Pattern matching (#2016)** - Glob-style pattern evaluation:
   - `pattern_matches()` - Simple glob matching
   - `PhasePatterns::find_phase()` - Find phase by function name

8. **SDN serialization (#2017)** - Export configuration:
   - `LayoutConfig::to_sdn()` - Serialize to SDN string

### Compiler Integration (#2018-#2019)

9. **ProjectContext integration (#2018)**:
   - Added `layout_config: Option<LayoutConfig>` field
   - Added `load_layout_config()` for automatic loading
   - `layout.sdn` auto-detected in project root

10. **Layout API methods (#2019)**:
    - `ProjectContext::layout_config()` - Get layout config
    - `ProjectContext::get_layout_phase()` - Get phase for function
    - `ProjectContext::is_layout_anchor()` - Check if function is anchor

## Files Created

- `src/compiler/src/hir/types/layout_config.rs` - Layout configuration types (~400 lines)
- `doc/spec/layout.sdn` - SDN schema example and documentation

## Files Modified

- `src/compiler/src/hir/types/mod.rs` - Added layout_config module
- `src/compiler/src/project.rs` - Integrated LayoutConfig loading
- `src/compiler/Cargo.toml` - Added simple-sdn dependency

## SDN Schema Example

```sdn
layout:
    page_size: 4096

    budgets:
        startup: 8
        first_frame: 4
        steady: 0
        cold: 0

    patterns:
        startup = [parse_*, init_*, setup_*]
        first_frame = [render_first_*, ui_init_*]
        cold = [help_*, error_*, debug_*]

    anchors:
        event_loop = [main_loop, event_loop, run_loop]

    recorded |function, phase, size, call_count|
        main, startup, 256, 1
        parse_args, startup, 512, 1
        event_loop, steady, 128, 50000
```

## Usage

Projects can now create a `layout.sdn` file in their root directory:

```bash
# Project structure
myproject/
├── simple.toml
├── layout.sdn     # <-- Layout configuration
└── src/
    └── main.spl
```

The layout configuration is automatically loaded by `ProjectContext` and can be used during compilation to assign layout phases to functions.

## Test Coverage

- Unit tests in `layout_config.rs` for pattern matching and config parsing
- Integration with ProjectContext tested via existing project tests

## Next Steps (Phase 3-7)

- Phase 3 (#2020-#2029): Test framework layout recording
- Phase 4 (#2030-#2039): Layout solver (bin packing)
- Phase 5 (#2040-#2049): SMF format extensions
- Phase 6: Native linker integration (ELF/PE)
- Phase 7: CLI commands (--layout-record, --layout-apply)

## Build Verification

```bash
cargo build -p simple-compiler  # Success (126 warnings)
cargo build --workspace         # Success
```
