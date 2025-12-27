# Feature Documentation Structure

This directory contains organized feature documentation for Simple Language.

## Directory Structure

```
doc/features/
├── feature.md              # Main feature overview and statistics
├── __index__.md            # This file - directory structure guide
├── _template.md            # Template for individual feature files
│
├── infrastructure/         # Core compiler infrastructure (#1-#9)
│   ├── __index__.md
│   └── *.md               # Individual feature files
│
├── language/              # Language features
│   ├── core/              # Core language features (#10-#49)
│   ├── metaprogramming/   # Macros, DSL, decorators (#1300-#1324)
│   ├── types/             # Type system extensions (#1330-#1342)
│   └── pattern_matching/  # Pattern matching safety (#1325-#1329)
│
├── codegen/               # Code generation (#95-#103)
│
├── concurrency/           # Concurrency features (#1104-#1115, #1730-#1779)
│
├── testing/               # Testing frameworks
│   ├── bdd/               # BDD spec framework (#180-#188, #1343-#1347)
│   └── doctest/           # Documentation testing (#192-#197)
│
├── verification/          # Formal verification (#950-#970, #1840-#1909)
│
├── aop/                   # AOP & Unified Predicates (#1000-#1050, #1391-#1403)
│
├── tooling/               # Development tools
│   ├── multi_language/    # Multi-language support (#1180-#1199)
│   ├── tree_sitter/       # Tree-sitter integration (#1156-#1179)
│   └── dev_tools/         # LSP, DAP (#1359-#1368)
│
├── mcp/                   # MCP Protocol (#1200-#1299, #1348-#1358)
│
├── ui/                    # UI frameworks
│   ├── tui/               # Terminal UI (#1369-#1378, #1830-#1839)
│   ├── gui/               # Desktop GUI
│   ├── electron/          # Electron apps (#1404-#1420)
│   └── vscode/            # VSCode extension (#1421-#1450)
│
├── gpu/                   # GPU computing
│   ├── simd/              # SIMD operations (#400-#404)
│   └── vulkan/            # Vulkan backend (#1450-#1509)
│
├── graphics/              # 3D Graphics (#1780-#1829)
│
├── game_engine/           # Game engine integration
│   ├── godot/             # Godot integration (#1520-#1567)
│   ├── unreal/            # Unreal Engine (#1568-#1595)
│   └── physics/           # Physics engine (#1590-#1649)
│
├── ml/                    # Machine learning (#1650-#1729)
│
├── database/              # Database abstraction (#700-#799)
│
├── sdn/                   # SDN format (#1051-#1060)
│
├── llm_friendly/          # LLM-friendly features (#880-#919)
│
├── formatting/            # Formatter & lints (#1131-#1145)
│
├── ffi/                   # FFI/ABI interface (#1116-#1130)
│
├── optimization/          # Performance optimization (#1970-#2049)
│
├── math/                  # Simple Math (#1910-#1969)
│
└── done/                  # Archived completed feature batches
    └── feature_done_*.md  # Historical archives
```

## Feature File Format

Each feature has its own markdown file following `_template.md`. The files are:
- Named by feature ID: `{id}_{short_name}.md` (e.g., `0001_lexer.md`)
- Generated from BDD system tests when available
- Manually maintained for planned features

## BDD Test Integration

Feature files can be auto-generated from BDD system tests:

```simple
# In simple/std_lib/test/system/features/infrastructure/lexer_spec.spl
describe "Feature #1: Lexer":
    @feature_id: 1
    @feature_name: "Lexer"
    @difficulty: 3
    @status: "complete"
    @impl: "R"

    it "tokenizes basic identifiers":
        # test code...
```

The test runner exports feature documentation to corresponding `.md` files.

## Status Legend

- `✅` Complete - Fully implemented and tested
- `📋` Planned - Designed, not yet implemented
- `🔄` In Progress - Partially implemented

## Related Documentation

- [feature.md](feature.md) - Main feature overview and statistics
- [CLAUDE.md](../../CLAUDE.md) - Development guide
- [spec/](../spec/) - Language specifications
