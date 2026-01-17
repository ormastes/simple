# Simple Language - TODO Status Report

**Date:** 2026-01-17 (Updated)
**Previous Date:** 2026-01-16

---

## Executive Summary

**Total TODOs:** 772

| Priority | Count | Percentage | Notes |
|----------|-------|------------|-------|
| P1 (High) | 153 | 20% | Many in concurrency/async specs |
| P2 (Medium) | 59 | 8% | Mixed: Godot, tooling, parsing |
| P3 (Low) | 414 | 54% | Vulkan UI, stdlib, tooling |
| Untagged | 146 | 19% | Needs triage |

**Key Changes from Previous Report:**
- Total count increased from 119 to 772 (comprehensive scan)
- Previous report only counted src/ directory; this includes simple/ (stdlib + apps)
- No monoio P1 blockers found in current scan (may have been resolved)

---

## P1 TODOs - High Priority (153 items)

### By Area

#### Concurrency Features (49 items)
Placeholder tests awaiting language feature implementation:
- `suspension_operator_spec.spl` (12 items) - `~=` operator support
- `promise_type_spec.spl` (16 items) - Promise type implementation
- `effect_inference_spec.spl` (13 items) - Effect inference system
- `async_default_spec.spl` (8 items) - Async-default mode

#### UI/Vulkan (22 items)
- `vulkan.spl` (10 items) - Layout algorithms, incremental updates
- `vulkan_types.spl` (3 items) - Queue handles, implement functions
- `hot_reload.spl` (4 items) - File system operations
- `vscode.spl` (2 items) - Secure random generation
- `browser.spl` (2 items) - Event dispatch
- `vulkan/layout.spl` (1 item) - Layout algorithm

#### Compiler/Parser (11 items)
- `watch.spl` (3 items) - File watching, formatting, linting
- `build.spl` (1 item) - File watching
- `parser/treesitter/` (4 items) - Sibling/parent navigation, grammar loading
- `mode_config_parser.spl` (3 items) - SDN/TOML/attribute parsing

#### Interpreter (14 items)
- `expr/__init__.spl` (3 items) - Indexing, field access, lambda
- `async_runtime/actors.spl` (3 items) - Handler invoke, message requeue, pattern match
- `ffi/builtins.spl` (2 items) - Proper comparison
- `ffi/extern.spl` (2 items) - Type marshalling
- `helpers/macros.spl` (1 item) - Sequence matching
- `control/match.spl` (1 item) - Struct pattern matching
- `expr/calls.spl` (1 item) - Closure calls
- `async_runtime/futures.spl` (1 item) - Proper polling

#### LSP/MCP (8 items)
- `lsp/handlers/completion.spl` (2 items) - Context analysis, prefix extraction
- `lsp/handlers/references.spl` (1 item) - Scope-based filtering
- `mcp/main.spl` (1 item) - Search across files
- `mcp/core/transport.spl` (3 items) - TCP reading/writing
- `mcp/advanced.spl` (1 item) - Protobuf encoding

#### Stdlib Core (25 items)
- `io/fs.spl` (1 item) - Variant selection
- `lms/server.spl` (1 item) - Resource reading
- `spec/mode_runner.spl` (2 items) - Mode switching, error handling
- `spec/property/runner.spl` (1 item) - Timeout mechanism
- `core/decorators.spl` (1 item) - Timeout mechanism
- `vscode/` (4 items) - LSP handler, JSON serialization
- `tooling/` (15 items) - Various compiler/testing/deployment tasks

#### Physics/Verification (7 items)
- `physics/collision/__init__.spl` (3 items) - Sphere casting, BVH
- `verification/lean/expressions.spl` (1 item) - Module prefix matching
- `ml/torch/checkpoint.spl` (1 item) - Deserialization

#### Tests/Validation (8 items)
- `vulkan_phase1_validation.spl` (9 items) - FFI implementation tests
- `union_impl_spec.spl` (1 item) - Union type implementation

---

## P2 TODOs - Medium Priority (59 items)

### By Area

#### Godot Integration (22 items)
- `world.spl` (6 items) - RID parsing
- `tilemap.spl` (4 items) - Vector2 variants
- `navigation.spl` (4 items) - Vector2/3 parsing
- `camera.spl` (3 items) - Vector parsing
- `saveload.spl` (2 items) - PackedStringArray
- `networking.spl` (2 items) - Events, PackedInt32Array
- `ui_advanced.spl` (1 item) - PackedInt32Array

#### Tooling (16 items)
- `testing/runner.spl` (4 items) - Spec/process execution
- `testing/aggregation.spl` (2 items) - Output parsing
- `compiler/rust.spl` (2 items) - JSON parsing
- `core/dependency.spl` (2 items) - Tree-sitter parsing
- Various others (6 items)

#### Vulkan Renderer (6 items)
- `vulkan_renderer.spl` (6 items) - Attribute parsing, optimizations

#### MCP/Multi-lang (6 items)
- `multi_lang/` (4 items) - Ruby, Go, Erlang, C parsing
- `examples/template_provider.spl` (1 item) - Language parsing
- `simple_lang/coverage.spl` (1 item) - Coverage JSON

#### Other (9 items)
- `interpreter/main.spl` (2 items) - Load/parse, evaluate
- `dap/server.spl` (1 item) - Program path parsing
- `vscode/` (2 items) - JSON parsing, webview
- `cli/parsed_args.spl` (1 item) - Arg tracking
- `unreal/ubt.spl` (1 item) - JSON version file
- `mcp/advanced.spl` (1 item) - Chunk parsing
- `contracts_spec.spl` (1 item) - Contract blocks

---

## P3 TODOs - Low Priority (414 items)

### Distribution

| Category | Count | Notes |
|----------|-------|-------|
| Vulkan/UI | ~150 | Types, renderer, pipelines, fonts |
| Godot | ~60 | Physics3D, scene, particles, lighting |
| Tooling | ~80 | Deployment, packaging, testing |
| VSCode | ~25 | Providers, manifest, workspace |
| MCP | ~30 | Multi-lang, tooling, providers |
| Stdlib | ~40 | Collections, doctest, specs |
| Other | ~29 | Various |

### Notable P3 Categories

**Vulkan UI (150+ items):**
- Instance/device creation
- Swapchain management
- Render pass and framebuffers
- Pipeline and shaders
- Draw calls and presentation

**Tooling/Deployment (80+ items):**
- Container builds
- Package formats (deb, rpm, npm, pip)
- Optimization passes
- CI/CD automation

**Godot Integration (60+ items):**
- 3D physics vectors
- Scene management
- Particle systems
- Navigation meshes

---

## Untagged TODOs (146 items)

TODOs without priority tags that need triage:
- `simple/` directory: 142 items
- `src/` directory: 4 items

### Recommended Triage

Run the TODO lint to identify and prioritize these:
```bash
./target/debug/simple lint --check-todos simple/
```

---

## Comparison with Previous Report

| Metric | Previous (01-16) | Current (01-17) | Change |
|--------|------------------|-----------------|--------|
| Total | 119 | 772 | +653 |
| P1 | 15 | 153 | +138 |
| P2 | 2 | 59 | +57 |
| P3 | 34 | 414 | +380 |
| Untagged | 68 | 146 | +78 |

**Note:** Previous report only scanned `src/` directory. Current report includes full `simple/` directory (stdlib, apps, tests).

---

## Recommendations

### Immediate Actions

1. **Triage Untagged TODOs** (146 items)
   - Run TODO lint on simple/ directory
   - Prioritize by impact and effort

2. **Review Concurrency P1s** (49 items)
   - These are spec placeholders
   - Will be resolved when parser/type system supports features

3. **Vulkan P1s** (22 items)
   - Core rendering infrastructure
   - Should prioritize layout algorithms and event dispatch

### Short-term

4. **Parser/Compiler P1s** (11 items)
   - File watching for watch mode
   - Tree-sitter improvements

5. **Interpreter P1s** (14 items)
   - Core expression evaluation
   - FFI type marshalling

### Long-term

6. **P3 Cleanup** (414 items)
   - Many are implementation placeholders
   - Review for obsolete items

---

## Metrics

### TODO Density
- **Total TODOs:** 772
- **Codebase:** simple/ + src/
- **Status:** Active development phase

### Priority Distribution
```
P1: ████████████████████ 20%
P2: ████████ 8%
P3: ██████████████████████████████████████████████████████ 54%
Untagged: ███████████████████ 19%
```

### By Directory
- `simple/std_lib/src/`: ~400 TODOs
- `simple/std_lib/test/`: ~100 TODOs
- `simple/app/`: ~120 TODOs
- `src/`: ~9 TODOs (+ lint test examples)

---

*Report generated: 2026-01-17*
*Method: grep -r "TODO:" with priority pattern matching*
*Excludes: vscode-test vendor files, lint test examples*
