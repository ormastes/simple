# Difficulty Level 5 Features - Extremely Complex

**Source:** `doc/features/postponed_feature.md`
**Total Level-5 Features:** 7
**Average Estimated Effort:** 60-150+ hours per feature

This document lists only the **difficulty level 5** features from postponed_feature.md - the most complex and time-intensive features requiring deep expertise and substantial engineering effort.

---

## Summary

| ID | Feature | Category | Effort | Priority | Source |
|----|---------|----------|--------|----------|--------|
| #1302 | Hygienic macro expansion | Metaprogramming | 60h+ | High | macro.md |
| #1359 | Language Server Protocol (LSP) | Developer Tools | 40h | Medium | 30_pending_features.md |
| #1366 | Debug Adapter Protocol (DAP) | Developer Tools | 50h | Medium | 30_pending_features.md |
| #1374 | Immediate Mode GUI (egui-style) | UI Framework | 100h+ | Low | 30_pending_features.md |
| #1375 | Native widgets (platform-specific) | UI Framework | 150h+ | Low | 30_pending_features.md |
| #1376 | Web-based GUI (Electron-style) | UI Framework | 150h+ | Low | 30_pending_features.md |
| #1378 | Cross-platform rendering | UI Framework | 120h+ | Low | 30_pending_features.md |

**Total Estimated Effort:** 770+ hours

---

## Feature Details

### #1302: Hygienic Macro Expansion

**Category:** Metaprogramming
**Difficulty:** 5/5
**Estimated Effort:** 60+ hours
**Priority:** High
**Status:** ✅ Implemented (Parser ✅, Basic Expansion ✅, Hygiene ✅)
**Source:** `doc/spec/macro.md`

**Description:**
Implement hygienic macro expansion that prevents name capture and maintains lexical scoping. Macros must not accidentally shadow or capture variables from the calling context.

**Current Implementation Status:**

✅ **Parser Complete** (`src/parser/src/statements/mod.rs`, ~400 lines):
- Full AST: `MacroDef`, `MacroParam`, `MacroContractItem`, `MacroIntroSpec`, `MacroInjectSpec`
- Contract parsing: `returns`, `intro`, `inject`
- Targets: `enclosing.{module|class|struct|trait}`, `callsite.block.{head|tail|here}`
- Intro kinds: `fn`, `field`, `type`, `let`, `const`
- All grammar from `doc/spec/macro.md` implemented

✅ **Basic Non-Hygienic Expansion** (`src/compiler/src/interpreter_macro.rs`, ~300 lines):
- `const_eval:` block execution at expansion time
- `emit:` block template substitution and execution
- Built-in macros: `println!`, `assert!`, `assert_eq!`, `vec!`, `panic!`, `format!`, `dbg!`, `assert_unit!`
- User-defined macro expansion with parameter binding
- Works for simple cases without name capture issues

✅ **Hygienic Expansion (This Feature #1302)** now runs as an AST walker inside `src/compiler/src/interpreter_macro.rs`
  - `MacroHygieneContext` keeps a gensym counter plus a stack of scope maps so every fresh binding can be renamed before it leaks to the caller
  - `apply_macro_hygiene_block/node/expr/pattern` traverse emitted fragments (including `const_eval`, `emit`, and inline `MacroStmt::Stmt`) and rename identifiers while respecting nested scopes such as `match` arms, loops, `fn` definitions, and comprehensions
  - Hygiene runs before `exec_block`/`exec_node`, so macro-generated `let`/`fn`/`match` bindings never shadow the caller’s symbols or collide across nested macros

**Follow-up Work:**
- 🔄 #1303: `intro`/`inject`/`returns` contract items still need symbol-table integration so macro headers can advertise introduced names
- 📋 #1304: One-pass LL(1) macro compilation remains planned until #1303 is wired into the type checker and parser table

**Technical Challenges:**
- Complex scope tracking during expansion
- Interaction with type inference (type variables need hygiene too)
- Error reporting for macro-generated code (source spans)
- Performance optimization for nested macros
- Hygienic interaction with `intro`/`inject` contract items

**Dependencies:**
- ✅ #1300: `macro` keyword with contract syntax (Parser complete)
- ✅ #1301: `const_eval:` and `emit:` blocks (Basic expansion working)
- 🔄 #1303: `intro`/`inject`/`returns` contract items (Parsed, not integrated)
- ⏳ #1304: One-pass macro compilation (Awaiting #1303 symbol-table data)
- ✅ Parser complete
- 🔄 Type checker (partial, needs intro/inject integration)

**Related Features:**
- #1303: `intro`/`inject`/`returns` contract items - Symbol table integration
- #1304: One-pass macro compilation (LL(1)) - Requires hygienic expansion

**Implementation Approach:**

1. **MacroHygieneContext:** A small struct (`gensym_counter: usize`, `scopes: Vec<HashMap<String, String>>`) tracks the current scope stack and generates fresh names whenever a macro introduces `let`, `fn`, `match`, or pattern bindings.
2. **AST walker helpers:** `apply_macro_hygiene_block/node/expr/pattern` push/pop scopes for structured constructs (functions, loops, match arms, comprehensions, `with`/`context` blocks) and call `bind`/`resolve` so emitted bindings are renamed consistently while references resolve to the new names.
3. **Expansion pipeline integration:** `expand_user_macro` now runs hygiene on every `const_eval` block, on the template-substituted `emit` blocks, and on inline `MacroStmt::Stmt` nodes before calling `exec_block`/`exec_block_fn`, so macro output is already safe to type-check and execute.

**Example (Hygienic Expansion):**
```simple
# User code
let _tmp = 10

# Macro expands to:
macro let_temp(expr):
    emit:
        let _tmp = expr
        use(_tmp)

# After hygienic expansion the macro generates:
let _tmp_gensym_1 = expr
use(_tmp_gensym_1)  # Macro storage is renamed, so user's `_tmp` stays untouched
```

**Testing Plan:**
- Regression test that a macro-introduced binding cannot shadow a caller variable (assert renamed identifier).
- Nested macro suites that expand macros inside macros to ensure hygiene survives multiple scopes.
- Contract tests that exercise `const_eval`/`emit` alongside `intro`/`inject` hooks so hygiene runs before symbol declarations.
- Micro-benchmarks for gensym generation to keep expansion latency in check as macros grow in depth.

---

### #1359: Language Server Protocol (LSP) Implementation

**Category:** Developer Tools
**Difficulty:** 5/5
**Estimated Effort:** 40 hours
**Priority:** Medium
**Status:** 📋 Planned
**Source:** `doc/plans/30_pending_features.md` §1

**Description:**
Full Language Server Protocol implementation providing IDE features like auto-completion, go-to-definition, refactoring, and diagnostics.

**Sub-Features:**
- #1360: Syntax highlighting (Diff: 2)
- #1361: Auto-completion (Diff: 4)
- #1362: Go to definition (Diff: 3)
- #1363: Find references (Diff: 3)
- #1364: Hover documentation (Diff: 2)
- #1365: Error diagnostics (Diff: 3)

**Technical Challenges:**
- Incremental parsing and re-analysis
- Fast completion suggestions
- Cross-file reference tracking
- Real-time error reporting
- Memory-efficient AST caching

**Editor Support:**
- VS Code extension
- Neovim plugin
- Generic LSP clients (Emacs, Sublime, etc.)

**Dependencies:**
- Parser complete ✅
- Type checker complete (partial)
- AST traversal utilities
- Module resolution

**Implementation Approach:**
- **Recommended:** Self-hosted in Simple language (`simple/std_lib/src/lsp/`)
- Protocol: JSON-RPC over stdio/TCP
- Architecture: Single-threaded async or multi-threaded

**Related Features:**
- #1200-1299: Language Model Server & MCP (Tree-sitter integration)
- #1348-1358: MCP core protocol

---

### #1366: Debug Adapter Protocol (DAP) Implementation

**Category:** Developer Tools
**Difficulty:** 5/5
**Estimated Effort:** 50 hours
**Priority:** Medium
**Status:** 📋 Planned
**Source:** `doc/plans/30_pending_features.md` §2

**Description:**
Full Debug Adapter Protocol implementation for debugging Simple programs in IDEs.

**Sub-Features:**
- #1367: Breakpoints and stepping (step in/over/out) (Diff: 4)
- #1368: Variable inspection (Diff: 4)

**Features:**
- Breakpoints (line, conditional, function)
- Step through code (in/over/out)
- Variable inspection and modification
- Call stack visualization
- Expression evaluation
- Watch expressions

**Technical Challenges:**
- Interpreter instrumentation for breakpoints
- Stack frame introspection
- Heap object inspection
- Expression evaluation in paused context
- Performance (minimal overhead when not debugging)

**Integration:**
- VS Code debugger
- Neovim debugger (nvim-dap)
- Generic DAP clients

**Dependencies:**
- Interpreter complete ✅
- Runtime introspection APIs
- Source map generation
- Symbol table preservation

**Protocol:** JSON-RPC over stdio/TCP

**Implementation Approach:**
- Extend existing interpreter with debugging hooks
- Trap mechanism for breakpoints
- Stack frame snapshot API

---

### #1374: Immediate Mode GUI (egui-style)

**Category:** UI Framework - GUI
**Difficulty:** 5/5
**Estimated Effort:** 100+ hours
**Priority:** Low
**Status:** 📋 Planned
**Source:** `doc/plans/30_pending_features.md` §7

**Description:**
Immediate mode GUI framework inspired by Dear ImGui and egui. Simple API where UI is re-drawn each frame from application state.

**Features:**
- Immediate mode rendering (no retained state)
- Hot reload friendly (UI = function of state)
- Simple declarative API
- Built-in widgets (buttons, sliders, text input, etc.)
- Layout system
- Styling and theming

**Technical Challenges:**
- Cross-platform rendering backend
- Input handling (mouse, keyboard, touch)
- Text rendering and shaping
- Performance optimization (60fps)
- Widget state management (without explicit state)

**Backends:**
- OpenGL/Vulkan/Metal for rendering
- SDL/GLFW for windowing and input
- Platform-specific (Win32, X11, Cocoa)

**Example:**
```simple
use std.gui.*

app = Gui():
    fn render():
        window("My App"):
            label("Hello, World!")
            if button("Click Me"):
                println("Button clicked!")

            text_input("Name:", ref: name)

    run()
```

**Related Features:**
- #1375: Native widgets (alternative approach)
- #1376: Web-based GUI (alternative approach)
- #1377: Hot reload support (Diff: 4)
- #1378: Cross-platform rendering

**Recommendation:** Start with this approach (simplest API).

---

### #1375: Native Widgets (Platform-Specific GUI)

**Category:** UI Framework - GUI
**Difficulty:** 5/5
**Estimated Effort:** 150+ hours
**Priority:** Low
**Status:** 📋 Planned
**Source:** `doc/plans/30_pending_features.md` §7

**Description:**
Native GUI framework using platform-specific widgets (GTK, Qt, Cocoa, Win32) for native look and feel.

**Platforms:**
- Linux: GTK+ or Qt
- macOS: Cocoa (AppKit)
- Windows: Win32 or WPF
- Cross-platform: Qt

**Pros:**
- Native look and feel
- OS integration (menus, dialogs)
- Accessibility support

**Cons:**
- Complex platform-specific code
- Different APIs per platform
- Larger maintenance burden

**Technical Challenges:**
- Cross-platform API abstraction
- Platform-specific event loops
- Layout differences across platforms
- Widget capability differences
- Build system complexity (linking native libs)

**Dependencies:**
- FFI bindings for native libraries
- Cross-compilation support
- Platform detection

**Alternative:** Use Qt for unified cross-platform API.

**Related Features:**
- #1374: Immediate Mode GUI (recommended alternative)
- #1378: Cross-platform rendering

---

### #1376: Web-Based GUI (Electron-style)

**Category:** UI Framework - GUI
**Difficulty:** 5/5
**Estimated Effort:** 150+ hours
**Priority:** Low
**Status:** 📋 Planned
**Source:** `doc/plans/30_pending_features.md` §7

**Description:**
Web-based GUI framework using HTML/CSS/JavaScript for rendering (Electron/Tauri-style).

**Approaches:**
1. **Electron-style:** Bundle Chromium + Node.js
2. **Tauri-style:** Use system WebView (lighter)
3. **Custom:** Embed web rendering engine

**Pros:**
- Cross-platform (HTML/CSS works everywhere)
- Familiar web technologies
- Rich styling and layout
- Large ecosystem (npm packages)

**Cons:**
- Heavy runtime (Chromium ~100MB)
- Higher memory usage
- Slower startup
- Security concerns (web vulnerabilities)

**Technical Challenges:**
- Bridging Simple ↔ JavaScript
- IPC between processes
- Packaging and distribution
- Update mechanism
- Security isolation

**Dependencies:**
- Web rendering engine (Chromium or WebView)
- IPC mechanism
- FFI for JavaScript bridge
- HTTP server (local)

**Related Features:**
- #520-536: Web framework (backend)
- #1374: Immediate Mode GUI (lighter alternative)

---

### #1378: Cross-Platform Rendering

**Category:** UI Framework - GUI
**Difficulty:** 5/5
**Estimated Effort:** 120+ hours
**Priority:** Low
**Status:** 📋 Planned
**Source:** `doc/plans/30_pending_features.md` §7

**Description:**
Unified cross-platform rendering abstraction supporting multiple backends (OpenGL, Vulkan, Metal, DirectX, WebGPU).

**Backends:**
- OpenGL 3.3+ (cross-platform, legacy)
- Vulkan (modern, explicit)
- Metal (macOS/iOS)
- DirectX 11/12 (Windows)
- WebGPU (web, future)

**Features:**
- Unified rendering API
- Shader abstraction (GLSL → backend-specific)
- Texture and buffer management
- 2D and 3D rendering
- Text rendering (font rasterization)

**Technical Challenges:**
- API differences across backends
- Shader compilation and translation
- Performance optimization per backend
- Resource management
- Platform-specific quirks

**Dependencies:**
- Graphics API bindings (FFI)
- Shader compiler (SPIR-V?)
- Window management (#1369-1373 for TUI)

**Related Features:**
- #1374: Immediate Mode GUI (consumer)
- #1369-1373: TUI framework (simpler alternative)
- #300-329: GPU/SIMD (existing GPU support)

**Recommendation:** Use existing library (wgpu, gfx-hal) instead of building from scratch.

---

## Priority Ranking

### High Priority (Critical for Language Maturity):
1. **#1302: Hygienic Macro Expansion** - Completes macro system (#1300-1304)

### Medium Priority (Developer Experience):
2. **#1359: LSP Implementation** - Critical for IDE support and adoption
3. **#1366: DAP Implementation** - Important for debugging workflow

### Low Priority (Nice-to-Have):
4. **#1374: Immediate Mode GUI** - Showcase feature, not core language
5. **#1375: Native Widgets** - Alternative GUI approach
6. **#1376: Web-Based GUI** - Alternative GUI approach
7. **#1378: Cross-Platform Rendering** - Infrastructure for GUI

---

## Implementation Recommendations

### Immediate Focus:
- **#1302 (Macro Hygiene):** Complete macro system specification (#1300-1304) first, then implement expansion.

### Short-Term (Next 6 months):
- **#1359 (LSP):** High ROI for developer adoption. Implement in Simple language (self-hosted).

### Medium-Term (6-12 months):
- **#1366 (DAP):** After LSP is stable. Leverage interpreter introspection.

### Long-Term (Future):
- **GUI Frameworks (#1374-1378):** Only after language and stdlib are mature. Consider using external libraries (wgpu, egui) via FFI instead of building from scratch.

---

## Resource Requirements

### Expertise Needed:

**#1302 (Macro Hygiene):**
- Compiler engineering
- Macro systems (Scheme, Rust, C++)
- Type theory

**#1359 (LSP):**
- Language Server Protocol spec
- Incremental parsing
- IDE integration

**#1366 (DAP):**
- Debugger implementation
- Runtime introspection
- Protocol design

**#1374-1378 (GUI):**
- Graphics programming
- UI/UX design
- Platform-specific APIs

---

## Dependencies and Blockers

### Unblocked (Can Start Now):
- ✅ #1359: Parser complete, type checker partial

### Blocked:
- #1302: Requires #1300-1301 (macro syntax) first
- #1366: Requires runtime introspection APIs
- #1374-1378: Requires stdlib maturity, graphics bindings

---

## See Also

- `doc/features/postponed_feature.md` - All postponed features (104 total)
- `doc/features/feature.md` - Main feature tracking (588 features)
- `doc/plans/30_pending_features.md` - Pending features planning document
- `doc/spec/macro.md` - Macro specification
- `verification/memory_capabilities/` - Lean 4 capability verification (#1104)
- `verification/memory_model_drf/` - Lean 4 SC-DRF verification (#1105-1106)

**Note on Memory Model:** The happens-before partial order and SC-DRF guarantee are already complete (✅) and tracked as #1099, #1100, and #1105 in feature.md. These were previously verified in Lean 4 and implemented with runtime race detection APIs.
