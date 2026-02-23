# Pending Features - Future Development

**Status:** Planned / Low Priority  
**Timeline:** TBD based on priorities

## Developer Tooling

### 1. Language Server Protocol (LSP)

**Priority:** Medium  
**Estimated:** 40 hours

**Features:**
- Syntax highlighting
- Auto-completion
- Go to definition
- Find references
- Hover documentation
- Error diagnostics

**Editor Support:**
- VS Code extension
- Neovim plugin
- Generic LSP support (Emacs, Sublime, etc.)

**Dependencies:**
- Parser complete ✅
- Type checker complete
- AST traversal utilities

**See Also:** Industry LSP implementations (rust-analyzer, TypeScript LSP)

---

### 2. Debugger (DAP)

**Priority:** Medium  
**Estimated:** 50 hours

**Features:**
- Breakpoints
- Step through code
- Variable inspection
- Call stack visualization
- Conditional breakpoints

**Protocol:** Debug Adapter Protocol (DAP)

**Integration:**
- VS Code debugger
- Neovim debugger (nvim-dap)
- Generic DAP support

**Dependencies:**
- Interpreter complete
- Runtime introspection
- Source map generation

---

## AI/LLM Integration

### 3. Model Context Protocol (MCP) for LLMs

**Priority:** High  
**Estimated:** 20 hours

**Goal:** Optimize Simple for LLM code generation and assistance

**Features:**
- Context pack generator (implemented in #405)
- AST/IR export (implemented in #403)
- Structured diagnostics (implemented in #404)
- Contract blocks (in progress #400)
- Capability-based imports (#401)

**Already Planned:** See `doc/plans/llm_friendly.md`

**Status:** Core features being implemented

---

## Language Features

### 4. Convention Over Configuration

**Priority:** Medium  
**Estimated:** 15 hours

**Task:** Document and enforce language conventions

**Areas:**
- File naming: `snake_case.spl`
- Module structure: `lib/`, `src/`, `test/`
- Visibility defaults: Private by default
- Import organization: stdlib first, then external, then local
- Code style: Canonical formatter (gofmt-style)

**Deliverables:**
- Update language spec with conventions
- Linter rules for conventions
- Formatter enforcement
- Migration guide

**File:** `doc/spec/conventions.md` (to create)

---

## GUI/UI Support

### 5. Ruby on Rails-Style Web Framework

**Priority:** Low  
**Estimated:** 100+ hours

**Goal:** Full-stack web framework for Simple

**Features:**
- MVC architecture
- ORM (database abstraction)
- Routing DSL
- Template engine
- Asset pipeline
- WebSocket support
- Hot reload
- RESTful APIs

**Example:**
```simple
# routes.spl
routes:
    get "/", controller: Home, action: index
    resources users

# controllers/home.spl
class HomeController:
    fn index(request: Request) -> Response:
        users = User.all()
        render("index.html", users: users)

# models/user.spl
class User(Model):
    field name: str
    field email: str
    validates email, format: EMAIL_REGEX
```

**Dependencies:**
- HTTP server
- Database drivers
- Template engine
- ORM layer

---

### 6. Terminal UI (TUI) Framework

**Priority:** Medium  
**Estimated:** 30 hours

**Goal:** Build rich terminal applications

**Features:**
- Widget system (buttons, input, lists, tables)
- Layout engine (flex, grid)
- Event handling (keyboard, mouse)
- Styling (colors, borders, padding)
- Screen management

**Example:**
```simple
use std.tui.*

app = App():
    layout = VBox():
        title = Text("Welcome").style(bold, color: blue)
        input = Input(placeholder: "Enter name...")
        button = Button("Submit").on_click(handle_submit)
    
    render(layout)
```

**Inspiration:**
- Rust: ratatui
- Go: bubbletea
- Python: textual

---

### 7. GUI Framework

**Priority:** Low  
**Estimated:** 150+ hours

**Goal:** Native GUI applications

**Options:**

**A. Native Widgets**
- Platform-specific (GTK, Qt, Cocoa, Win32)
- Pros: Native look and feel
- Cons: Complex, platform-specific

**B. Immediate Mode GUI**
- Inspired by Dear ImGui, egui
- Pros: Simple API, hot reload friendly
- Cons: Limited customization

**C. Web-Based (Electron-style)**
- HTML/CSS/JS rendering
- Pros: Cross-platform, familiar
- Cons: Heavy runtime

**Recommended:** Start with Immediate Mode (egui-style)

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

---

## Infrastructure

### 8. Test Infrastructure Enhancements

**Status:** Partially complete (BDD, Doctest)

**Remaining:**
- Property-based testing (#406)
- Snapshot/golden tests (#407)
- Mutation testing
- Fuzz testing

**See:** `doc/plans/llm_friendly.md` for details

---

### 9. Build System Enhancements

**Future Features:**
- Incremental compilation
- Distributed builds
- Build caching (ccache-style)
- Remote execution (Bazel-style)

---

### 10. Package Registry

**Priority:** Medium  
**Estimated:** 60 hours

**Goal:** Central package repository (crates.io-style)

**Features:**
- Package publishing
- Version management
- Dependency resolution
- Security scanning
- Documentation hosting
- Download statistics

**Infrastructure:**
- Web frontend
- API server
- Storage backend
- CDN for packages

---

## Priority Matrix

| Feature | Priority | Effort | Value | Dependencies |
|---------|----------|--------|-------|--------------|
| MCP/LLM | High | 20h | High | In progress |
| LSP | Medium | 40h | High | Parser ✅ |
| Conventions | Medium | 15h | High | Spec update |
| TUI Framework | Medium | 30h | Medium | stdlib I/O |
| DAP Debugger | Medium | 50h | Medium | Interpreter |
| Package Registry | Medium | 60h | High | Package manager ✅ |
| Web Framework | Low | 100h+ | Medium | Many deps |
| GUI Framework | Low | 150h+ | Low | Many deps |

---

## Recommendation

**Immediate Focus:**
1. Complete LLM-friendly features (#400-410)
2. Complete BDD/Doctest frameworks
3. LSP implementation (high value, moderate effort)
4. Convention documentation

**Medium-term:**
5. TUI framework (practical, showcases language)
6. Package registry (enables ecosystem growth)
7. DAP debugger (developer experience)

**Long-term:**
8. Web framework (when stdlib mature)
9. GUI framework (nice-to-have)

---

## See Also

- `doc/plans/llm_friendly.md` - LLM features (in progress)
- `doc/plans/28_testing/testing_bdd_framework.md` - BDD framework
- `doc/plans/29_doctest.md` - Doctest framework
- `doc/features/feature.md` - Complete feature list
