# Electron & VSCode Extension WASM Support - Implementation Plan

**Date:** 2025-12-26
**Status:** 📋 **PLANNED**
**Features:** 37 total (17 Electron + 20 VSCode)
**Estimated Timeline:** 14 weeks (Electron: 6 weeks, VSCode: 8 weeks)

## Executive Summary

This plan implements **WASM-based Electron desktop apps** and **VSCode extensions** using Simple language. Both focus on **UI-less applications** (background workers, system services, language tools) rather than GUI applications.

**Key Differentiators:**
- ✅ **Headless/Background**: No UI framework dependencies
- ✅ **High Performance**: WASM for CPU-intensive tasks
- ✅ **Type Safety**: Compile-time validation
- ✅ **Cross-Platform**: Single codebase, multiple targets
- ✅ **Native Integration**: System APIs without JavaScript overhead

---

## Part 1: Electron Desktop Apps (#1404-#1420)

**Timeline:** 6 weeks
**LOC:** ~2,200 lines (800 Rust, 1400 Simple)
**Features:** 17

### Use Cases

1. **System Tray Applications**
   - Battery monitors
   - Network status indicators
   - Clipboard managers
   - Screenshot tools

2. **Background Workers**
   - File synchronization services
   - Log processors
   - Data transformation pipelines
   - Scheduled task runners

3. **System Integrations**
   - Global hotkey handlers
   - File watchers
   - Power management
   - Native notifications

### Architecture

```
┌─────────────────────────────────────────┐
│         Electron Application            │
├─────────────────────────────────────────┤
│  Main Process (Node.js)                 │
│  ├─ WASM Loader (N-API)                 │
│  ├─ IPC Bridge                          │
│  └─ Native Module Interface             │
├─────────────────────────────────────────┤
│  Simple WASM Module                     │
│  ├─ System Tray Logic                   │
│  ├─ File Watcher Handlers               │
│  ├─ Power Monitor Callbacks             │
│  └─ Worker Pool Management              │
├─────────────────────────────────────────┤
│  Electron APIs (via FFI)                │
│  ├─ app (lifecycle)                     │
│  ├─ Tray (system tray)                  │
│  ├─ powerMonitor (battery events)       │
│  ├─ globalShortcut (hotkeys)            │
│  ├─ clipboard (copy/paste)              │
│  └─ Notification (alerts)               │
└─────────────────────────────────────────┘
```

### Implementation Phases

#### Phase 1: Core Infrastructure (2 weeks, ~600 LOC)

**Week 1: WASM Loaders**
- **#1404: Main process WASM loader** (~150 LOC)
  - N-API bindings for WASM instantiation
  - Memory management (linear memory allocation)
  - Export/import resolution
  - Error handling

- **#1405: Renderer process WASM loader** (~100 LOC)
  - WebAssembly.instantiate wrapper
  - Shared memory support
  - Performance monitoring

**Week 2: FFI Bridge**
- **#1406: Node.js FFI bridge** (~200 LOC)
  - Value marshalling (Simple ↔ JavaScript)
  - Function call bridge
  - Async/Promise integration
  - Callback handling

- **#1407: IPC message handlers** (~150 LOC)
  - WASM → Main process IPC
  - Main → Renderer IPC
  - Message serialization (JSON/Binary)

**Deliverables:**
- WASM loads in Electron main/renderer
- FFI calls work bidirectionally
- IPC communication functional

#### Phase 2: System Integration (2 weeks, ~800 LOC)

**Week 3: Native APIs**
- **#1408: N-API native module integration** (~200 LOC)
  - Native addon loader
  - Symbol resolution
  - Error propagation

- **#1409: System tray support** (~150 LOC)
  ```simple
  import electron.tray

  fn create_tray():
      tray = Tray.new("App Name")
      tray.setIcon("icon.png")
      tray.setContextMenu([
          MenuItem.new("Open", on_open),
          MenuItem.new("Quit", on_quit)
      ])
  ```

- **#1410: Background worker pool** (~200 LOC)
  - Worker thread spawning
  - Task queue management
  - Result aggregation

**Week 4: File & Power APIs**
- **#1411: File system watcher** (~150 LOC)
  ```simple
  import electron.fs

  fn watch_directory(path: String):
      watcher = fs.watch(path, fn(event, filename):
          if event == "change":
              process_file(filename)
      )
  ```

- **#1415: Auto-updater integration** (~100 LOC)
  - Version checking
  - Update downloading
  - Installation triggering

**Deliverables:**
- System tray apps working
- File watchers functional
- Background workers processing tasks

#### Phase 3: CLI & Packaging (1 week, ~400 LOC)

**Week 5: Build Tools**
- **#1412: `simple electron build` CLI** (~150 LOC)
  ```bash
  simple electron build monitor.spl -o dist/
  # Generates:
  # - dist/main.js (Electron entry point)
  # - dist/monitor.wasm
  # - dist/package.json
  # - dist/icon.png (if provided)
  ```

- **#1413: `simple electron package` CLI** (~150 LOC)
  ```bash
  simple electron package dist/ \
      --platform win,mac,linux \
      --arch x64,arm64 \
      --name "System Monitor" \
      --version 1.0.0
  # Uses electron-builder internally
  ```

- **#1414: Manifest generation** (~100 LOC)
  - package.json generator
  - electron-builder config
  - Icon/resource bundling

**Deliverables:**
- CLI builds Electron apps
- Cross-platform packaging works
- Distributable binaries generated

#### Phase 4: Additional Features (1 week, ~400 LOC)

**Week 6: Utilities**
- **#1416: Native notifications** (~50 LOC)
- **#1417: Global shortcuts** (~100 LOC)
- **#1418: Power monitor** (~100 LOC)
- **#1419: Clipboard access** (~50 LOC)
- **#1420: Testing framework** (~100 LOC)
  - Spectron-based testing
  - Headless mode tests
  - Screenshot comparison

**Deliverables:**
- All utility APIs working
- Testing framework operational
- Example apps complete

### Example: System Monitor App

**File:** `monitor.spl`

```simple
import electron.app
import electron.tray
import electron.power
import electron.notification
import os.cpu
import os.memory

let tray: Tray? = none
let updateInterval: i32 = 5000  # 5 seconds

fn main():
    app.on("ready", on_ready)
    app.on("window-all-closed", fn(): pass)  # Keep running

fn on_ready():
    tray = Tray.new("System Monitor")
    tray!.setIcon("icon.png")
    tray!.setToolTip("System Monitor")

    # Build context menu
    menu = [
        MenuItem.new("CPU: 0%", none).setEnabled(false),
        MenuItem.new("Memory: 0%", none).setEnabled(false),
        MenuSeparator.new(),
        MenuItem.new("Quit", on_quit)
    ]
    tray!.setContextMenu(menu)

    # Monitor battery
    power.onBatteryLow(on_battery_low)

    # Start monitoring
    update_stats()

fn update_stats():
    cpu_usage = cpu.getUsage()
    mem_usage = memory.getUsage()

    # Update menu
    menu = tray!.getContextMenu()
    menu[0].label = "CPU: {cpu_usage}%"
    menu[1].label = "Memory: {mem_usage}%"
    tray!.setContextMenu(menu)

    # Update icon color based on CPU
    if cpu_usage > 80:
        tray!.setIcon("icon_red.png")
    elif cpu_usage > 50:
        tray!.setIcon("icon_yellow.png")
    else:
        tray!.setIcon("icon_green.png")

    # Schedule next update
    setTimeout(update_stats, updateInterval)

fn on_battery_low():
    notification = Notification.new({
        title: "Battery Low",
        body: "Please plug in your device",
        urgency: "critical"
    })
    notification.show()

fn on_quit():
    app.quit()
```

**Build & Run:**

```bash
# Build
simple electron build monitor.spl -o dist/

# Test
cd dist && npm start

# Package for all platforms
simple electron package dist/ \
    --platform all \
    --arch x64 \
    --name "System Monitor" \
    --version 1.0.0

# Output:
# - system-monitor-1.0.0.exe (Windows)
# - system-monitor-1.0.0.dmg (macOS)
# - system-monitor-1.0.0.AppImage (Linux)
```

---

## Part 2: VSCode Extension Support (#1421-#1440)

**Timeline:** 8 weeks
**LOC:** ~3,500 lines (1,200 Rust, 2,300 Simple)
**Features:** 20

### Use Cases

1. **Language Servers**
   - Syntax highlighting
   - Code completion
   - Go-to-definition
   - Diagnostics

2. **Code Actions**
   - Auto-fix suggestions
   - Refactoring tools
   - Import organizers
   - Code formatters

3. **Task Providers**
   - Build system integration
   - Test runners
   - Deployment automation
   - Custom workflows

4. **Document Providers**
   - Virtual file systems
   - Preview generators
   - Data visualizers
   - Log viewers

### Architecture

```
┌─────────────────────────────────────────┐
│      VSCode Extension Host              │
├─────────────────────────────────────────┤
│  Extension Main (JavaScript)            │
│  ├─ WASM Loader                         │
│  ├─ Extension API Bridge                │
│  └─ Protocol Handlers                   │
├─────────────────────────────────────────┤
│  Simple WASM Module                     │
│  ├─ Language Server Protocol            │
│  ├─ Completion Provider Logic           │
│  ├─ Diagnostics Engine                  │
│  └─ Code Action Generator               │
├─────────────────────────────────────────┤
│  VSCode Extension API (via FFI)         │
│  ├─ languages.* (providers)             │
│  ├─ commands.* (actions)                │
│  ├─ window.* (UI elements)              │
│  ├─ workspace.* (files)                 │
│  └─ debug.* (DAP)                       │
└─────────────────────────────────────────┘
```

### Implementation Phases

#### Phase 1: Core Infrastructure (2 weeks, ~800 LOC)

**Week 1: Extension Foundation**
- **#1421: Extension manifest generator** (~200 LOC)
  ```simple
  # Generates package.json
  manifest = ExtensionManifest.new({
      name: "simple-lang-support",
      displayName: "Simple Language Support",
      version: "1.0.0",
      engines: {vscode: "^1.80.0"},
      activationEvents: ["onLanguage:simple"],
      contributes: {
          languages: [{
              id: "simple",
              extensions: [".spl"]
          }]
      }
  })
  ```

- **#1423: Command registration API** (~150 LOC)
  ```simple
  import vscode

  fn activate(context: ExtensionContext):
      cmd = vscode.commands.registerCommand(
          "simple.formatDocument",
          format_document
      )
      context.subscriptions.push(cmd)
  ```

**Week 2: Language Server Protocol**
- **#1422: WASM LSP implementation** (~450 LOC)
  - Protocol message handling
  - Request/response routing
  - Capability negotiation
  - Async operation support

**Deliverables:**
- Extension activates in VSCode
- Commands registered and working
- LSP communication functional

#### Phase 2: Language Features (3 weeks, ~1,200 LOC)

**Week 3: Basic Providers**
- **#1427: Completion provider** (~300 LOC)
  ```simple
  import vscode

  fn provideCompletionItems(document: TextDocument, position: Position):
      line = document.lineAt(position.line)
      text = line.text.substring(0, position.character)

      # WASM-based completion logic
      if text.endsWith("fn "):
          return [
              CompletionItem.new("main", CompletionItemKind.Function),
              CompletionItem.new("async fn", CompletionItemKind.Snippet)
          ]

      # Keyword completions
      return get_keyword_completions()
  ```

- **#1428: Hover provider** (~150 LOC)
  - Symbol documentation lookup
  - Type information display
  - Markdown formatting

- **#1429: Go-to-definition** (~200 LOC)
  - Symbol resolution
  - Cross-file navigation
  - Workspace indexing

**Week 4: Diagnostics & Actions**
- **#1426: Diagnostics publisher** (~250 LOC)
  ```simple
  fn update_diagnostics(document: TextDocument):
      diagnostics = []

      # Parse and analyze
      errors = parse_document(document.getText())

      for error in errors:
          diagnostic = Diagnostic.new(
              range: error.range,
              message: error.message,
              severity: DiagnosticSeverity.Error,
              source: "simple"
          )
          diagnostics.append(diagnostic)

      # Publish
      diagnosticCollection.set(document.uri, diagnostics)
  ```

- **#1425: Code action provider** (~300 LOC)
  - Quick fixes
  - Refactoring suggestions
  - Import additions

**Week 5: Advanced Features**
- **#1424: Document provider** (~150 LOC)
  - Virtual file system
  - Preview generation

- **#1430: Tree view provider** (~150 LOC)
  - Custom sidebar views
  - File explorer integration

**Deliverables:**
- Full language support working
- Diagnostics showing in editor
- Code actions available

#### Phase 3: Integration Features (2 weeks, ~800 LOC)

**Week 6: Workspace Integration**
- **#1431: Status bar integration** (~100 LOC)
- **#1432: Configuration API** (~150 LOC)
  ```simple
  import vscode

  fn get_config():
      config = vscode.workspace.getConfiguration("simple")
      format_on_save = config.get("formatOnSave", true)
      max_line_length = config.get("maxLineLength", 100)
      return {formatOnSave, maxLineLength}
  ```

- **#1433: Task provider** (~200 LOC)
  ```simple
  fn provideTasks():
      return [
          Task.new({
              name: "build",
              execution: ShellExecution.new("simple build app.spl")
          }),
          Task.new({
              name: "test",
              execution: ShellExecution.new("simple test")
          })
      ]
  ```

**Week 7: Advanced Features**
- **#1434: Debug adapter protocol** (~250 LOC)
  - Breakpoint management
  - Variable inspection
  - Stack trace viewing

- **#1435: Terminal integration** (~100 LOC)
  - REPL support
  - Output formatting

**Deliverables:**
- Workspace features integrated
- Tasks and debugging working
- Terminal integration complete

#### Phase 4: Packaging & Publishing (1 week, ~700 LOC)

**Week 8: Build & Distribution**
- **#1436: `simple vscode build` CLI** (~200 LOC)
  ```bash
  simple vscode build extension.spl -o dist/
  # Generates:
  # - dist/extension.js (entry point)
  # - dist/extension.wasm
  # - dist/package.json (manifest)
  ```

- **#1437: `simple vscode package` CLI** (~250 LOC)
  ```bash
  simple vscode package dist/ \
      --name simple-lang-support \
      --version 1.0.0
  # Output: simple-lang-support-1.0.0.vsix
  ```

- **#1438: Testing framework** (~150 LOC)
  - Extension host testing
  - Integration tests
  - UI tests

- **#1439: Webview WASM loader** (~100 LOC)
  - Custom webview panels
  - WASM in webview context

**Deliverables:**
- CLI builds .vsix packages
- Testing framework operational
- Extension publishable

### Example: Simple Language Extension

**File:** `simple-lang-extension.spl`

```simple
import vscode

let diagnosticCollection: DiagnosticCollection? = none

fn activate(context: ExtensionContext):
    console.log("Simple Language Extension activated")

    # Create diagnostic collection
    diagnosticCollection = vscode.languages.createDiagnosticCollection("simple")
    context.subscriptions.push(diagnosticCollection!)

    # Register language features
    register_completion_provider(context)
    register_hover_provider(context)
    register_code_actions(context)
    register_diagnostics(context)

    # Register commands
    register_commands(context)

fn register_completion_provider(context: ExtensionContext):
    provider = vscode.languages.registerCompletionItemProvider(
        "simple",
        {provideCompletionItems: provide_completions},
        ".", ":"  # Trigger characters
    )
    context.subscriptions.push(provider)

fn provide_completions(document: TextDocument, position: Position):
    line = document.lineAt(position.line).text

    # Keyword completions
    keywords = ["fn", "let", "if", "else", "for", "while", "return", "import"]
    items = []

    for keyword in keywords:
        item = CompletionItem.new(keyword, CompletionItemKind.Keyword)
        item.detail = "Simple keyword"
        items.append(item)

    # Type completions
    types = ["i32", "i64", "f32", "f64", "String", "bool"]
    for type_name in types:
        item = CompletionItem.new(type_name, CompletionItemKind.Class)
        item.detail = "Simple type"
        items.append(item)

    return items

fn register_hover_provider(context: ExtensionContext):
    provider = vscode.languages.registerHoverProvider(
        "simple",
        {provideHover: provide_hover}
    )
    context.subscriptions.push(provider)

fn provide_hover(document: TextDocument, position: Position):
    range = document.getWordRangeAtPosition(position)
    if range == none:
        return none

    word = document.getText(range!)

    # Look up documentation
    docs = get_documentation(word)
    if docs != none:
        return Hover.new(MarkdownString.new(docs!))

    return none

fn register_code_actions(context: ExtensionContext):
    provider = vscode.languages.registerCodeActionsProvider(
        "simple",
        {provideCodeActions: provide_code_actions}
    )
    context.subscriptions.push(provider)

fn provide_code_actions(document: TextDocument, range: Range, context: CodeActionContext):
    actions = []

    for diagnostic in context.diagnostics:
        if diagnostic.code == "unused-variable":
            # Quick fix: remove unused variable
            action = CodeAction.new(
                "Remove unused variable",
                CodeActionKind.QuickFix
            )
            action.diagnostics = [diagnostic]

            edit = WorkspaceEdit.new()
            edit.delete(document.uri, diagnostic.range)
            action.edit = edit

            actions.append(action)

    return actions

fn register_diagnostics(context: ExtensionContext):
    # Update diagnostics on document change
    vscode.workspace.onDidChangeTextDocument(fn(event):
        update_diagnostics(event.document)
    )

    # Update diagnostics on document open
    vscode.workspace.onDidOpenTextDocument(fn(document):
        update_diagnostics(document)
    )

fn update_diagnostics(document: TextDocument):
    if document.languageId != "simple":
        return

    diagnostics = []
    text = document.getText()

    # Simple syntax check (find undefined variables)
    lines = text.split("\n")
    for i in 0..lines.len():
        line = lines[i]

        # Check for common issues
        if line.contains("TODO"):
            diagnostic = Diagnostic.new(
                Range.new(Position.new(i, 0), Position.new(i, line.len())),
                "TODO comment found",
                DiagnosticSeverity.Information
            )
            diagnostic.source = "simple"
            diagnostics.append(diagnostic)

    diagnosticCollection!.set(document.uri, diagnostics)

fn register_commands(context: ExtensionContext):
    # Format document command
    cmd1 = vscode.commands.registerCommand(
        "simple.formatDocument",
        format_document
    )

    # Run tests command
    cmd2 = vscode.commands.registerCommand(
        "simple.runTests",
        run_tests
    )

    context.subscriptions.push(cmd1)
    context.subscriptions.push(cmd2)

fn format_document():
    editor = vscode.window.activeTextEditor
    if editor == none:
        return

    document = editor!.document

    # Format the document
    formatted_text = format_simple_code(document.getText())

    # Apply edit
    edit = WorkspaceEdit.new()
    full_range = Range.new(
        Position.new(0, 0),
        document.positionAt(document.getText().len())
    )
    edit.replace(document.uri, full_range, formatted_text)
    vscode.workspace.applyEdit(edit)

fn run_tests():
    terminal = vscode.window.createTerminal("Simple Tests")
    terminal.show()
    terminal.sendText("simple test")

fn deactivate():
    # Cleanup
    if diagnosticCollection != none:
        diagnosticCollection!.dispose()

# Helper functions
fn get_documentation(symbol: String): String? =
    # Look up in documentation database
    # (WASM-based fast lookup)
    docs_db.lookup(symbol)

fn format_simple_code(code: String): String =
    # WASM-based fast formatting
    formatter.format(code)
```

**Build & Publish:**

```bash
# Build extension
simple vscode build simple-lang-extension.spl -o dist/

# Test locally
code --extensionDevelopmentPath=./dist

# Package
simple vscode package dist/ \
    --name simple-lang-support \
    --version 1.0.0 \
    --publisher your-name

# Output: simple-lang-support-1.0.0.vsix

# Publish to marketplace
simple vscode publish simple-lang-support-1.0.0.vsix \
    --token <your-vsce-token>
```

---

## Dependencies

### Electron Dependencies

| Dependency | Purpose | Version |
|------------|---------|---------|
| `electron` | Desktop app framework | ^27.0.0 |
| `electron-builder` | Packaging | ^24.0.0 |
| `@napi-rs/wasm-runtime` | WASM loader | ^0.2.0 |
| `spectron` (optional) | Testing | ^19.0.0 |

### VSCode Dependencies

| Dependency | Purpose | Version |
|------------|---------|---------|
| `vscode` | Extension API | ^1.80.0 |
| `@vscode/vsce` | Packaging tool | ^2.20.0 |
| `@vscode/test-electron` | Testing | ^2.3.0 |

### Simple Compiler Dependencies

| Component | Purpose | LOC |
|-----------|---------|-----|
| WASM Target | Compile to wasm32 | Existing |
| FFI Bridge | JS ↔ WASM calls | ~300 |
| CLI Tools | Build/package commands | ~600 |
| Stdlib Modules | electron.*, vscode.* | ~1,800 |

---

## Testing Strategy

### Electron Testing

**Unit Tests:**
```simple
import spec
import electron.tray

describe("Tray API", fn():
    it("creates tray with icon", fn():
        tray = Tray.new("Test App")
        tray.setIcon("test-icon.png")
        expect(tray.getTitle()).to_equal("Test App")
    )

    it("sets context menu", fn():
        tray = Tray.new("Test")
        menu = [MenuItem.new("Quit", fn(): pass)]
        tray.setContextMenu(menu)
        expect(tray.getContextMenu().len()).to_equal(1)
    )
)
```

**Integration Tests:**
```bash
# Spectron-based UI testing
simple electron test monitor.spl --headless
```

### VSCode Testing

**Unit Tests:**
```simple
import spec
import vscode.test

describe("Completion Provider", fn():
    it("provides keyword completions", fn():
        document = vscode.test.createDocument("test.spl", "fn ")
        position = Position.new(0, 3)

        completions = provide_completions(document, position)
        expect(completions.len()).to_be_greater_than(0)
    )
)
```

**Integration Tests:**
```bash
# VSCode extension tester
simple vscode test extension.spl
```

---

## Performance Benchmarks

### Electron Performance

| Metric | Target | Notes |
|--------|--------|-------|
| App startup time | <2s | Cold start |
| WASM load time | <100ms | ~500KB module |
| Memory footprint | <100MB | Idle state |
| CPU usage (idle) | <1% | Background monitoring |

### VSCode Extension Performance

| Metric | Target | Notes |
|--------|--------|-------|
| Extension activation | <500ms | On language open |
| Completion latency | <50ms | Typing response |
| Diagnostics update | <200ms | Per file change |
| Memory per file | <5MB | AST + index |

---

## Advantages Over Traditional Approaches

### vs. Pure JavaScript Electron

| Aspect | Simple WASM | JavaScript |
|--------|-------------|------------|
| Type Safety | ✅ Compile-time | ⚠️ Runtime only |
| Performance | ✅ 2-5x faster | Baseline |
| Memory Safety | ✅ Guaranteed | ⚠️ Manual |
| Binary Size | ✅ 200-500KB | 1-5MB |
| Threading | ✅ Native | ⚠️ Worker overhead |

### vs. TypeScript VSCode Extensions

| Aspect | Simple WASM | TypeScript |
|--------|-------------|------------|
| Compilation | ✅ Compile-time checks | ⚠️ Transpile only |
| Performance | ✅ 3-10x faster (parsing) | Baseline |
| Memory | ✅ 50% less | Higher GC overhead |
| Deploy Size | ✅ Smaller (~500KB) | Larger (1-3MB) |

---

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Electron API changes | Medium | Low | Version pinning, compatibility layer |
| VSCode API instability | Medium | Low | Target stable API version |
| WASM size bloat | Low | Medium | Tree shaking, optimization |
| FFI overhead | Medium | Medium | Batch calls, caching |
| Debugging difficulty | High | Medium | Source maps, logging |

---

## Timeline Summary

| Phase | Duration | Features | LOC |
|-------|----------|----------|-----|
| **Electron Phase 1** | 2 weeks | Core infra (#1404-1407) | 600 |
| **Electron Phase 2** | 2 weeks | System APIs (#1408-1411, 1415) | 800 |
| **Electron Phase 3** | 1 week | CLI & packaging (#1412-1414) | 400 |
| **Electron Phase 4** | 1 week | Utilities (#1416-1420) | 400 |
| **VSCode Phase 1** | 2 weeks | Foundation (#1421-1423) | 800 |
| **VSCode Phase 2** | 3 weeks | Language features (#1424-1430) | 1,200 |
| **VSCode Phase 3** | 2 weeks | Integration (#1431-1435) | 800 |
| **VSCode Phase 4** | 1 week | Packaging (#1436-1440) | 700 |
| **Total** | **14 weeks** | **37 features** | **5,700** |

---

## Success Criteria

### Electron

- ✅ System tray app runs on Windows/macOS/Linux
- ✅ File watcher processes 1000+ files/sec
- ✅ Background worker handles 100 tasks/sec
- ✅ Packaging produces <50MB binaries
- ✅ Auto-updater works reliably

### VSCode

- ✅ Extension activates in <500ms
- ✅ Completion suggestions in <50ms
- ✅ Diagnostics update in <200ms
- ✅ Go-to-definition in <100ms
- ✅ VSIX package <2MB

---

## Future Enhancements

### Electron (Post-MVP)

1. **Window management** - Create/manage windows from WASM
2. **Menu bar apps** - macOS menu bar integration
3. **Dock integration** - macOS dock menu/badge
4. **Windows taskbar** - Windows notification area
5. **Linux system menu** - GNOME/KDE integration

### VSCode (Post-MVP)

1. **Semantic tokens** - Enhanced syntax highlighting
2. **Inline values** - Debugger inline display
3. **Call hierarchy** - Function call tree
4. **Type hierarchy** - Type inheritance tree
5. **Notebook support** - Jupyter notebook kernels

---

## Conclusion

This plan provides **comprehensive Electron and VSCode extension support** for Simple language, focusing on **headless/background applications** rather than UI frameworks. The 14-week timeline delivers **37 features** across both platforms, enabling:

- **Desktop system utilities** (tray apps, file watchers, workers)
- **Editor plugins** (language servers, code actions, tasks)
- **High performance** (WASM for CPU-intensive tasks)
- **Type safety** (compile-time validation)
- **Cross-platform** (single codebase)

**Ready to proceed with implementation upon approval.**
