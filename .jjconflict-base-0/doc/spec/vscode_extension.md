# VSCode Extension API Specification

**Version:** 1.0
**Date:** 2025-12-26
**Scope:** VSCode extension development with Simple language

## Overview

This specification defines the VSCode Extension API for building editor plugins with Simple. The API provides access to VSCode's extension features including language servers, code actions, custom commands, diagnostics, tasks, terminals, and custom views.

**Design Principles:**
1. **WASM-First**: Extensions compile to WebAssembly for cross-platform compatibility
2. **Type-Safe**: All APIs use Simple's static type system
3. **Event-Driven**: Reactive programming model with callbacks and providers
4. **Consistent**: Follows VSCode's existing extension API patterns
5. **Simple**: Maximum defaults, minimal boilerplate

---

## Part 1: Core Extension Structure

### Extension Lifecycle

Every VSCode extension has two main lifecycle functions:

```simple
import vscode

# Called when extension is activated
pub fn activate(context: ExtensionContext):
    # Register features, providers, commands
    let disposable = vscode.commands.register_command("myext.hello", fn(args):
        vscode.window.show_information_message("Hello!")
    )

    context.subscriptions.push(disposable)

# Called when extension is deactivated
pub fn deactivate():
    # Cleanup resources
    pass
```

### Extension Context

The `ExtensionContext` object provides access to extension state and subscription management:

```simple
pub class ExtensionContext:
    pub subscriptions: List[i64]      # Disposables
    pub workspace_state: Dict[String, String]  # Workspace-specific state
    pub global_state: Dict[String, String]     # Global state
```

**Usage:**
- `context.subscriptions.push(id)` - Add disposable for automatic cleanup
- `context.workspace_state` - Store workspace-specific data
- `context.global_state` - Store global extension data

---

## Part 2: Commands API

### Registering Commands

Commands are executable actions that can be triggered from the command palette, keyboard shortcuts, or menus.

```simple
import vscode.commands

pub fn activate(context: ExtensionContext):
    # Register command handler
    let sub = commands.register_command("simple.formatDocument", fn(args):
        # Get active editor
        match window.get_active_text_editor():
            some(editor):
                let formatted = format_code(editor.document.get_text())
                # Apply edit
                window.show_information_message("Formatted!")
            none:
                window.show_error_message("No active editor")
    )

    context.subscriptions.push(sub)
```

### Executing Commands

```simple
# Execute built-in command
commands.execute_command("editor.action.formatDocument", [])

# Execute custom command
commands.execute_command("simple.analyze", ["file.spl"])
```

---

## Part 3: Language Features

### Completion Provider

Provide autocomplete suggestions:

```simple
import vscode.languages

pub fn activate(context: ExtensionContext):
    let sub = languages.register_completion_provider("simple", fn(doc, pos):
        return [
            CompletionItem.new("fn", CompletionItemKind_Keyword),
            CompletionItem.new("let", CompletionItemKind_Keyword),
            CompletionItem.new("class", CompletionItemKind_Keyword),
            CompletionItem.new("import", CompletionItemKind_Keyword)
        ]
    )

    context.subscriptions.push(sub)
```

### Hover Provider

Show information on hover:

```simple
pub fn activate(context: ExtensionContext):
    let sub = languages.register_hover_provider("simple", fn(doc, pos):
        let word = doc.get_word_range_at_position(pos)
        match word:
            some(range):
                # Look up symbol documentation
                let hover_text = "**Function:** `calculate(x: i32)`\n\nCalculates the result."
                return some(Hover.new(hover_text))
            none:
                return none
    )

    context.subscriptions.push(sub)
```

### Definition Provider

Provide go-to-definition:

```simple
pub fn activate(context: ExtensionContext):
    let sub = languages.register_definition_provider("simple", fn(doc, pos):
        # Find symbol definition
        let symbol = find_symbol_at_position(doc, pos)
        match symbol:
            some(sym):
                return some(Range.new(
                    Position.new(sym.line, sym.column),
                    Position.new(sym.line, sym.column + sym.length)
                ))
            none:
                return none
    )

    context.subscriptions.push(sub)
```

### Diagnostics

Publish errors and warnings:

```simple
pub fn activate(context: ExtensionContext):
    # Create diagnostic collection
    let diagnostics = DiagnosticCollection.new("simple")

    # Publish diagnostics for a file
    let diag1 = Diagnostic.new(
        Range.new(Position.new(5, 0), Position.new(5, 10)),
        "Undefined variable 'x'",
        DiagnosticSeverity_Error
    )
    diag1.source = "simple-compiler"
    diag1.code = "E001"

    diagnostics.set("file:///path/to/file.spl", [diag1])

    # Clear diagnostics
    diagnostics.clear()
```

---

## Part 4: Code Actions

### Quick Fixes and Refactorings

```simple
import vscode.actions

pub fn activate(context: ExtensionContext):
    let sub = actions.register_code_actions_provider("simple", fn(doc, range, ctx):
        let action_list: List[CodeAction] = []

        # Quick fix for each diagnostic
        for diag in ctx.diagnostics:
            if diag.code == "unused-variable":
                let action = CodeAction.new("Remove unused variable", CodeActionKind_QuickFix)

                let edit = WorkspaceEdit.new()
                edit.delete(doc.uri, diag.range)

                action.edit = some(edit)
                action.is_preferred = true
                action_list.append(action)

        # Refactoring: Extract function
        if range.start.line != range.end.line:
            let refactor = CodeAction.new("Extract to function", CodeActionKind_RefactorExtract)
            action_list.append(refactor)

        # Source action: Organize imports
        let organize = CodeAction.new("Organize imports", CodeActionKind_SourceOrganizeImports)
        action_list.append(organize)

        return action_list
    )

    context.subscriptions.push(sub)
```

---

## Part 5: Workspace API

### Configuration

```simple
import vscode.workspace

# Get configuration
let config = workspace.get_configuration("simple")
let tab_size = config.get("tabSize")  # "4"
let format_on_save = config.get("formatOnSave")  # "true"

# Update configuration
config.update("tabSize", "2")
```

### File Operations

```simple
# Find files
let spl_files = workspace.find_files("**/*.spl", "**/target/**")
for file in spl_files:
    print "Found: " + file

# Open document
match workspace.open_text_document("file:///path/file.spl"):
    some(doc):
        print "Opened: " + doc.uri
    none:
        print "Failed to open"

# Save document
workspace.save_text_document("file:///path/file.spl")
```

### File System Watcher

```simple
let watcher = workspace.create_file_system_watcher("**/*.spl")

watcher.on_change(fn(uri):
    # Recompile on file change
    compile_file(uri)
)

watcher.on_create(fn(uri):
    print "New file: " + uri
)

watcher.on_delete(fn(uri):
    print "Deleted: " + uri
)

context.subscriptions.push(watcher)
```

---

## Part 6: Tasks

### Task Provider

```simple
import vscode.tasks

pub fn activate(context: ExtensionContext):
    let sub = tasks.register_task_provider("simple", fn():
        let task_list: List[Task] = []

        # Build task
        let build = tasks.create_build_task("Build Project", "simple build")
        task_list.append(build)

        # Test task
        let test = tasks.create_test_task("Run Tests", "simple test")
        task_list.append(test)

        # Custom task
        let fmt = tasks.create_custom_task("Format Code", "simple fmt", TaskGroup_Build)
        task_list.append(fmt)

        return task_list
    )

    context.subscriptions.push(sub)
```

### Executing Tasks

```simple
# Create and execute task
let def = TaskDefinition.new("simple")
let task = Task.new(def, "Build", "Simple")
task.execution = some(ShellExecution.new("simple build main.spl"))

tasks.execute_task(task)
```

---

## Part 7: Terminal Integration

### Creating Terminals

```simple
import vscode.terminal

# Simple terminal
let term = terminal.create_simple_terminal("My Terminal")
term.show()
term.send_text("echo Hello World")

# Terminal with options
let opts = TerminalOptions.new()
opts.name = "Build Output"
opts.cwd = "/workspace"
opts.env = {"NODE_ENV": "production"}

let build_term = terminal.create_terminal(opts)
build_term.show()
build_term.send_text("npm run build")
```

### Terminal Helpers

```simple
# Reuse terminal
let build = terminal.get_or_create_terminal("Build")
build.send_text("simple build")

# Run command in terminal
terminal.run_command("simple test", "Test")

# Specialized terminals
let build_term = terminal.create_build_terminal()
build_term.send_text("simple build")

let test_term = terminal.create_test_terminal()
test_term.send_text("simple test")
```

---

## Part 8: Tree Views

### Custom Tree Views

```simple
import vscode.tree_view

pub fn activate(context: ExtensionContext):
    # Create tree data provider
    let provider = TreeDataProvider.new("simple.fileExplorer")

    provider.get_children_fn = fn(element):
        match element:
            none:
                # Root level
                let src = tree_view.create_folder_item("src", "file:///workspace/src")
                let tests = tree_view.create_folder_item("tests", "file:///workspace/tests")
                return [src, tests]

            some(id):
                if id == "file:///workspace/src":
                    # Files in src
                    let main = tree_view.create_file_item("main.spl", "file:///workspace/src/main.spl")
                    let lib = tree_view.create_file_item("lib.spl", "file:///workspace/src/lib.spl")
                    return [main, lib]
                else:
                    return []

    # Register tree view
    let view = tree_view.create_tree_view("simple.fileExplorer", provider)
    view.reveal("file:///workspace/src/main.spl", true)
```

---

## Part 9: Document Providers

### Virtual Documents

```simple
import vscode.document_provider

pub fn activate(context: ExtensionContext):
    # Create AST viewer
    let ast_provider = TextDocumentContentProvider.new("simple-ast")

    ast_provider.provide_fn = fn(uri):
        # Extract real file path
        let file_path = uri.replace("simple-ast://", "")

        # Parse file and show AST
        let source = read_file(file_path)
        let ast = parse(source)
        return format_ast(ast)

    document_provider.register_text_document_content_provider("simple-ast", ast_provider)

    # Usage: Open "simple-ast://path/to/file.spl" to view AST
```

### Preview Provider

```simple
# Markdown preview
let preview = document_provider.create_preview_provider("simple-preview", fn(uri):
    let source = read_file(uri)
    return render_markdown(source)
)

document_provider.register_text_document_content_provider("simple-preview", preview)
```

---

## Part 10: Window API

### Messages

```simple
import vscode.window

# Information message
window.show_information_message("Operation completed")

# Warning message
window.show_warning_message("File not found")

# Error message
window.show_error_message("Compilation failed")
```

### Status Bar

```simple
# Create status bar item
let status = window.create_status_bar_item(StatusBarAlignment_Right, 100)
status.set_text("$(check) Ready")
status.set_tooltip("Simple language server ready")
status.show()

# Update status
status.set_text("$(sync~spin) Building...")

# Hide when done
status.hide()
```

---

## Part 11: Extension Manifest (package.json)

Extensions require a `package.json` manifest to declare their capabilities:

```json
{
  "name": "simple-language",
  "displayName": "Simple Language Support",
  "version": "1.0.0",
  "publisher": "simple-lang",
  "engines": {
    "vscode": "^1.70.0"
  },
  "categories": ["Programming Languages"],
  "activationEvents": [
    "onLanguage:simple",
    "onCommand:simple.build"
  ],
  "main": "./out/extension.js",
  "contributes": {
    "languages": [{
      "id": "simple",
      "extensions": [".spl"],
      "aliases": ["Simple", "simple"]
    }],
    "commands": [{
      "command": "simple.build",
      "title": "Simple: Build Project"
    }],
    "taskDefinitions": [{
      "type": "simple",
      "properties": {
        "task": {
          "type": "string",
          "description": "Task type (build, test, etc.)"
        }
      }
    }],
    "viewsContainers": {
      "activitybar": [{
        "id": "simple-explorer",
        "title": "Simple",
        "icon": "resources/simple.svg"
      }]
    },
    "views": {
      "simple-explorer": [{
        "id": "simple.fileExplorer",
        "name": "Files"
      }]
    }
  }
}
```

---

## Part 12: Build & Package

### Building Extensions

```bash
# Build extension WASM
simple vscode build my-extension.spl -o dist/

# Generate package.json manifest
simple vscode manifest my-extension.spl -o package.json

# Package extension (creates .vsix)
simple vscode package

# Install locally
code --install-extension simple-language-1.0.0.vsix

# Publish to marketplace
simple vscode publish
```

---

## Part 13: Testing Extensions

### Test Framework

```simple
# Extension test
import vscode
import spec

describe "Extension Activation":
    it "should register commands":
        # Activate extension
        activate(context)

        # Verify command registered
        let commands = vscode.commands.get_commands()
        expect(commands).to_contain("simple.build")

    it "should provide completions":
        let doc = create_test_document("let x = ")
        let pos = Position.new(0, 8)

        let items = completion_provider(doc, pos)
        expect(items.len()).to_be_greater_than(0)
        expect(items[0].label).to_equal("fn")
```

### E2E Tests

VSCode provides `@vscode/test-electron` for end-to-end testing:

```typescript
// test/suite/extension.test.ts
import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Extension Test Suite', () => {
    test('Should activate extension', async () => {
        const ext = vscode.extensions.getExtension('simple-lang.simple-language');
        assert.ok(ext);
        await ext?.activate();
    });

    test('Should provide completions', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'let x = '
        });

        const pos = new vscode.Position(0, 8);
        const items = await vscode.commands.executeCommand(
            'vscode.executeCompletionItemProvider',
            doc.uri,
            pos
        );

        assert.ok(items && (items as any).items.length > 0);
    });
});
```

---

## Part 14: Best Practices

### 1. Resource Cleanup

Always dispose of subscriptions:

```simple
pub fn activate(context: ExtensionContext):
    let sub1 = commands.register_command("cmd1", handler1)
    let sub2 = languages.register_completion_provider("simple", provider)

    context.subscriptions.push(sub1)
    context.subscriptions.push(sub2)  # Auto-disposed on deactivation
```

### 2. Error Handling

Handle errors gracefully:

```simple
pub fn activate(context: ExtensionContext):
    commands.register_command("simple.build", fn(args):
        try:
            build_project()
            window.show_information_message("Build succeeded!")
        catch e:
            window.show_error_message("Build failed: " + e.message)
    )
```

### 3. Async Operations

Use async for long-running operations:

```simple
async fn build_project():
    window.show_information_message("Building...")

    # Long operation
    await compile_all_files()

    window.show_information_message("Build complete!")
```

### 4. Performance

- Cache parsed ASTs and symbol tables
- Use incremental parsing for large files
- Debounce file change events
- Lazy-load providers

### 5. User Experience

- Provide clear error messages
- Show progress for long operations
- Use appropriate message severity (info/warning/error)
- Add tooltips to status bar items
- Group related commands in the command palette

---

## Part 15: Example Extensions

### 1. Language Server Extension

```simple
import vscode

pub fn activate(context: ExtensionContext):
    # Completion provider
    let completion_sub = vscode.languages.register_completion_provider("simple", fn(doc, pos):
        return get_completions(doc, pos)
    )

    # Hover provider
    let hover_sub = vscode.languages.register_hover_provider("simple", fn(doc, pos):
        return get_hover_info(doc, pos)
    )

    # Definition provider
    let definition_sub = vscode.languages.register_definition_provider("simple", fn(doc, pos):
        return find_definition(doc, pos)
    )

    # Diagnostics
    let diagnostics = vscode.languages.DiagnosticCollection.new("simple")

    # Watch for file changes
    let watcher = vscode.workspace.create_file_system_watcher("**/*.spl")
    watcher.on_change(fn(uri):
        let errors = check_file(uri)
        diagnostics.set(uri, errors)
    )

    context.subscriptions.push(completion_sub)
    context.subscriptions.push(hover_sub)
    context.subscriptions.push(definition_sub)
```

### 2. Build Task Extension

```simple
import vscode

pub fn activate(context: ExtensionContext):
    # Register task provider
    let task_sub = vscode.tasks.register_task_provider("simple", fn():
        return [
            vscode.tasks.create_build_task("Build", "simple build"),
            vscode.tasks.create_test_task("Test", "simple test"),
            vscode.tasks.create_custom_task("Format", "simple fmt", TaskGroup_Build)
        ]
    )

    # Build command
    let build_sub = vscode.commands.register_command("simple.build", fn(args):
        vscode.terminal.run_command("simple build", "Build")
    )

    context.subscriptions.push(task_sub)
    context.subscriptions.push(build_sub)
```

---

## Related Documentation

- [VSCode Extension API](https://code.visualstudio.com/api) - Official VSCode extension docs
- [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) - LSP specification
- [Debug Adapter Protocol](https://microsoft.github.io/debug-adapter-protocol/) - DAP specification
- [WebAssembly](https://webassembly.org/) - WASM specification
