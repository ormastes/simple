# Simple Language Extension for VSCode

Rich language support for the Simple programming language, powered by Tree-sitter and Language Server Protocol (LSP).

## Features

### ✨ Semantic Syntax Highlighting

Tree-sitter-powered, accurate syntax highlighting that understands your code structure:

- **Keywords** - Control flow, declarations, modifiers
- **Functions** - Definitions, calls, methods
- **Types** - Primitives, user-defined, generics
- **Variables** - Parameters, fields, bindings
- **Literals** - Strings (including f-strings), numbers, booleans
- **Comments** - Line, block, documentation

### 🚀 Language Server Features

- **Code Completion** - Intelligent completions for keywords, types, functions
- **Go to Definition** - Jump to symbol definitions (F12)
- **Hover Information** - View documentation on hover
- **Find References** - Find all references to a symbol (Shift+F12)
- **Diagnostics** - Real-time parse error reporting with error recovery
- **Incremental Parsing** - Fast, efficient updates as you type

### 🤖 AI-Powered Features

Supercharge your Simple development with AI assistance (requires GitHub Copilot or compatible extension):

- **🎯 Inline Completions** - Get AI-powered code suggestions as you type (ghost text)
- **💬 AI Chat Panel** - Interactive coding assistant for questions and help
- **📖 Code Explanation** - Understand what your code does (right-click → Explain Selected Code)
- **✅ Code Review** - Get suggestions for improvements (right-click → Review Selected Code)
- **🪄 Code Generation** - Generate code from natural language descriptions
- **🔄 Context-Aware** - AI understands your file structure and imports

**Status Bar Icons:**
- `$(sparkle) AI` - AI completions enabled (click to toggle)
- `$(circle-slash) AI` - AI completions disabled (click to enable)
- `$(warning) AI` - Language model not available (install Copilot)

**Commands:**
- `Cmd/Ctrl+Shift+P` → "Simple AI: Open Chat Panel"
- `Cmd/Ctrl+Shift+P` → "Simple AI: Generate Code from Description"
- Right-click on selected code → "Explain Selected Code" / "Review Selected Code"

## Installation

### From VSIX (Recommended)

1. Download `simple-language-0.1.0.vsix` from releases
2. Install via VSCode:
   ```bash
   code --install-extension simple-language-0.1.0.vsix
   ```

   Or use the VSCode UI: Extensions → ··· → Install from VSIX

### Build from Source

```bash
# Clone repository
git clone https://github.com/simple-lang/simple
cd simple/simple/app/vscode_extension

# Install dependencies
npm install

# Compile TypeScript
npm run compile

# Package extension
npm run package

# Install
code --install-extension simple-language-0.1.0.vsix
```

## Requirements

- **VSCode** 1.80.0 or higher
- **Simple LSP Server** (`simple-lsp`) must be in your PATH

### Optional Bundled WASM Artifacts

The extension can bundle prebuilt WASM artifacts under `wasm/`:

- `wasm/simple-lsp.wasm`
- `wasm/math-core.wasm`

`npm run compile` now runs a staging step after TypeScript compilation. It copies
WASM files into `wasm/` from either explicit source paths or a shared build
directory:

```bash
# Stage artifacts from explicit files
export SIMPLE_VSCODE_LSP_WASM_SOURCE=/abs/path/to/simple-lsp.wasm
export SIMPLE_VSCODE_MATH_WASM_SOURCE=/abs/path/to/math-core.wasm
npm run compile

# Or stage both from one build directory
export SIMPLE_VSCODE_WASM_BUILD_DIR=/abs/path/to/generated-wasm
npm run compile
```

The default math-core build now comes from the pure-Simple entrypoint in
`src/app/vscode_extension/math_core/main.spl` and stages the resulting artifact
into `wasm/math-core.wasm`:

```bash
npm run build:math-core-wasm
```

This uses `simple compile src/app/vscode_extension/math_core/main.spl --target=wasm32-wasi`
from the repo root. The script looks for `simple` in this order:

- `SIMPLE_VSCODE_SIMPLE_BIN`
- `src/compiler_rust/target/debug/simple`
- `src/compiler_rust/target/release/simple`
- `simple` from your `PATH`

`npm run compile` now rebuilds the pure-Simple `math-core.wasm` first, then
stages any explicit wasm overrides (`SIMPLE_VSCODE_*`) afterward.

The existing `SIMPLE_VSCODE_MATH_WASM_SOURCE` and `SIMPLE_VSCODE_WASM_BUILD_DIR`
paths still work for overriding the staged artifact after the default build.

### Building WASM On macOS

For LLVM-backed WASM builds on this machine, the working environment was:

```bash
export LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18
export PATH=/opt/homebrew/opt/llvm@18/bin:$PATH
export LIBRARY_PATH=/opt/homebrew/lib:/opt/homebrew/opt/zstd/lib:$LIBRARY_PATH
export DYLD_LIBRARY_PATH=/opt/homebrew/lib:/opt/homebrew/opt/zstd/lib:$DYLD_LIBRARY_PATH
```

Then build the driver with LLVM enabled:

```bash
cd src/compiler_rust
cargo build -p simple-driver --bin simple --features llvm
```

Example artifact generation:

```bash
# Generic target compile
src/compiler_rust/target/debug/simple compile /tmp/simple_vscode_smoke.spl --target=wasm32-wasi -o /tmp/simple_vscode_smoke.smf

# VSCode scaffold build
src/compiler_rust/target/debug/simple vscode build /tmp/simple_vscode_smoke.spl -o /tmp/simple-vscode-out --name math-core-test --display-name "Math Core Test" --publisher ormastes --version 0.0.1 --release
```

### Installing Simple LSP Server

```bash
# Build Simple compiler
cd simple
cargo build --release

# Add to PATH (Linux/macOS)
export PATH="$PATH:$(pwd)/target/release"

# Or specify path in VSCode settings
```

## Configuration

Access settings via: Preferences → Settings → Extensions → Simple

### `simple.lsp.serverPath`

Path to the `simple-lsp` executable.

- **Default:** `"simple-lsp"` (assumes it's in PATH)
- **Example:** `"/home/user/simple/target/release/simple-lsp"`

```json
{
  "simple.lsp.serverPath": "/path/to/simple-lsp"
}
```

### `simple.lsp.trace.server`

Trace LSP communication for debugging.

- **Options:** `"off"`, `"messages"`, `"verbose"`
- **Default:** `"off"`

```json
{
  "simple.lsp.trace.server": "verbose"
}
```

### `simple.lsp.enableSemanticTokens`

Enable/disable semantic syntax highlighting.

- **Default:** `true`

```json
{
  "simple.lsp.enableSemanticTokens": true
}
```

### `simple.lsp.debounceDelay`

Delay before sending document changes to LSP server (milliseconds).

- **Default:** `300`
- **Range:** 0-2000

```json
{
  "simple.lsp.debounceDelay": 300
}
```

### `simple.ai.enabled`

Enable/disable AI-powered features.

- **Default:** `true`
- **Requires:** GitHub Copilot or compatible language model extension

```json
{
  "simple.ai.enabled": true
}
```

### `simple.ai.inlineCompletions`

Enable/disable AI-powered inline code completions (ghost text suggestions).

- **Default:** `true`

```json
{
  "simple.ai.inlineCompletions": true
}
```

### `simple.ai.chatPanel`

Enable/disable AI chat panel.

- **Default:** `true`

```json
{
  "simple.ai.chatPanel": true
}
```

## Usage

### Math Demo Workspace

Use the files under `src/app/vscode_extension/test-workspace/` to verify the
local math rendering path in VSCode.

For arithmetic-focused coverage, open:

`src/app/vscode_extension/test-workspace/math_arithmetic_demo.spl`

This file exercises:

- addition: `2 + 3`
- subtraction: `10 - 3`
- multiplication: `4 * 5`
- division: `15 / 3`
- fractions and powers: `frac(1, 2) + alpha^2`
- roots: `sqrt(x^2 + y^2)`
- sums: `sum(i, 0..10) i^2`
- integrals: `int(x, 0..1) x^2`
- transpose: `A' + B'`

Expected pretty output examples:

- `frac(1, 2) + alpha^2` → `(1)/(2) + α²`
- `sum(i, 0..10) i^2` → `∑(i=0..10) i²`
- `int(x, 0..1) x^2` → `∫(x=0..1) x²`
- `A' + B'` → `Aᵀ + Bᵀ`

### Synced Math Panel

The extension also provides a synced companion panel that mirrors the active
math block and delegates edits back to the source document.

Open it from the Command Palette with:

- `Simple: Toggle Synced Math Panel`

Use this when you want a rendered math surface alongside the source editor
without leaving the `.spl` document as the source of truth.

### Viewing LSP Server Output

1. Open Output panel: **View** → **Output**
2. Select **Simple Language Server** from dropdown

Or use command palette:

```
Simple: Show LSP Server Output
```

### Restarting LSP Server

If the LSP server becomes unresponsive:

1. Command Palette (Ctrl+Shift+P / Cmd+Shift+P)
2. Search: `Simple: Restart LSP Server`

### Enabling Semantic Highlighting

Semantic highlighting should be enabled by default. If not:

1. Open Settings
2. Search: `editor.semanticHighlighting.enabled`
3. Set to `true` or `configuredByTheme`

## Troubleshooting

### LSP Server Not Starting

**Symptoms:** No syntax highlighting, no completions, status bar shows error

**Solutions:**

1. **Check LSP server is installed:**
   ```bash
   which simple-lsp
   # or
   simple-lsp --version
   ```

2. **Check output panel:**
   - View → Output → Simple Language Server
   - Look for error messages

3. **Verify configuration:**
   - Settings → Simple → LSP Server Path
   - Ensure path is correct and executable

4. **Try absolute path:**
   ```json
   {
     "simple.lsp.serverPath": "/full/path/to/simple-lsp"
   }
   ```

### Semantic Highlighting Not Working

**Symptoms:** Basic highlighting works, but no semantic colors

**Solutions:**

1. **Enable semantic highlighting:**
   ```json
   {
     "editor.semanticHighlighting.enabled": true
   }
   ```

2. **Check feature is enabled:**
   ```json
   {
     "simple.lsp.enableSemanticTokens": true
   }
   ```

3. **Restart LSP server:**
   - Command: `Simple: Restart LSP Server`

### Performance Issues

**Symptoms:** Slow completions, laggy typing

**Solutions:**

1. **Increase debounce delay:**
   ```json
   {
     "simple.lsp.debounceDelay": 500
   }
   ```

2. **Check LSP server logs:**
   - View → Output → Simple Language Server
   - Look for performance warnings

3. **Reduce file watching:**
   - Close unused Simple projects
   - Exclude build directories from workspace

### LSP Server Crashes

**Symptoms:** Status bar shows error, no features work

**Solutions:**

1. **Check server output:**
   - View → Output → Simple Language Server
   - Look for panic or error messages

2. **Report issue:**
   - Copy error logs
   - Create issue at: https://github.com/simple-lang/simple/issues

3. **Restart server:**
   - Command: `Simple: Restart LSP Server`

### AI Features Not Working

**Symptoms:** No inline completions, AI commands unavailable

**Solutions:**

1. **Install GitHub Copilot:**
   - VSCode Extensions → Search "GitHub Copilot"
   - Install and sign in with GitHub account
   - Or install compatible language model extension

2. **Check AI features are enabled:**
   ```json
   {
     "simple.ai.enabled": true,
     "simple.ai.inlineCompletions": true
   }
   ```

3. **Check output panel:**
   - View → Output → Simple AI Assistant
   - Look for "No language models available" warning

4. **Verify Copilot is active:**
   - Check Copilot status in status bar
   - Sign in if needed

5. **Toggle inline completions:**
   - Click AI icon in status bar
   - Or Command: `Simple AI: Toggle AI Inline Completions`

### AI Chat Panel Not Opening

**Solutions:**

1. **Check configuration:**
   ```json
   {
     "simple.ai.chatPanel": true
   }
   ```

2. **Use command:**
   - Cmd/Ctrl+Shift+P → "Simple AI: Open Chat Panel"

3. **Check for errors:**
   - View → Output → Simple AI Assistant

### AI Completions Too Slow

**Solutions:**

1. **Use smaller model (if available):**
   - AI typically uses GPT-4 by default
   - Smaller models may be faster

2. **Disable inline completions:**
   ```json
   {
     "simple.ai.inlineCompletions": false
   }
   ```
   Or click AI icon in status bar to toggle

3. **Use chat panel instead:**
   - Better for complex queries
   - Less interruption during typing

## Math Block Rendering

Simple supports three math block types with full syntax highlighting:
`m{}`, `loss{}`, and `nograd{}`.

```simple
val result = m{ x^2 + y^2 }
val sigmoid = loss{ frac(1, 1 + exp(-x)) }
val init = nograd{ sqrt(frac(6, fan_in + fan_out)) }
```

**Syntax highlighting** covers:
- Block delimiters (`m{`, `loss{`, `nograd{`) as keywords
- Nested braces (e.g., `m{ \frac{10}{2} }` highlights correctly)
- Math functions: `sin`, `cos`, `tan`, `tanh`, `exp`, `log`, `sqrt`, `abs`, `frac`, `sum`, `product`, `integral`, `dot`, `softmax`, `relu`, `sigmoid`
- Greek letters: `alpha`, `beta`, `gamma`, `theta`, `sigma`, `omega`, etc.
- Math operators: `^`, `@`, `.+`, `.-`, `.*`, `./`, `.^`, `'`, `..`
- LaTeX commands: `\frac`, `\sqrt`, `\sum`, `\exp`, `\pi`, etc.
- Constants: `pi`, `e`, `infinity`, `partial`, `nabla`

**LSP hover** shows rendered math (LaTeX, Unicode, Markdown) when hovering over math blocks.

**Commands:**
- `Simple: Toggle Math Preview` — toggle math preview panel
- `Simple: Toggle Synced Math Panel` — open the synced math companion panel
- `Simple: Toggle Inline Render` — toggle inline rendering

**Settings:**
- `simple.math.previewOnHover` — show math hover previews
- `simple.math.syncPanel.autoOpen` — automatically open the synced math panel when the caret enters a math block
- `simple.math.renderInline` — enable inline math decorations

## Test CodeLens (Gutter Arrows)

The extension shows "▶ Run" CodeLens buttons above test blocks in `.spl` files:

| Block | CodeLens |
|-------|----------|
| `describe "...":` | ▶ Run File |
| `context "...":` | ▶ Run Test |
| `it "...":` | ▶ Run Test |
| `""" sdoctest:` | ▶ Run Doctest |

Clicking a CodeLens runs the test via `bin/simple test` in the integrated terminal.

## Features in Detail

### Semantic Tokens

Powered by Tree-sitter queries (`highlights.scm`), semantic tokens provide:

- **Context-aware highlighting** - Functions are colored differently in definitions vs calls
- **Modifier support** - Async, deprecated, readonly symbols have distinct styles
- **Fast updates** - Incremental parsing for instant feedback

### Code Completion

Intelligent completions based on:

- Language keywords and constructs
- Types in scope
- Functions and methods
- Variables and parameters
- Import suggestions

### Hover Documentation

Hover over symbols to see:

- Type information
- Function signatures
- Documentation comments
- Source location

### Go to Definition

Jump to definitions with F12:

- Functions
- Classes, enums, traits
- Variables
- Type aliases

### Find References

Find all uses of a symbol (Shift+F12):

- Function calls
- Variable references
- Type usage

### Diagnostics

Real-time error reporting:

- Parse errors with error recovery
- Syntax issues
- Squiggly underlines with quick info

## Development

### Running in Development Mode

1. Open `simple/app/vscode_extension/` in VSCode
2. Press F5 to launch Extension Development Host
3. Open a .spl file to test

### Debugging LSP Communication

Enable verbose tracing:

```json
{
  "simple.lsp.trace.server": "verbose"
}
```

View in Output panel: Simple Language Server

### Building

```bash
npm install
npm run compile
npm run package
```

### Publishing

```bash
# Login to VSCode marketplace
vsce login simple-lang

# Publish new version
vsce publish
```

## Keyboard Shortcuts

| Action | Windows/Linux | macOS |
|--------|---------------|-------|
| Go to Definition | F12 | F12 |
| Peek Definition | Alt+F12 | ⌥F12 |
| Find References | Shift+F12 | ⇧F12 |
| Rename Symbol | F2 | F2 |
| Show Hover | Ctrl+K Ctrl+I | ⌘K ⌘I |
| Trigger Completion | Ctrl+Space | ⌃Space |

## Contributing

Contributions welcome! Please see [CONTRIBUTING.md](../CONTRIBUTING.md)

## License

MIT License - see [LICENSE](../LICENSE)

## Links

- [Simple Language](https://github.com/simple-lang/simple)
- [Report Issues](https://github.com/simple-lang/simple/issues)
- [LSP Specification](https://microsoft.github.io/language-server-protocol/)
- [Tree-sitter](https://tree-sitter.github.io/tree-sitter/)
