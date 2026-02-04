# VS Code Setup Guide: Simple LSP and DAP

**Complete guide for setting up Simple language support in Visual Studio Code**

---

## Prerequisites

- ✅ Simple compiler installed (`simple --version` should work)
- ✅ VS Code installed (version 1.60+)
- ✅ Simple binary in PATH: `/path/to/simple/bin/simple`

---

## Part 1: LSP Setup (Code Intelligence)

### Step 1: Install Simple LSP Extension (if available)

```bash
# If Simple has a published VS Code extension
code --install-extension simple.simple-language-support
```

**OR** configure manually (see Step 2)

### Step 2: Manual LSP Configuration

Create `.vscode/settings.json` in your Simple project:

```json
{
  "simple.lsp.enabled": true,
  "simple.lsp.serverPath": "/path/to/simple/bin/simple",
  "simple.lsp.serverArgs": ["lsp", "start"],
  "simple.lsp.trace.server": "verbose",

  // Language association
  "[simple]": {
    "editor.defaultFormatter": "simple.simple-language-support",
    "editor.formatOnSave": true
  },

  // IntelliSense settings
  "editor.quickSuggestions": {
    "other": true,
    "comments": false,
    "strings": false
  },
  "editor.suggest.snippetsPreventQuickSuggestions": false,

  // Diagnostics
  "simple.lsp.diagnostics.enable": true,
  "simple.lsp.diagnostics.delay": 500
}
```

### Step 3: Configure Language Server

Create `.vscode/launch.json` for LSP server configuration:

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Start Simple LSP Server",
      "type": "node",
      "request": "launch",
      "program": "${workspaceFolder}/bin/simple",
      "args": ["lsp", "start", "--stdio"],
      "console": "integratedTerminal",
      "cwd": "${workspaceFolder}"
    }
  ]
}
```

### Step 4: Define File Associations

Create `.vscode/extensions.json`:

```json
{
  "recommendations": [
    "simple.simple-language-support"
  ]
}
```

Create `.vscode/languages.json`:

```json
{
  "contributes": {
    "languages": [
      {
        "id": "simple",
        "aliases": ["Simple", "simple"],
        "extensions": [".spl", ".sspec"],
        "configuration": "./language-configuration.json"
      }
    ]
  }
}
```

### Step 5: Create Language Configuration

Create `.vscode/language-configuration.json`:

```json
{
  "comments": {
    "lineComment": "#",
    "blockComment": ["#[", "]#"]
  },
  "brackets": [
    ["{", "}"],
    ["[", "]"],
    ["(", ")"]
  ],
  "autoClosingPairs": [
    { "open": "{", "close": "}" },
    { "open": "[", "close": "]" },
    { "open": "(", "close": ")" },
    { "open": "\"", "close": "\"", "notIn": ["string"] },
    { "open": "'", "close": "'", "notIn": ["string", "comment"] }
  ],
  "surroundingPairs": [
    ["{", "}"],
    ["[", "]"],
    ["(", ")"],
    ["\"", "\""],
    ["'", "'"]
  ],
  "folding": {
    "markers": {
      "start": "^\\s*#\\s*region\\b",
      "end": "^\\s*#\\s*endregion\\b"
    }
  },
  "wordPattern": "(-?\\d*\\.\\d\\w*)|([^\\`\\~\\!\\@\\#\\%\\^\\&\\*\\(\\)\\-\\=\\+\\[\\{\\]\\}\\\\\\|\\;\\:\\'\\\"\\,\\.\\<\\>\\/\\?\\s]+)"
}
```

### Step 6: Test LSP Features

Open a Simple file and test:

1. **Auto-completion**: Type `fn ` and press Ctrl+Space
2. **Hover**: Hover over a function name to see signature
3. **Go to Definition**: Ctrl+Click or F12 on a symbol
4. **Find References**: Right-click → Find All References
5. **Diagnostics**: Introduce syntax error and see red squigglies

---

## Part 2: DAP Setup (Debugging)

### Step 1: Configure Debug Adapter

Add to `.vscode/launch.json`:

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Debug Simple Program",
      "type": "simple",
      "request": "launch",
      "program": "${file}",
      "args": [],
      "cwd": "${workspaceFolder}",
      "stopOnEntry": true,
      "console": "integratedTerminal",
      "debugAdapter": {
        "type": "executable",
        "command": "simple",
        "args": ["dap", "start", "--stdio"]
      }
    },
    {
      "name": "Debug Simple Program (No Stop)",
      "type": "simple",
      "request": "launch",
      "program": "${file}",
      "args": [],
      "cwd": "${workspaceFolder}",
      "stopOnEntry": false,
      "console": "integratedTerminal"
    },
    {
      "name": "Debug Simple Tests",
      "type": "simple",
      "request": "launch",
      "program": "${workspaceFolder}/test",
      "args": ["--test-runner"],
      "cwd": "${workspaceFolder}",
      "stopOnEntry": false
    }
  ]
}
```

### Step 2: Configure Breakpoints

The Simple DAP supports:

- **Line breakpoints**: Click left of line numbers
- **Conditional breakpoints**: Right-click breakpoint → Edit Breakpoint → Add condition
- **Log points**: Right-click → Add Logpoint
- **Function breakpoints**: In Breakpoints pane → Add Function Breakpoint

Example conditional breakpoint:
```simple
x > 10 and y < 5
```

Example log point message:
```
Value of x is {x}, y is {y}
```

### Step 3: Debug Controls

Keyboard shortcuts:
- **F5**: Start debugging / Continue
- **F10**: Step over
- **F11**: Step into
- **Shift+F11**: Step out
- **F9**: Toggle breakpoint
- **Shift+F5**: Stop debugging
- **Ctrl+Shift+F5**: Restart debugging

### Step 4: Variable Inspection

While debugging:

1. **Variables Pane**: See local/global variables
2. **Watch Expressions**: Add expressions to monitor
3. **Call Stack**: See function call hierarchy
4. **Debug Console**: Evaluate expressions at runtime

Example debug console commands:
```
> x + y
> myFunction(42)
> self.field_name
```

### Step 5: Test Debugging

Create a test file `debug_test.spl`:

```simple
fn factorial(n: i64) -> i64:
    if n <= 1:
        1  # Breakpoint here
    else:
        n * factorial(n - 1)  # Breakpoint here

fn main():
    val result = factorial(5)
    print "Result: {result}"
```

Set breakpoints on lines 3 and 6, then:
1. Press F5 to start debugging
2. Use F10 to step over
3. Use F11 to step into recursive call
4. Inspect `n` variable in Variables pane
5. Add watch expression: `n * 2`

---

## Part 3: Integrated Experience

### LSP + DAP Together

Create `.vscode/tasks.json` for build tasks:

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "build-simple",
      "type": "shell",
      "command": "simple",
      "args": ["build"],
      "group": {
        "kind": "build",
        "isDefault": true
      },
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": []
    },
    {
      "label": "test-simple",
      "type": "shell",
      "command": "simple",
      "args": ["test"],
      "group": {
        "kind": "test",
        "isDefault": true
      }
    },
    {
      "label": "lint-simple",
      "type": "shell",
      "command": "simple",
      "args": ["lint", "${file}"],
      "group": "none"
    }
  ]
}
```

### Recommended Extensions

Add to `.vscode/extensions.json`:

```json
{
  "recommendations": [
    "simple.simple-language-support",
    "ms-vscode.vscode-js-debug",
    "dbaeumer.vscode-eslint",
    "esbenp.prettier-vscode"
  ]
}
```

### Workspace Settings

Complete `.vscode/settings.json`:

```json
{
  // LSP Settings
  "simple.lsp.enabled": true,
  "simple.lsp.serverPath": "simple",
  "simple.lsp.serverArgs": ["lsp", "start"],
  "simple.lsp.trace.server": "messages",
  "simple.lsp.diagnostics.enable": true,
  "simple.lsp.diagnostics.delay": 500,

  // DAP Settings
  "simple.dap.enabled": true,
  "simple.dap.adapterPath": "simple",
  "simple.dap.adapterArgs": ["dap", "start"],

  // Editor Settings
  "[simple]": {
    "editor.defaultFormatter": "simple.simple-language-support",
    "editor.formatOnSave": true,
    "editor.tabSize": 4,
    "editor.insertSpaces": true,
    "editor.semanticHighlighting.enabled": true
  },

  // File Associations
  "files.associations": {
    "*.spl": "simple",
    "*.sspec": "simple"
  },

  // Search Exclusions
  "search.exclude": {
    "**/build/**": true,
    "**/.simple/**": true
  },

  // Build on Save
  "simple.build.onSave": false,
  "simple.lint.onSave": true
}
```

---

## Troubleshooting

### LSP Server Not Starting

**Check server path**:
```bash
which simple
# Should output: /path/to/simple/bin/simple
```

**Check server logs**:
- View → Output → Select "Simple LSP" from dropdown
- Look for connection errors or startup issues

**Manual test**:
```bash
simple lsp start --stdio
# Should start LSP server and wait for JSON-RPC input
```

### Completion Not Working

1. **Check LSP is running**: Status bar should show "Simple LSP: Ready"
2. **Check file is recognized**: File should have Simple icon
3. **Reload window**: Ctrl+Shift+P → "Reload Window"
4. **Check output panel**: View → Output → Simple LSP

### Debugging Not Working

**Check DAP adapter**:
```bash
simple dap start --stdio
# Should start DAP server
```

**Check launch configuration**: Ensure `debugAdapter.command` points to `simple`

**Enable DAP logging**: Add to `launch.json`:
```json
{
  "trace": true,
  "logFile": "/tmp/simple-dap.log"
}
```

### Breakpoints Not Hitting

1. **Ensure debugging is enabled** in Simple runtime
2. **Check file path** matches exactly (case-sensitive)
3. **Verify breakpoint line** has executable code (not comments/blank)
4. **Check breakpoint indicator** is red (enabled) not gray (disabled)

### Performance Issues

**Disable features temporarily**:
```json
{
  "simple.lsp.diagnostics.enable": false,
  "simple.lsp.semanticTokens.enable": false
}
```

**Increase diagnostic delay**:
```json
{
  "simple.lsp.diagnostics.delay": 2000
}
```

---

## Advanced Configuration

### Multi-root Workspaces

For projects with multiple Simple packages:

```json
{
  "folders": [
    { "path": "package-a" },
    { "path": "package-b" }
  ],
  "settings": {
    "simple.lsp.workspaceRoots": [
      "${workspaceFolder}/package-a",
      "${workspaceFolder}/package-b"
    ]
  }
}
```

### Custom Build Tasks

Pre-launch build task:

```json
{
  "name": "Debug with Build",
  "type": "simple",
  "request": "launch",
  "program": "${file}",
  "preLaunchTask": "build-simple"
}
```

### Remote Debugging

Debug on remote machine:

```json
{
  "name": "Remote Debug",
  "type": "simple",
  "request": "attach",
  "address": "192.168.1.100",
  "port": 9229,
  "remoteRoot": "/remote/path",
  "localRoot": "${workspaceFolder}"
}
```

---

## Tips and Best Practices

### 1. Use Workspace Recommendations

Create `.vscode/extensions.json` to auto-suggest Simple extension to collaborators.

### 2. Configure Auto-Save

For live error checking:
```json
{
  "files.autoSave": "afterDelay",
  "files.autoSaveDelay": 1000
}
```

### 3. Enable Semantic Highlighting

For better syntax coloring:
```json
{
  "editor.semanticHighlighting.enabled": true
}
```

### 4. Use Integrated Terminal

Run Simple commands directly:
- Ctrl+` to open terminal
- Type `simple build`, `simple test`, etc.

### 5. Configure Git Integration

Add to `.gitignore`:
```
.vscode/*
!.vscode/settings.json
!.vscode/tasks.json
!.vscode/launch.json
!.vscode/extensions.json
build/
.simple/
```

---

## Complete Example Project Structure

```
my-simple-project/
├── .vscode/
│   ├── settings.json          # LSP/DAP settings
│   ├── launch.json            # Debug configurations
│   ├── tasks.json             # Build tasks
│   ├── extensions.json        # Extension recommendations
│   └── language-configuration.json  # Simple language config
├── src/
│   └── main.spl              # Source files
├── test/
│   └── main_spec.spl         # Test files
├── simple.sdn                 # Project manifest
└── README.md
```

---

## Resources

- **Simple Documentation**: `/path/to/simple/doc/`
- **LSP Protocol**: https://microsoft.github.io/language-server-protocol/
- **DAP Protocol**: https://microsoft.github.io/debug-adapter-protocol/
- **VS Code API**: https://code.visualstudio.com/api

---

## Getting Help

**Issue Tracker**: https://github.com/simple-lang/simple/issues
**Community**: Simple language Discord/Slack
**Documentation**: `simple --help lsp` and `simple --help dap`

---

**Status**: ✅ Complete VS Code setup guide for Simple LSP and DAP
