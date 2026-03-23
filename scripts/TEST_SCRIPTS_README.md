# UI Backend Test Scripts

Two comprehensive PowerShell scripts for testing the Simple framework's UI backends on Windows.

## Scripts

### test_all_backends.ps1
**Comprehensive automated test suite for all 4 UI backends.**

Tests and validates:
- **TUI Backend**: Terminal user interface with headless testing
- **Web Backend**: HTTP server startup and endpoint response
- **Electron Backend**: Desktop application launcher
- **Tauri Backend**: Rust-based desktop shell (Cargo compilation check)
- **File Format Variations**: LF/CRLF line ending handling

**Usage:**
```powershell
PS> .\test_all_backends.ps1
PS> .\test_all_backends.ps1 -WebPort 9000
PS> .\test_all_backends.ps1 -DemoFile examples\ui\hello_simple.ui.sdn
```

**Parameters:**
- `-DemoFile` (string): Path to demo UI file. Default: `examples\ui\demo_kitchen_sink.ui.sdn`
- `-WebPort` (int): HTTP port for web backend. Default: `8765`
- `-TauriCargoPath` (string): Path to Tauri's Cargo.toml. Default: `tools\tauri-shell\src-tauri`
- `-ElectronPath` (string): Path to Electron app. Default: `tools\electron-shell`

**Output Example:**
```
═══════════════════════════════════════════════════════════════════════════
  Simple UI Backend Test Suite
═══════════════════════════════════════════════════════════════════════════

  Project Root: C:\dev\simple
  Simple Binary: C:\dev\simple\bin\release\simple.exe
  Demo File: C:\dev\simple\examples\ui\demo_kitchen_sink.ui.sdn
  Web Port: 8765

  [Test 1: TUI Backend (Headless)]
  [PASS] TUI backend executed successfully

  [Test 2: Web Backend]
  [PASS] Web server responds with status 200

  [Test 3: Electron Backend]
  [PASS] Electron shell launched successfully

  [Test 4: Tauri Backend]
  [PASS] Tauri shell launched successfully

  [Test 5: UI File Format Variations]
  [PASS] TUI handles LF line endings correctly

═══════════════════════════════════════════════════════════════════════════
  TEST SUMMARY
═══════════════════════════════════════════════════════════════════════════
  Passed:  5
  Failed:  0
  Skipped: 0
  Total:   5

  Result: ALL TESTS PASSED
```

### test_tui.ps1
**Interactive TUI demo launcher.**

Launches the kitchen sink demo with full terminal UI rendering. Perfect for visual testing of TUI capabilities.

**Usage:**
```powershell
PS> .\test_tui.ps1
PS> .\test_tui.ps1 -DemoFile examples\ui\hello_simple.ui.sdn
```

**Controls:**
- **↑ ↓ ← →**: Navigate menu items
- **Tab**: Move to next control
- **Enter**: Activate button or select option
- **Type**: Enter text in input fields
- **q / Esc**: Quit the demo
- **Ctrl+C**: Force quit

**Demonstrates:**
- Menubar, Tabs, Panels
- Text input, TextArea, Checkbox, Dropdown
- Lists, Trees, Tables
- Progress bars, Dividers, Status bar
- Full ANSI terminal rendering on Windows

## Requirements

### Prerequisites
- Windows 10 / Windows Server 2016+ with PowerShell 5.0+
- Simple binary at `bin\release\simple.exe` (run `scripts\setup.cmd` to configure)

### Optional Dependencies
- **Electron** (for desktop testing): `npm install -g electron`
- **Rust/Cargo** (for Tauri): https://www.rust-lang.org/tools/install
- **Node.js** (for npm): https://nodejs.org/

## Setup

1. Run the project setup:
   ```powershell
   PS> .\scripts\setup.cmd
   ```

2. (Optional) Install Electron for desktop testing:
   ```powershell
   PS> npm install -g electron
   ```

3. (Optional) Install Rust for Tauri testing:
   - Download from https://www.rust-lang.org/tools/install
   - Run the installer

## Troubleshooting

### Script won't run: "cannot be loaded because running scripts is disabled"
Enable script execution for your user:
```powershell
PS> Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

### Simple binary not found
Run setup:
```powershell
PS> .\scripts\setup.cmd
```

### Web backend test fails
Ensure port 8765 is available:
```powershell
PS> netstat -ano | findstr :8765
```

### Electron not found
Install it globally:
```powershell
PS> npm install -g electron
```

### Tauri compilation fails
Ensure Rust is installed and updated:
```powershell
PS> rustup update
PS> rustc --version
```

## Architecture

**test_all_backends.ps1** includes:
- Preflight validation of binaries and files
- Cross-backend testing infrastructure
- HTTP endpoint validation
- Process lifecycle management with timeout handling
- Dependency detection (Electron, Cargo, etc.)
- Graceful skipping of unavailable backends
- Color-coded output for easy reading
- Detailed exit codes and result reporting

**test_tui.ps1** includes:
- ASCII logo and styled output
- Interactive prerequisite checking
- User-friendly control instructions
- Clean error messaging
- Demo tips and usage guidance

## Exit Codes

- `0`: All tests passed (test_all_backends.ps1)
- `1`: One or more tests failed
- Script aborts if preflight checks fail

## Files Tested

- `examples/ui/demo_kitchen_sink.ui.sdn` - Comprehensive widget showcase
- Temporary test files created with various line endings (cleaned up automatically)

## See Also

- `scripts/test_ui_backends.cmd` - Older batch script version
- `doc/README.md` - Framework documentation
- `CLAUDE.md` - Development guidelines
