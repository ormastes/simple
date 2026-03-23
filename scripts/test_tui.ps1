#Requires -Version 5.0
<#
.SYNOPSIS
    Interactive TUI backend demo for the Simple framework.

.DESCRIPTION
    Launches the TUI (Terminal User Interface) backend with the kitchen sink demo.
    Shows all available widgets rendered in the terminal.

    Controls:
      - Navigate with arrow keys
      - Tab to move between controls
      - Enter to activate buttons
      - Type in input fields
      - Press 'q' or Ctrl+C to quit

.PARAMETER DemoFile
    Path to demo UI file (.ui.sdn). Defaults to examples/ui/demo_kitchen_sink.ui.sdn

.EXAMPLE
    PS> .\test_tui.ps1

.EXAMPLE
    PS> .\test_tui.ps1 -DemoFile examples\ui\hello_simple.ui.sdn
#>

param(
    [string]$DemoFile = "examples\ui\demo_kitchen_sink.ui.sdn"
)

# =========================================================================
# Configuration
# =========================================================================

$ErrorActionPreference = 'Continue'
$ProgressPreference = 'SilentlyContinue'

# Resolve paths relative to script location
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProjectRoot = Split-Path -Parent $ScriptDir
$SimpleBin = Join-Path $ProjectRoot "bin\release\simple.exe"
$DemoFullPath = Join-Path $ProjectRoot $DemoFile

# =========================================================================
# Utility Functions
# =========================================================================

function Write-Logo {
    Write-Host @"
 _____ _           _
|  ___| |         | |
| |_  | |__  | |  | |__
|  _| | '_ \ | |  | '_ \
| |   | |_) | \  \_/ |_) |
\_|   |_.__/   \_/\_./___/

 UI Framework - TUI Backend Demo

"@ -ForegroundColor Cyan
}

function Verify-Prerequisites {
    Write-Host "Checking prerequisites..." -ForegroundColor Yellow

    if (-not (Test-Path $SimpleBin)) {
        Write-Host "ERROR: Simple binary not found at:" -ForegroundColor Red
        Write-Host "  $SimpleBin" -ForegroundColor Red
        Write-Host ""
        Write-Host "Solution: Run scripts\setup.cmd to configure the project." -ForegroundColor Yellow
        exit 1
    }

    if (-not (Test-Path $DemoFullPath)) {
        Write-Host "ERROR: Demo file not found at:" -ForegroundColor Red
        Write-Host "  $DemoFullPath" -ForegroundColor Red
        exit 1
    }

    Write-Host "  ✓ Simple binary found" -ForegroundColor Green
    Write-Host "  ✓ Demo file found" -ForegroundColor Green
    Write-Host ""
}

function Show-Instructions {
    Write-Host "CONTROLS:" -ForegroundColor Cyan
    Write-Host "  ↑ ↓ ← → : Navigate menu items" -ForegroundColor Gray
    Write-Host "  Tab      : Move to next control" -ForegroundColor Gray
    Write-Host "  Enter    : Activate button or select option" -ForegroundColor Gray
    Write-Host "  Type     : Enter text in input fields" -ForegroundColor Gray
    Write-Host "  q / Esc  : Quit the demo" -ForegroundColor Gray
    Write-Host "  Ctrl+C   : Force quit" -ForegroundColor Gray
    Write-Host ""
    Write-Host "This demo shows all supported widgets:" -ForegroundColor Cyan
    Write-Host "  • Menubar, Tabs, Panels" -ForegroundColor Gray
    Write-Host "  • Text input, TextArea, Checkbox, Dropdown" -ForegroundColor Gray
    Write-Host "  • Lists, Trees, Tables" -ForegroundColor Gray
    Write-Host "  • Progress bars, Dividers, Status bar" -ForegroundColor Gray
    Write-Host ""
}

function Launch-TuiDemo {
    Write-Host "Launching TUI demo..." -ForegroundColor Yellow
    Write-Host "Press Ctrl+C to force quit at any time." -ForegroundColor Yellow
    Write-Host ""
    Write-Host ("=" * 75) -ForegroundColor Gray
    Write-Host ""

    try {
        # Launch TUI with the demo file
        # The & operator allows the process to run interactively
        & $SimpleBin ui tui $DemoFullPath
    }
    catch {
        Write-Host ""
        Write-Host "Error launching TUI: $($_.Exception.Message)" -ForegroundColor Red
        exit 1
    }
}

function Show-ExitMessage {
    Write-Host ""
    Write-Host ("=" * 75) -ForegroundColor Gray
    Write-Host ""
    Write-Host "Demo closed." -ForegroundColor Green
    Write-Host ""
    Write-Host "Tips:" -ForegroundColor Yellow
    Write-Host "  • Modify demo file: $DemoFile" -ForegroundColor Gray
    Write-Host "  • Run test suite: .\test_all_backends.ps1" -ForegroundColor Gray
    Write-Host "  • Build Tauri: cd $ProjectRoot\tools\tauri-shell\src-tauri && cargo build --release" -ForegroundColor Gray
    Write-Host ""
}

# =========================================================================
# Main
# =========================================================================

function Main {
    Clear-Host
    Write-Logo
    Verify-Prerequisites
    Show-Instructions
    Launch-TuiDemo
    Show-ExitMessage
}

Main
