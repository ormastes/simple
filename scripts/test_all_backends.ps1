#Requires -Version 5.0
<#
.SYNOPSIS
    Comprehensive Windows PowerShell test suite for all 4 Simple UI backends.

.DESCRIPTION
    Tests TUI (terminal), Web (HTTP), Electron, and Tauri UI backends.
    Validates that each backend can start, respond, and handle basic UI rendering.

.PARAMETER DemoFile
    Path to demo UI file (.ui.sdn). Defaults to examples/ui/demo_kitchen_sink.ui.sdn

.PARAMETER WebPort
    Port for web backend. Defaults to 8765

.PARAMETER TauriCargoPath
    Path to Tauri's Cargo.toml. Defaults to tools/tauri-shell/src-tauri

.PARAMETER ElectronPath
    Path to Electron app. Defaults to tools/electron-shell

.EXAMPLE
    PS> .\test_all_backends.ps1

.EXAMPLE
    PS> .\test_all_backends.ps1 -DemoFile examples\ui\hello_simple.ui.sdn -WebPort 9000
#>

param(
    [string]$DemoFile = "examples\ui\demo_kitchen_sink.ui.sdn",
    [int]$WebPort = 8765,
    [string]$TauriCargoPath = "tools\tauri-shell\src-tauri",
    [string]$ElectronPath = "tools\electron-shell"
)

# =========================================================================
# Configuration & Paths
# =========================================================================

$ErrorActionPreference = 'Continue'
$ProgressPreference = 'SilentlyContinue'

# Resolve paths relative to script location
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProjectRoot = Split-Path -Parent $ScriptDir
$SimpleBin = Join-Path $ProjectRoot "bin\release\simple.exe"
$DemoFullPath = Join-Path $ProjectRoot $DemoFile

# Test results tracking
$Results = @{
    Passed = 0
    Failed = 0
    Skipped = 0
    Total = 0
}

$TestResults = @()

# =========================================================================
# Utility Functions
# =========================================================================

function Write-Header {
    param([string]$Title)
    Write-Host "`n" -NoNewline
    Write-Host "=" * 75 -ForegroundColor Cyan
    Write-Host "  $Title" -ForegroundColor Cyan
    Write-Host "=" * 75 -ForegroundColor Cyan
}

function Write-SubHeader {
    param([string]$Title)
    Write-Host "`n  [$Title]" -ForegroundColor Yellow
}

function Write-Pass {
    param([string]$Message)
    Write-Host "  [PASS] $Message" -ForegroundColor Green
    $Results.Passed++
}

function Write-Fail {
    param([string]$Message)
    Write-Host "  [FAIL] $Message" -ForegroundColor Red
    $Results.Failed++
}

function Write-Skip {
    param([string]$Message)
    Write-Host "  [SKIP] $Message" -ForegroundColor Gray
    $Results.Skipped++
}

function Write-Info {
    param([string]$Message)
    Write-Host "  $Message" -ForegroundColor Gray
}

function Test-FileExists {
    param([string]$Path, [string]$Description)
    if (-not (Test-Path $Path)) {
        Write-Fail "$Description not found at: $Path"
        return $false
    }
    Write-Info "$Description found: $Path"
    return $true
}

function Invoke-SimpleCommand {
    param(
        [string[]]$Arguments,
        [int]$TimeoutSeconds = 10,
        [bool]$CaptureOutput = $true
    )

    try {
        if ($CaptureOutput) {
            $process = & $SimpleBin @Arguments 2>&1
            return @{
                Success = $?
                Output = $process
                ExitCode = $LASTEXITCODE
            }
        } else {
            & $SimpleBin @Arguments
            return @{
                Success = $?
                ExitCode = $LASTEXITCODE
            }
        }
    }
    catch {
        return @{
            Success = $false
            Error = $_.Exception.Message
            ExitCode = -1
        }
    }
}

function Start-ProcessTimeout {
    param(
        [string]$FilePath,
        [string[]]$ArgumentList,
        [int]$TimeoutSeconds = 5
    )

    try {
        $process = Start-Process -FilePath $FilePath -ArgumentList $ArgumentList `
                                 -PassThru -ErrorAction Stop
        $result = Wait-Process -InputObject $process -Timeout $TimeoutSeconds `
                               -ErrorAction SilentlyContinue

        if ($null -eq $result) {
            # Process still running, kill it
            Stop-Process -InputObject $process -Force -ErrorAction SilentlyContinue | Out-Null
            return @{ TimedOut = $true; Process = $process }
        }

        return @{ TimedOut = $false; Process = $process; ExitCode = $process.ExitCode }
    }
    catch {
        return @{ Success = $false; Error = $_.Exception.Message }
    }
}

function Test-HttpEndpoint {
    param(
        [string]$Url,
        [int]$TimeoutMs = 5000
    )

    try {
        $response = Invoke-WebRequest -Uri $Url -TimeoutSec ($TimeoutMs / 1000) `
                                      -ErrorAction Stop
        return @{ Success = $true; StatusCode = $response.StatusCode }
    }
    catch {
        return @{ Success = $false; Error = $_.Exception.Message }
    }
}

function Get-ProcessByPort {
    param([int]$Port)

    try {
        $netstat = netstat -ano | Select-String ":$Port\s+"
        if ($netstat) {
            $parts = $netstat -split '\s+'
            return $parts[-1]  # PID is last element
        }
        return $null
    }
    catch {
        return $null
    }
}

function Cleanup-ProcessByName {
    param([string]$ProcessName)

    try {
        Get-Process -Name $ProcessName -ErrorAction SilentlyContinue |
            Stop-Process -Force -ErrorAction SilentlyContinue
    }
    catch {}
}

function Test-DependencyExists {
    param([string]$Command, [string]$FriendlyName)

    try {
        $null = & where.exe $Command
        return $true
    }
    catch {
        return $false
    }
}

# =========================================================================
# Pre-flight Checks
# =========================================================================

function Invoke-PrefightChecks {
    Write-Header "PREFLIGHT CHECKS"

    $allGood = $true

    # Check Simple binary
    if (-not (Test-FileExists $SimpleBin "Simple binary")) {
        $allGood = $false
    }

    # Check demo file
    if (-not (Test-FileExists $DemoFullPath "Demo UI file")) {
        $allGood = $false
    }

    if (-not $allGood) {
        Write-Host "`n  Cannot continue without required files.`n" -ForegroundColor Red
        exit 1
    }

    Write-Host "`n  All checks passed. Starting tests...`n" -ForegroundColor Green
}

# =========================================================================
# Test 1: TUI Backend (Headless)
# =========================================================================

function Test-TuiBackend {
    Write-SubHeader "Test 1: TUI Backend (Headless)"
    $Results.Total++

    # Test with simple echo input
    Write-Info "Running TUI with auto-quit input..."

    $output = "quit`n" | & $SimpleBin ui tui $DemoFullPath 2>&1

    if ($LASTEXITCODE -eq 0) {
        Write-Pass "TUI backend executed successfully"
        Write-Info "Output lines: $($output.Count)"
        return $true
    } else {
        Write-Fail "TUI backend exited with code $LASTEXITCODE"
        Write-Info "Last output: $(if ($output) { $output[-1] } else { '(no output)' })"
        return $false
    }
}

# =========================================================================
# Test 2: Web Backend
# =========================================================================

function Test-WebBackend {
    Write-SubHeader "Test 2: Web Backend"
    $Results.Total++

    Write-Info "Starting web server on port $WebPort..."

    # Start web server in background
    $webProcess = Start-Process -FilePath $SimpleBin `
                                -ArgumentList "ui", "web", $DemoFullPath, "--port", $WebPort `
                                -PassThru -ErrorAction Stop

    # Give server time to start
    Write-Info "Waiting 2 seconds for server startup..."
    Start-Sleep -Seconds 2

    # Test endpoint
    $url = "http://localhost:$WebPort/"
    Write-Info "Testing endpoint: $url"

    $webTest = Test-HttpEndpoint -Url $url -TimeoutMs 5000

    # Cleanup
    Write-Info "Stopping web server..."
    Stop-Process -InputObject $webProcess -Force -ErrorAction SilentlyContinue | Out-Null

    if ($webTest.Success) {
        Write-Pass "Web server responds with status $($webTest.StatusCode)"
        return $true
    } else {
        Write-Fail "Web server not responding: $($webTest.Error)"
        return $false
    }
}

# =========================================================================
# Test 3: Electron Backend
# =========================================================================

function Test-ElectronBackend {
    Write-SubHeader "Test 3: Electron Backend"
    $Results.Total++

    # Check if electron is available
    if (-not (Test-DependencyExists "electron" "Electron")) {
        Write-Skip "Electron not found in PATH. Install with: npm install -g electron"
        Write-Info "More info: https://www.electronjs.org/docs/latest/tutorial/installation"
        return $null
    }

    Write-Info "Electron found. Checking electron shell..."
    $electronShellPath = Join-Path $ProjectRoot $ElectronPath

    if (-not (Test-Path $electronShellPath)) {
        Write-Skip "Electron shell not found at: $electronShellPath"
        return $null
    }

    Write-Info "Attempting to launch Electron app..."

    # Try to start Electron (will auto-close after timeout)
    $result = Start-ProcessTimeout -FilePath "electron" `
                                   -ArgumentList @($electronShellPath, $SimpleBin, $DemoFullPath) `
                                   -TimeoutSeconds 5

    if ($result.TimedOut) {
        Write-Pass "Electron shell launched successfully (timed out as expected)"
        return $true
    } elseif ($result.ExitCode -eq 0) {
        Write-Pass "Electron shell completed"
        return $true
    } else {
        Write-Fail "Electron exited with code $($result.ExitCode)"
        return $false
    }
}

# =========================================================================
# Test 4: Tauri Backend
# =========================================================================

function Test-TauriBackend {
    Write-SubHeader "Test 4: Tauri Backend"
    $Results.Total++

    Write-Info "Checking Tauri shell build..."
    $tauriShellExe = Join-Path $ProjectRoot $TauriCargoPath "target\release\simple-tauri-shell.exe"

    # If shell exists, try to run it
    if (Test-Path $tauriShellExe) {
        Write-Info "Tauri shell found at: $tauriShellExe"
        Write-Info "Attempting to launch Tauri app..."

        $result = Start-ProcessTimeout -FilePath $tauriShellExe `
                                       -ArgumentList @($SimpleBin, $DemoFullPath) `
                                       -TimeoutSeconds 5

        if ($result.TimedOut) {
            Write-Pass "Tauri shell launched successfully (timed out as expected)"
            return $true
        } elseif ($result.ExitCode -eq 0) {
            Write-Pass "Tauri shell completed"
            return $true
        } else {
            Write-Fail "Tauri shell exited with code $($result.ExitCode)"
            return $false
        }
    }

    # Shell not built, check if cargo is available
    Write-Info "Tauri shell not built. Checking if Rust/cargo is available..."

    if (-not (Test-DependencyExists "cargo" "Cargo")) {
        Write-Skip "Cargo not found. Install Rust from: https://www.rust-lang.org/tools/install"
        Write-Info "To build Tauri shell after installing Rust:"
        Write-Info "  cd $TauriCargoPath"
        Write-Info "  cargo build --release"
        return $null
    }

    Write-Info "Cargo found. Checking if Tauri code compiles..."

    Push-Location (Join-Path $ProjectRoot $TauriCargoPath)
    try {
        $output = & cargo check 2>&1

        if ($LASTEXITCODE -eq 0) {
            Write-Pass "Tauri code compiles successfully"
            Write-Info "To build and run: cargo build --release"
            return $true
        } else {
            Write-Fail "Tauri code has compilation errors"
            Write-Info "Error output: $(($output | Select-Object -Last 3) -join ' | ')"
            return $false
        }
    }
    catch {
        Write-Fail "Error running cargo check: $($_.Exception.Message)"
        return $false
    }
    finally {
        Pop-Location
    }
}

# =========================================================================
# Test 5: UI File Format Variations
# =========================================================================

function Test-UiFileVariations {
    Write-SubHeader "Test 5: UI File Format Variations"
    $Results.Total++

    Write-Info "Creating temporary test file with LF line endings..."

    $tempFile = [System.IO.Path]::GetTempFileName()
    $tempFile = [System.IO.Path]::ChangeExtension($tempFile, ".ui.sdn")

    try {
        # Write test file with LF only (Unix style)
        $testContent = @"
app:
    title: "Format Test"
    theme: dark
layout:
    type: vbox
    id: root
    children:
        msg:
            type: text
            id: msg
            content: "Line ending test"
        status:
            type: statusbar
            id: status
            left: "Test"
            right: "LF"
"@

        [System.IO.File]::WriteAllText($tempFile, $testContent, [System.Text.Encoding]::UTF8)

        Write-Info "Testing with LF line endings..."
        $output = "quit`n" | & $SimpleBin ui tui $tempFile 2>&1

        if ($LASTEXITCODE -eq 0) {
            Write-Pass "TUI handles LF line endings correctly"
            return $true
        } else {
            Write-Fail "TUI failed with LF line endings (exit code: $LASTEXITCODE)"
            return $false
        }
    }
    catch {
        Write-Fail "Error testing file format: $($_.Exception.Message)"
        return $false
    }
    finally {
        Remove-Item $tempFile -Force -ErrorAction SilentlyContinue
    }
}

# =========================================================================
# Main Execution
# =========================================================================

function Main {
    Write-Host ""
    Write-Host "╔" + ("═" * 73) + "╗" -ForegroundColor Cyan
    Write-Host "║" + (" " * 15) + "Simple UI Backend Test Suite" + (" " * 30) + "║" -ForegroundColor Cyan
    Write-Host "╚" + ("═" * 73) + "╝" -ForegroundColor Cyan
    Write-Host ""

    Write-Host "  Project Root: $ProjectRoot" -ForegroundColor Gray
    Write-Host "  Simple Binary: $SimpleBin" -ForegroundColor Gray
    Write-Host "  Demo File: $DemoFullPath" -ForegroundColor Gray
    Write-Host "  Web Port: $WebPort" -ForegroundColor Gray
    Write-Host ""

    # Preflight checks
    Invoke-PrefightChecks

    # Run all tests
    $testsPassed = 0
    $testsFailed = 0

    # Test 1: TUI Backend
    if (Test-TuiBackend) { $testsPassed++ } else { $testsFailed++ }

    # Test 2: Web Backend
    if (Test-WebBackend) { $testsPassed++ } else { $testsFailed++ }

    # Test 3: Electron Backend
    $electronResult = Test-ElectronBackend
    if ($electronResult -eq $true) { $testsPassed++ }
    elseif ($electronResult -eq $false) { $testsFailed++ }

    # Test 4: Tauri Backend
    $tauriResult = Test-TauriBackend
    if ($tauriResult -eq $true) { $testsPassed++ }
    elseif ($tauriResult -eq $false) { $testsFailed++ }

    # Test 5: File format variations
    if (Test-UiFileVariations) { $testsPassed++ } else { $testsFailed++ }

    # Summary
    Write-Header "TEST SUMMARY"
    Write-Host "  Passed:  $($Results.Passed)" -ForegroundColor Green
    Write-Host "  Failed:  $($Results.Failed)" -ForegroundColor $(if ($Results.Failed -gt 0) { "Red" } else { "Green" })
    Write-Host "  Skipped: $($Results.Skipped)" -ForegroundColor Gray
    Write-Host "  Total:   $($Results.Total)"
    Write-Host ""

    # Exit code
    if ($Results.Failed -gt 0) {
        Write-Host "  Result: SOME TESTS FAILED" -ForegroundColor Red
        Write-Host ""
        exit 1
    } else {
        Write-Host "  Result: ALL TESTS PASSED" -ForegroundColor Green
        Write-Host ""
        exit 0
    }
}

# Run main
Main
