param(
    [string]$BuildDir = "build\tmp\windows_native_mdi_evidence",
    [string]$ReportPath = "",
    [string]$SimpleBin = "",
    [string]$Entry = "src/os/hosted/hosted_win32_mdi_probe.spl",
    [string]$Title = "SimpleOS Win32 Hosted MDI Probe",
    [int]$TimeoutSecs = 45
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)

function Resolve-RepoPath([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path)) {
        return $path
    }
    if ([System.IO.Path]::IsPathRooted($path)) {
        return $path
    }
    return Join-Path $repoRoot $path
}

$BuildDir = Resolve-RepoPath $BuildDir
if ([string]::IsNullOrWhiteSpace($ReportPath)) {
    $ReportPath = Join-Path $BuildDir "report.md"
}
$ReportPath = Resolve-RepoPath $ReportPath
$Entry = Resolve-RepoPath $Entry

$EvidencePath = Join-Path $BuildDir "evidence.env"
$ProofPath = Join-Path $BuildDir "windows_native_mdi_proof.env"
$ScreenshotPath = Join-Path $BuildDir "windows_native_mdi.png"
$LogPath = Join-Path $BuildDir "windows_native_mdi.log"
$ScreenshotSemanticLog = Join-Path $BuildDir "windows_native_mdi_screenshot_semantic.log"
$Win32ScreenshotSemanticLog = Join-Path $BuildDir "win32_native_mdi_screenshot_semantic.log"

function Add-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
}

function Write-Rows([string]$path, $rows) {
    $dir = Split-Path -Parent $path
    if (-not [string]::IsNullOrWhiteSpace($dir)) {
        New-Item -ItemType Directory -Force -Path $dir | Out-Null
    }
    Set-Content -LiteralPath $path -Value $rows -Encoding utf8
}

function Write-Report {
    $report = New-Object System.Collections.Generic.List[string]
    $report.Add("# Windows Native MDI Evidence") | Out-Null
    $report.Add("") | Out-Null
    $report.Add("## Raw Evidence") | Out-Null
    $report.Add("") | Out-Null
    if (Test-Path -LiteralPath $EvidencePath) {
        foreach ($line in Get-Content -LiteralPath $EvidencePath) { $report.Add("- $line") | Out-Null }
    }
    if (Test-Path -LiteralPath $ProofPath) {
        $report.Add("") | Out-Null
        $report.Add("## Probe Proof") | Out-Null
        foreach ($line in Get-Content -LiteralPath $ProofPath) { $report.Add("- $line") | Out-Null }
    }
    Write-Rows $ReportPath $report
}

function Emit-And-Exit($status, $reason, $exitCode, $windowFound) {
    $rows = New-Object System.Collections.Generic.List[string]
    Add-Row $rows "windows_native_mdi_evidence_status" $status
    Add-Row $rows "windows_native_mdi_evidence_reason" $reason
    Add-Row $rows "windows_native_mdi_evidence_simple_bin" "$script:ResolvedSimpleBin"
    Add-Row $rows "windows_native_mdi_evidence_simple_bin_source" "$script:SimpleBinSource"
    Add-Row $rows "windows_native_mdi_evidence_simple_bin_status" "$script:SimpleBinStatus"
    Add-Row $rows "windows_native_mdi_evidence_host_os" "$script:HostOs"
    Add-Row $rows "windows_native_mdi_evidence_window_found" "$windowFound"
    Add-Row $rows "windows_native_mdi_evidence_proof_path" $(if ($status -eq "skip") { "" } else { $ProofPath })
    Add-Row $rows "windows_native_mdi_evidence_screenshot_path" $(if ($status -eq "skip") { "" } else { $ScreenshotPath })
    Add-Row $rows "windows_native_mdi_evidence_log_path" $(if ($status -eq "skip") { "" } else { $LogPath })
    Add-Row $rows "windows_native_mdi_evidence_report_path" "$ReportPath"
    Write-Rows $EvidencePath $rows
    Write-Report
    Get-Content -LiteralPath $EvidencePath
    exit $exitCode
}

function Is-RustSeedSimple([string]$path) {
    return $path -match '(^|[\\/])src[\\/]compiler_rust[\\/]'
}

function Test-SimpleBinCandidate([string]$path) {
    $path = Resolve-RepoPath $path
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $false }
    try {
        return ((Get-Item -LiteralPath $path).Length -gt 0)
    } catch {
        return $false
    }
}

function Copy-CurrentDriverCandidate {
    foreach ($candidate in @(
        "src\compiler_rust\target\debug\simple.exe",
        "src\compiler_rust\target\bootstrap\simple.exe"
    )) {
        $candidatePath = Resolve-RepoPath $candidate
        if (Test-SimpleBinCandidate $candidatePath) {
            $driverDir = Join-Path $BuildDir "simple_driver_current"
            New-Item -ItemType Directory -Force -Path $driverDir | Out-Null
            $driverPath = Join-Path $driverDir "simple.exe"
            Copy-Item -LiteralPath $candidatePath -Destination $driverPath -Force
            if (Test-SimpleBinCandidate $driverPath) {
                $script:SimpleBinSource = "copied-current-driver:$candidate"
                $script:SimpleBinStatus = "pass"
                return $driverPath
            }
        }
    }
    return ""
}

function Resolve-SimpleBin {
    if (-not [string]::IsNullOrWhiteSpace($SimpleBin)) {
        $resolvedExplicit = Resolve-RepoPath $SimpleBin
        $script:SimpleBinSource = "explicit-env"
        if (Is-RustSeedSimple $resolvedExplicit) {
            $script:SimpleBinStatus = "forbidden"
            return $resolvedExplicit
        }
        if (-not (Test-SimpleBinCandidate $resolvedExplicit)) {
            $script:SimpleBinStatus = "invalid"
            return $resolvedExplicit
        }
        $script:SimpleBinStatus = "pass"
        return $resolvedExplicit
    }
    $copiedDriver = Copy-CurrentDriverCandidate
    if (-not [string]::IsNullOrWhiteSpace($copiedDriver)) {
        return $copiedDriver
    }
    $script:SimpleBinSource = "missing"
    $script:SimpleBinStatus = "missing"
    foreach ($candidate in @(
        "bin\release\simple.exe",
        "bin\release\x86_64-pc-windows-msvc\simple.exe",
        "build\bootstrap\stage3\simple.exe",
        "build\bootstrap\stage2\x86_64-pc-windows-msvc\simple.exe",
        "build\bootstrap\stage1\simple.exe"
    )) {
        $candidatePath = Resolve-RepoPath $candidate
        if (Test-SimpleBinCandidate $candidatePath) {
            $script:SimpleBinSource = "self-hosted:$candidate"
            $script:SimpleBinStatus = "pass"
            return $candidatePath
        }
    }
    return ""
}

function Read-Field([string]$path, [string]$key) {
    if (-not (Test-Path -LiteralPath $path)) { return "" }
    $prefix = "$key="
    foreach ($line in Get-Content -LiteralPath $path) {
        if ($line.StartsWith($prefix)) { return $line.Substring($prefix.Length) }
    }
    return ""
}

function Quote-ProcessArg([string]$arg) {
    if ($null -eq $arg) { return '""' }
    if ($arg -notmatch '[\s"]') { return $arg }
    $escaped = $arg.Replace('"', '\"')
    return '"' + $escaped + '"'
}

function Join-ProcessArgs([string[]]$arguments) {
    $quoted = New-Object System.Collections.Generic.List[string]
    foreach ($arg in $arguments) { $quoted.Add((Quote-ProcessArg $arg)) | Out-Null }
    return ($quoted -join " ")
}

function Require-Proof([string]$key, [string]$expected, [string]$reason) {
    $actual = Read-Field $ProofPath $key
    if ($actual -ne $expected) { Emit-And-Exit "fail" $reason 1 "true" }
}

function Invoke-Simple([string[]]$arguments, [string]$stdoutPath, [string]$stderrPath, [int]$timeoutSecs) {
    $startInfo = New-Object System.Diagnostics.ProcessStartInfo
    $startInfo.FileName = (Resolve-Path -LiteralPath $script:ResolvedSimpleBin).Path
    $startInfo.Arguments = Join-ProcessArgs $arguments
    $startInfo.WorkingDirectory = $repoRoot
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $startInfo
    [void]$process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    if (-not $process.WaitForExit($timeoutSecs * 1000)) {
        try { $process.Kill($true) } catch { try { $process.Kill() } catch {} }
        Set-Content -LiteralPath $stdoutPath -Value $stdoutTask.Result -Encoding utf8
        Set-Content -LiteralPath $stderrPath -Value ($stderrTask.Result + "`ntimed out") -Encoding utf8
        return 124
    }
    Set-Content -LiteralPath $stdoutPath -Value $stdoutTask.Result -Encoding utf8
    Set-Content -LiteralPath $stderrPath -Value $stderrTask.Result -Encoding utf8
    return $process.ExitCode
}

function Flush-ProbeLog {
    if ($probe) {
        try { Set-Content -LiteralPath $LogPath -Value $probeStdoutTask.Result -Encoding utf8 } catch {}
        try { Add-Content -LiteralPath $LogPath -Value $probeStderrTask.Result -Encoding utf8 } catch {}
    }
}

New-Item -ItemType Directory -Force -Path $BuildDir | Out-Null
Remove-Item -LiteralPath $EvidencePath, $ProofPath, $ScreenshotPath, $LogPath, $ReportPath -Force -ErrorAction SilentlyContinue

$script:HostOs = if ($env:OS -eq "Windows_NT") { "windows" } else { "non-windows" }
$script:ResolvedSimpleBin = Resolve-SimpleBin

if ($script:SimpleBinStatus -eq "forbidden") { Emit-And-Exit "fail" "simple-bin-forbidden" 1 "false" }
if ($script:HostOs -ne "windows") { Emit-And-Exit "skip" "requires-windows" 0 "false" }
if ([string]::IsNullOrWhiteSpace($script:ResolvedSimpleBin) -or -not (Test-Path -LiteralPath $script:ResolvedSimpleBin)) {
    Emit-And-Exit "fail" "missing-simple-bin" 1 "false"
}
if (-not (Test-Path -LiteralPath $Entry)) { Emit-And-Exit "fail" "missing-entry" 1 "false" }
$ResolvedEntry = (Resolve-Path -LiteralPath $Entry).Path

$startInfo = New-Object System.Diagnostics.ProcessStartInfo
$startInfo.FileName = (Resolve-Path -LiteralPath $script:ResolvedSimpleBin).Path
$startInfo.Arguments = Join-ProcessArgs @($ResolvedEntry, "--interpret")
$startInfo.WorkingDirectory = $repoRoot
$startInfo.RedirectStandardOutput = $true
$startInfo.RedirectStandardError = $true
$startInfo.UseShellExecute = $false
$startInfo.CreateNoWindow = $true
$startInfo.Environment["SIMPLE_HOME"] = $repoRoot
$startInfo.Environment["SIMPLE_WIN32_MDI_PROOF_PATH"] = $ProofPath
$startInfo.Environment["SIMPLE_WIN32_MDI_HOLD_MS"] = "12000"
$probe = New-Object System.Diagnostics.Process
$probe.StartInfo = $startInfo
[void]$probe.Start()
$probeStdoutTask = $probe.StandardOutput.ReadToEndAsync()
$probeStderrTask = $probe.StandardError.ReadToEndAsync()

try {
    Start-Sleep -Milliseconds 1500
    if ($probe.HasExited -and -not (Test-Path -LiteralPath $ProofPath)) {
        Flush-ProbeLog
        Emit-And-Exit "fail" "simple-source-launch-failed" 1 "false"
    }

    $deadline = (Get-Date).AddSeconds($TimeoutSecs)
    $windowFound = $false
    while ((Get-Date) -lt $deadline) {
        $process = Get-Process | Where-Object { $_.MainWindowTitle -eq $Title } | Select-Object -First 1
        if ($process) {
            $windowFound = $true
            break
        }
        Start-Sleep -Milliseconds 500
    }
    if (-not $windowFound) { Emit-And-Exit "fail" "window-not-found" 1 "false" }

    $deadline = (Get-Date).AddSeconds($TimeoutSecs)
    while ((Get-Date) -lt $deadline) {
        if (Test-Path -LiteralPath $ProofPath) {
            if ((Get-Item -LiteralPath $ProofPath).Length -gt 0) { break }
        }
        Start-Sleep -Milliseconds 500
    }
    if (-not (Test-Path -LiteralPath $ProofPath)) { Emit-And-Exit "fail" "missing-proof" 1 "true" }

    Add-Type -AssemblyName System.Windows.Forms,System.Drawing
    $vs = [Windows.Forms.SystemInformation]::VirtualScreen
    $bmp = New-Object Drawing.Bitmap($vs.Width, $vs.Height)
    $g = [Drawing.Graphics]::FromImage($bmp)
    $g.CopyFromScreen($vs.Left, $vs.Top, 0, 0, $bmp.Size)
    $bmp.Save((Resolve-Path -LiteralPath $BuildDir).Path + "\windows_native_mdi.png")
    $g.Dispose()
    $bmp.Dispose()
    if (-not (Test-Path -LiteralPath $ScreenshotPath)) { Emit-And-Exit "fail" "missing-screenshot" 1 "true" }

    Require-Proof "status" "pass" "probe-status-not-pass"
    Require-Proof "backend" "win32-native" "probe-backend-mismatch"
    Require-Proof "drag_moved" "true" "probe-drag-not-proven"
    Require-Proof "focus_cycle_changed" "true" "probe-focus-cycle-not-proven"
    Require-Proof "titlebar_widget_markup_present" "true" "probe-titlebar-widget-missing"
    Require-Proof "titlebar_input_markup_present" "true" "probe-titlebar-input-missing"
    Require-Proof "body_button_markup_present" "true" "probe-body-button-missing"
    Require-Proof "body_input_markup_present" "true" "probe-body-input-missing"
    Require-Proof "titlebar_css_present" "true" "probe-titlebar-css-missing"
    Require-Proof "rendered_titlebar_css_applied" "true" "probe-rendered-titlebar-css-missing"
    Require-Proof "minimized_after_restore" "0" "probe-restore-not-proven"

    $semanticErr = Join-Path $BuildDir "windows_native_mdi_screenshot_semantic.err"
    $win32SemanticErr = Join-Path $BuildDir "win32_native_mdi_screenshot_semantic.err"
    try {
        $shot = [Drawing.Bitmap]::FromFile((Resolve-Path -LiteralPath $ScreenshotPath).Path)
        $unique = New-Object 'System.Collections.Generic.HashSet[int]'
        $titlebarCssPixels = 0
        $darkPixels = 0
        $accentPixels = 0
        for ($y = 0; $y -lt $shot.Height; $y += 1) {
            for ($x = 0; $x -lt $shot.Width; $x += 1) {
                $p = $shot.GetPixel($x, $y)
                $argb = $p.ToArgb()
                [void]$unique.Add($argb)
                if (($p.R -eq 0x12 -and $p.G -eq 0x3A -and $p.B -eq 0x34) -or
                    ($p.R -eq 0x34 -and $p.G -eq 0xD3 -and $p.B -eq 0x99)) {
                    $titlebarCssPixels += 1
                }
                if ($p.R -lt 45 -and $p.G -lt 55 -and $p.B -lt 65) {
                    $darkPixels += 1
                }
                if (($p.R -gt 190 -and $p.G -lt 100 -and $p.B -lt 100) -or
                    ($p.R -gt 180 -and $p.G -gt 120 -and $p.B -lt 80) -or
                    ($p.G -gt 140 -and $p.R -lt 100 -and $p.B -lt 120) -or
                    ($p.B -gt 140 -and $p.R -lt 170 -and $p.G -lt 200)) {
                    $accentPixels += 1
                }
            }
        }
        if ($shot.Width -lt 300 -or $shot.Height -lt 300) {
            "screenshot dimensions invalid: $($shot.Width)x$($shot.Height)" | Set-Content -LiteralPath $semanticErr
            Emit-And-Exit "fail" "screenshot-semantic-validation-failed" 1 "true"
        }
        if ($unique.Count -lt 16) {
            "screenshot appears blank: unique_colors=$($unique.Count)" | Set-Content -LiteralPath $semanticErr
            Emit-And-Exit "fail" "screenshot-semantic-validation-failed" 1 "true"
        }
        if ($titlebarCssPixels -lt 20 -or $darkPixels -lt 2000 -or $accentPixels -lt 100) {
            "win32 screenshot semantic failed: titlebar_css_pixels=$titlebarCssPixels dark_pixels=$darkPixels accent_pixels=$accentPixels" | Set-Content -LiteralPath $win32SemanticErr
            Emit-And-Exit "fail" "win32-screenshot-semantic-validation-failed" 1 "true"
        }
        "windows_native_mdi_screenshot=pass width=$($shot.Width) height=$($shot.Height) unique_colors=$($unique.Count)" | Set-Content -LiteralPath $ScreenshotSemanticLog
        "win32_native_mdi_screenshot_semantic=pass width=$($shot.Width) height=$($shot.Height) titlebar_css_pixels=$titlebarCssPixels dark_pixels=$darkPixels accent_pixels=$accentPixels" | Set-Content -LiteralPath $Win32ScreenshotSemanticLog
        $shot.Dispose()
    } catch {
        $_.Exception.Message | Set-Content -LiteralPath $semanticErr
        Emit-And-Exit "fail" "screenshot-semantic-validation-failed" 1 "true"
    }

    $titlebarCssPixels = ""
    foreach ($line in Get-Content -LiteralPath $Win32ScreenshotSemanticLog) {
        if ($line -match 'titlebar_css_pixels=([0-9]+)') {
            $titlebarCssPixels = $Matches[1]
            break
        }
    }
    if ([string]::IsNullOrWhiteSpace($titlebarCssPixels)) { Emit-And-Exit "fail" "screenshot-titlebar-css-metric-missing" 1 "true" }
    $renderedTitlebarCssPixels = Read-Field $ProofPath "rendered_titlebar_css_pixels"
    if ([string]::IsNullOrWhiteSpace($renderedTitlebarCssPixels)) { Emit-And-Exit "fail" "probe-rendered-titlebar-css-metric-missing" 1 "true" }

    $rows = New-Object System.Collections.Generic.List[string]
    Add-Row $rows "windows_native_mdi_evidence_status" "pass"
    Add-Row $rows "windows_native_mdi_evidence_reason" "pass"
    Add-Row $rows "windows_native_mdi_evidence_simple_bin" "$script:ResolvedSimpleBin"
    Add-Row $rows "windows_native_mdi_evidence_simple_bin_source" "$script:SimpleBinSource"
    Add-Row $rows "windows_native_mdi_evidence_simple_bin_status" "$script:SimpleBinStatus"
    Add-Row $rows "windows_native_mdi_evidence_host_os" "windows"
    Add-Row $rows "windows_native_mdi_evidence_window_found" "true"
    Add-Row $rows "windows_native_mdi_evidence_window_title" "$Title"
    Add-Row $rows "windows_native_mdi_evidence_titlebar_css_pixels" "$titlebarCssPixels"
    Add-Row $rows "windows_native_mdi_evidence_rendered_titlebar_css_pixels" "$renderedTitlebarCssPixels"
    Add-Row $rows "windows_native_mdi_evidence_proof_path" "$ProofPath"
    Add-Row $rows "windows_native_mdi_evidence_screenshot_path" "$ScreenshotPath"
    Add-Row $rows "windows_native_mdi_evidence_log_path" "$LogPath"
    Add-Row $rows "windows_native_mdi_evidence_report_path" "$ReportPath"
    Write-Rows $EvidencePath $rows
    Write-Report
    Get-Content -LiteralPath $EvidencePath
    exit 0
} finally {
    if ($probe -and -not $probe.HasExited) {
        try { $probe.Kill($true) } catch { try { $probe.Kill() } catch {} }
    }
    Flush-ProbeLog
}
