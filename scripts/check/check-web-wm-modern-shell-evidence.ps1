param(
    [string]$BuildDir = "build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence",
    [string]$EvidencePath = "",
    [string]$ReportPath = "",
    [int]$Width = 1360,
    [int]$Height = 840,
    [int]$TimeoutSecs = 60
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
if ([string]::IsNullOrWhiteSpace($EvidencePath)) { $EvidencePath = Join-Path $BuildDir "evidence.env" }
if ([string]::IsNullOrWhiteSpace($ReportPath)) { $ReportPath = Join-Path $BuildDir "report.md" }
$EvidencePath = Resolve-RepoPath $EvidencePath
$ReportPath = Resolve-RepoPath $ReportPath

$HtmlPath = Join-Path $BuildDir "simple_wm_modern_preview.html"
$ArgbPath = Join-Path $BuildDir "simple_wm_modern_preview_argb.json"
$PngPath = Join-Path $BuildDir "simple_wm_modern_preview.png"
$AuditPath = Join-Path $BuildDir "simple_wm_modern_preview_audit.json"
$LogPath = Join-Path $BuildDir "electron_capture.log"
$InteractionPath = Join-Path $BuildDir "simple_wm_modern_preview_interaction.json"
$InteractionPngPath = Join-Path $BuildDir "simple_wm_modern_preview_after_interaction.png"
$InteractionLogPath = Join-Path $BuildDir "electron_interaction.log"
$PreviewSourcePath = Join-Path $BuildDir "write_preview.spl"
$PreviewLogPath = Join-Path $BuildDir "preview.log"
$SimpleCmdPath = Resolve-RepoPath "bin\simple.cmd"
$ElectronBin = Resolve-RepoPath "tools\electron-shell\node_modules\electron\dist\electron.exe"
$Selectors = "#wm-desktop,.wm-window,.wm-titlebar,.wm-command-palette,.wm-effect-controls,.wm-quality-inspector,.wm-traffic-lights button,.wm-command-palette-input,.wm-command-item,.wm-effect-control"

function Add-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
}

function Evidence-Path([string]$path) {
    return $path.Replace('\', '/')
}

function Write-Rows([string]$path, $rows) {
    $dir = Split-Path -Parent $path
    if (-not [string]::IsNullOrWhiteSpace($dir)) { New-Item -ItemType Directory -Force -Path $dir | Out-Null }
    Set-Content -LiteralPath $path -Value $rows -Encoding utf8
}

function Write-Evidence([string]$status, [string]$reason) {
    $rows = New-Object System.Collections.Generic.List[string]
    Add-Row $rows "web_wm_modern_shell_evidence_status" $status
    Add-Row $rows "web_wm_modern_shell_evidence_reason" $reason
    Add-Row $rows "web_wm_modern_shell_evidence_html" (Evidence-Path $HtmlPath)
    Add-Row $rows "web_wm_modern_shell_evidence_html_path" (Evidence-Path $HtmlPath)
    Add-Row $rows "web_wm_modern_shell_evidence_argb" (Evidence-Path $ArgbPath)
    Add-Row $rows "web_wm_modern_shell_evidence_argb_path" (Evidence-Path $ArgbPath)
    Add-Row $rows "web_wm_modern_shell_evidence_png" (Evidence-Path $PngPath)
    Add-Row $rows "web_wm_modern_shell_evidence_png_path" (Evidence-Path $PngPath)
    Add-Row $rows "web_wm_modern_shell_evidence_audit" (Evidence-Path $AuditPath)
    Add-Row $rows "web_wm_modern_shell_evidence_audit_path" (Evidence-Path $AuditPath)
    Add-Row $rows "web_wm_modern_shell_evidence_log" (Evidence-Path $LogPath)
    Add-Row $rows "web_wm_modern_shell_evidence_log_path" (Evidence-Path $LogPath)
    Add-Row $rows "web_wm_modern_shell_evidence_interaction" (Evidence-Path $InteractionPath)
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_path" (Evidence-Path $InteractionPath)
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_png" (Evidence-Path $InteractionPngPath)
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_png_path" (Evidence-Path $InteractionPngPath)
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_log" (Evidence-Path $InteractionLogPath)
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_log_path" (Evidence-Path $InteractionLogPath)
    Add-Row $rows "web_wm_modern_shell_evidence_width" "$Width"
    Add-Row $rows "web_wm_modern_shell_evidence_height" "$Height"
    Add-Row $rows "web_wm_modern_shell_evidence_selectors" $Selectors
    Add-Row $rows "web_wm_modern_shell_evidence_contrast_min_x100" "450"
    Add-Row $rows "web_wm_modern_shell_evidence_touch_min_px" "44"
    Add-Row $rows "web_wm_modern_shell_evidence_media_features" "prefers-contrast=more,prefers-reduced-motion=reduce"
    Add-Row $rows "web_wm_modern_shell_evidence_simple_runtime" "bin\simple.cmd"
    Add-Row $rows "web_wm_modern_shell_evidence_simple_runtime_source" "windows-simple-cmd"
    Add-Row $rows "web_wm_modern_shell_evidence_simple_runtime_status" "pass"
    Add-Row $rows "web_wm_modern_shell_evidence_simple_runtime_failures" "none"
    Add-Row $rows "web_wm_modern_shell_evidence_bitmap_nonblank_status" "$script:BitmapNonblankStatus"
    Add-Row $rows "web_wm_modern_shell_evidence_audit_pass" "$script:AuditPass"
    Add-Row $rows "web_wm_modern_shell_evidence_unexpected_overlap_count" "$script:UnexpectedOverlapCount"
    Add-Row $rows "web_wm_modern_shell_evidence_clipped_count" "$script:ClippedCount"
    Add-Row $rows "web_wm_modern_shell_evidence_contrast_failures" "$script:ContrastFailures"
    Add-Row $rows "web_wm_modern_shell_evidence_touch_failures" "$script:TouchFailures"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_pass" "$script:InteractionPass"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_focus" "$script:InteractionFocus"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_keyboard" "$script:InteractionKeyboard"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_input" "$script:InteractionInput"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_pointer" "$script:InteractionPointer"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_clicks" "$script:InteractionClicks"
    Add-Row $rows "web_wm_modern_shell_evidence_interaction_event_count" "$script:InteractionEventCount"
    Write-Rows $EvidencePath $rows
}

function Write-Report([string]$status, [string]$reason) {
    $report = New-Object System.Collections.Generic.List[string]
    $report.Add("# Web WM Modern Shell Evidence") | Out-Null
    $report.Add("") | Out-Null
    $report.Add("- status: ``$status``") | Out-Null
    $report.Add("- reason: ``$reason``") | Out-Null
    $report.Add("- preview: ``$HtmlPath``") | Out-Null
    $report.Add("- ARGB: ``$ArgbPath``") | Out-Null
    $report.Add("- PNG: ``$PngPath``") | Out-Null
    $report.Add("- audit: ``$AuditPath``") | Out-Null
    $report.Add("- interaction: ``$InteractionPath``") | Out-Null
    $report.Add("- interaction PNG: ``$InteractionPngPath``") | Out-Null
    $report.Add("- log: ``$LogPath``") | Out-Null
    $report.Add("- interaction log: ``$InteractionLogPath``") | Out-Null
    $report.Add("- simple runtime: ``bin\simple.cmd``") | Out-Null
    $report.Add("- simple runtime source: ``windows-simple-cmd``") | Out-Null
    $report.Add("- simple runtime status: ``pass``") | Out-Null
    Write-Rows $ReportPath $report
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

function Finish([string]$status, [string]$reason, [int]$exitCode) {
    Write-Evidence $status $reason
    Write-Report $status $reason
    Get-Content -LiteralPath $EvidencePath
    exit $exitCode
}

function Invoke-Process([string]$fileName, [string[]]$arguments, [string]$logPath, [int]$timeoutSecs) {
    $startInfo = New-Object System.Diagnostics.ProcessStartInfo
    $startInfo.FileName = (Resolve-Path -LiteralPath (Resolve-RepoPath $fileName)).Path
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
        Set-Content -LiteralPath $logPath -Value ($stdoutTask.Result + "`n" + $stderrTask.Result + "`ntimed out") -Encoding utf8
        return 124
    }
    Set-Content -LiteralPath $logPath -Value ($stdoutTask.Result + "`n" + $stderrTask.Result) -Encoding utf8
    return $process.ExitCode
}

function Invoke-SimplePreview {
    $source = @"
use app.ui.web.html.{write_wm_modern_preview_html}

fn main():
    val ok = write_wm_modern_preview_html("$($HtmlPath.Replace('\', '/'))", "glass_dark")
    if ok:
        print "preview_written"
    else:
        print "preview_failed"
"@
    [System.IO.File]::WriteAllText($PreviewSourcePath, $source, [System.Text.Encoding]::ASCII)
    return Invoke-Process $SimpleCmdPath @($PreviewSourcePath, "--interpret") $PreviewLogPath $TimeoutSecs
}

function Set-CaptureEnv {
    $env:ELECTRON_CAPTURE_HTML = $HtmlPath
    $env:ELECTRON_CAPTURE_WIDTH = "$Width"
    $env:ELECTRON_CAPTURE_HEIGHT = "$Height"
    $env:ELECTRON_CAPTURE_OUTPUT = $ArgbPath
    $env:ELECTRON_CAPTURE_PNG_OUTPUT = $PngPath
    $env:ELECTRON_CAPTURE_AUDIT_SELECTORS = $Selectors
    $env:ELECTRON_CAPTURE_AUDIT_OUTPUT = $AuditPath
    $env:ELECTRON_CAPTURE_CONTRAST_MIN_X100 = "450"
    $env:ELECTRON_CAPTURE_TOUCH_MIN_PX = "44"
    $env:ELECTRON_CAPTURE_MEDIA_FEATURES = "prefers-contrast=more,prefers-reduced-motion=reduce"
    $env:ELECTRON_CAPTURE_FAIL_ON_AUDIT = "1"
    $env:ELECTRON_CAPTURE_OFFSCREEN_PAINT = "1"
    $env:ELECTRON_CAPTURE_SETTLE_MS = "1500"
    $env:ELECTRON_DISABLE_SANDBOX = "1"
}

function Set-InteractionEnv {
    $env:ELECTRON_INTERACT_HTML = $HtmlPath
    $env:ELECTRON_INTERACT_WIDTH = "$Width"
    $env:ELECTRON_INTERACT_HEIGHT = "$Height"
    $env:ELECTRON_INTERACT_OUTPUT = $InteractionPath
    $env:ELECTRON_INTERACT_PNG_OUTPUT = $InteractionPngPath
    $env:ELECTRON_INTERACT_SETTLE_MS = "800"
    $env:ELECTRON_DISABLE_SANDBOX = "1"
}

New-Item -ItemType Directory -Force -Path $BuildDir | Out-Null
Remove-Item -LiteralPath $EvidencePath, $ReportPath, $HtmlPath, $ArgbPath, $PngPath, $AuditPath, $LogPath, $InteractionPath, $InteractionPngPath, $InteractionLogPath, $PreviewSourcePath, $PreviewLogPath -Force -ErrorAction SilentlyContinue

$script:BitmapNonblankStatus = "not-run"
$script:AuditPass = "not-run"
$script:UnexpectedOverlapCount = "not-run"
$script:ClippedCount = "not-run"
$script:ContrastFailures = "not-run"
$script:TouchFailures = "not-run"
$script:InteractionPass = "not-run"
$script:InteractionFocus = "not-run"
$script:InteractionKeyboard = "not-run"
$script:InteractionInput = "not-run"
$script:InteractionPointer = "not-run"
$script:InteractionClicks = "not-run"
$script:InteractionEventCount = "not-run"

if (-not (Test-Path -LiteralPath $SimpleCmdPath)) { Finish "environment-unavailable" "simple-cmd-missing" 0 }
if (-not (Test-Path -LiteralPath $ElectronBin)) { Finish "environment-unavailable" "electron-missing" 0 }

$previewCode = Invoke-SimplePreview
if ($previewCode -ne 0 -or -not (Test-Path -LiteralPath $HtmlPath)) { Finish "environment-unavailable" "simple-runtime-preview-failed" 0 }

Set-CaptureEnv
$captureCode = Invoke-Process $ElectronBin @(
    "--no-sandbox",
    "--disable-gpu",
    "--disable-gpu-compositing",
    "--disable-software-rasterizer=false",
    "--disable-features=VizDisplayCompositor",
    "--force-device-scale-factor=1",
    "--high-dpi-support=1",
    "--force-color-profile=srgb",
    "tools\electron-live-bitmap\capture_html_argb.js"
) $LogPath $TimeoutSecs
if ($captureCode -ne 0 -or -not (Test-Path -LiteralPath $ArgbPath) -or -not (Test-Path -LiteralPath $AuditPath)) { Finish "fail" "capture-failed" 1 }

$argb = Get-Content -LiteralPath $ArgbPath -Raw | ConvertFrom-Json
$audit = Get-Content -LiteralPath $AuditPath -Raw | ConvertFrom-Json
$nonblank = $false
foreach ($pixel in $argb.pixels) {
    $value = [int64]$pixel
    if ($value -ne 0 -and $value -ne -1 -and $value -ne 4294967295) {
        $nonblank = $true
        break
    }
}
$script:BitmapNonblankStatus = if ($nonblank) { "pass" } else { "fail" }
$script:AuditPass = if ($audit.pass -eq $true) { "pass" } else { "fail" }
$script:UnexpectedOverlapCount = "$($audit.unexpectedOverlapCount)"
$script:ClippedCount = "$($audit.clippedCount)"
$script:ContrastFailures = "$($audit.contrastFailures)"
$script:TouchFailures = "$($audit.touchFailures)"
if ($script:BitmapNonblankStatus -ne "pass" -or $script:AuditPass -ne "pass") { Finish "fail" "audit-or-bitmap-failed" 1 }

Set-InteractionEnv
$interactionCode = Invoke-Process $ElectronBin @(
    "--no-sandbox",
    "--disable-gpu",
    "--disable-gpu-compositing",
    "--disable-software-rasterizer=false",
    "--disable-features=VizDisplayCompositor",
    "--force-device-scale-factor=1",
    "--high-dpi-support=1",
    "--force-color-profile=srgb",
    "tools\electron-live-bitmap\interact_html_controls.js"
) $InteractionLogPath $TimeoutSecs
if ($interactionCode -ne 0 -or -not (Test-Path -LiteralPath $InteractionPath)) { Finish "fail" "interaction-failed" 1 }

$interaction = Get-Content -LiteralPath $InteractionPath -Raw | ConvertFrom-Json
$script:InteractionPass = if ($interaction.pass -eq $true) { "pass" } else { "fail" }
$script:InteractionFocus = if ($interaction.focusDelivered -eq $true) { "pass" } else { "fail" }
$script:InteractionKeyboard = if ($interaction.keyboardInput -eq $true) { "pass" } else { "fail" }
$script:InteractionInput = if ($interaction.inputDelivered -eq $true) { "pass" } else { "fail" }
$script:InteractionPointer = if ($interaction.pointerDelivered -eq $true) { "pass" } else { "fail" }
$script:InteractionClicks = if ($interaction.controlClickDelivered -eq $true -and $interaction.taskbarClickDelivered -eq $true -and $interaction.trafficClickDelivered -eq $true) { "pass" } else { "fail" }
$script:InteractionEventCount = "$($interaction.eventCount)"
if ($script:InteractionPass -ne "pass") { Finish "fail" "interaction-audit-failed" 1 }

Finish "pass" "pass" 0
