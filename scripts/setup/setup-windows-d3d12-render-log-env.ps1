param(
    [ValidateSet("--check", "--refresh-directx", "--print-install")]
    [string]$Mode = "--check",
    [string]$BuildDir = "build\windows-d3d12-render-log-env",
    [string]$DirectxEvidencePath = "build\gui-web-2d-directx-env-windows\evidence.env",
    [int]$Width = 320,
    [int]$Height = 240,
    [int]$TimeoutSecs = 120,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$RemainingArgs = @()
)

$ErrorActionPreference = "Stop"

if ($RemainingArgs -contains "--print-install" -or $MyInvocation.Line -match '(^|\s)--print-install(\s|$)') {
    $Mode = "--print-install"
} elseif ($RemainingArgs -contains "--refresh-directx" -or $MyInvocation.Line -match '(^|\s)--refresh-directx(\s|$)') {
    $Mode = "--refresh-directx"
} elseif ($RemainingArgs -contains "--check" -or $MyInvocation.Line -match '(^|\s)--check(\s|$)') {
    $Mode = "--check"
}

function Write-Install {
    @"
Windows PowerShell:
  winget install --id Microsoft.PIX --accept-source-agreements --accept-package-agreements

Required completion evidence:
  - Native Simple D3D12 readback probe that emits windows_d3d12_native_readback_api=d3d12
  - Electron and Chrome D3D12-backed browser proof plus pairwise ARGB diffs
  - PIX .wpix or accepted GPU debugger artifact for strict capture mode

Diagnostics only:
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --gpu-capture
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-windows-d3d12-render-log-env.ps1 --check
"@
}

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

function Command-Source([string]$name) {
    $cmd = Get-Command $name -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    return ""
}

function Existing-Path([string[]]$paths) {
    foreach ($path in $paths) {
        if (-not [string]::IsNullOrWhiteSpace($path) -and (Test-Path -LiteralPath $path)) {
            return $path
        }
    }
    return ""
}

function Candidate-Path([string]$base, [string]$child) {
    if ([string]::IsNullOrWhiteSpace($base)) { return "" }
    return Join-Path $base $child
}

function Latest-PixTool {
    $pathTool = Command-Source "WinPix.exe"
    if ($pathTool -ne "") { return $pathTool }
    $pathTool = Command-Source "PIXWin.exe"
    if ($pathTool -ne "") { return $pathTool }
    $pixRoot = Candidate-Path $env:ProgramFiles "Microsoft PIX"
    if (-not [string]::IsNullOrWhiteSpace($pixRoot) -and (Test-Path -LiteralPath $pixRoot)) {
        $versions = Get-ChildItem -LiteralPath $pixRoot -Directory -ErrorAction SilentlyContinue |
            Sort-Object Name -Descending
        foreach ($version in $versions) {
            $candidate = Join-Path $version.FullName "WinPix.exe"
            if (Test-Path -LiteralPath $candidate) { return $candidate }
        }
    }
    return Existing-Path @(
        (Candidate-Path $env:ProgramFiles "Microsoft PIX\WinPix.exe"),
        (Candidate-Path ${env:ProgramFiles(x86)} "Microsoft PIX\WinPix.exe")
    )
}

function File-Status([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path)) { return "missing" }
    if (-not (Test-Path -LiteralPath $path)) { return "missing" }
    $item = Get-Item -LiteralPath $path
    if ($item.PSIsContainer) { return "not-regular" }
    if ($item.Length -le 0) { return "empty" }
    return "pass"
}

function Quote-Arg([string]$arg) {
    if ($arg -match '[\s"]') {
        return '"' + ($arg -replace '"', '\"') + '"'
    }
    return $arg
}

function Invoke-ProcessBound([string]$exe, [string[]]$arguments, [string]$stdoutPath, [string]$stderrPath, [int]$timeoutSecs) {
    $startInfo = New-Object System.Diagnostics.ProcessStartInfo
    $startInfo.FileName = $exe
    $startInfo.Arguments = ($arguments | ForEach-Object { Quote-Arg $_ }) -join " "
    $startInfo.WorkingDirectory = (Get-Location).Path
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

function Read-KeyValueFile([string]$path) {
    $map = @{}
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $map }
    Get-Content -LiteralPath $path | ForEach-Object {
        $line = $_.Trim()
        if ($line -eq "" -or $line.StartsWith("#")) { return }
        $idx = $line.IndexOf("=")
        if ($idx -le 0) { return }
        $map[$line.Substring(0, $idx)] = $line.Substring($idx + 1)
    }
    return $map
}

function Value-Or($map, [string[]]$keys, [string]$defaultValue = "") {
    foreach ($key in $keys) {
        if ($map.ContainsKey($key) -and "$($map[$key])" -ne "") { return "$($map[$key])" }
    }
    return $defaultValue
}

if ($Mode -eq "--print-install") {
    Write-Install
    exit 0
}

New-Item -ItemType Directory -Force -Path $BuildDir | Out-Null
$nativeEnv = Join-Path $BuildDir "windows-d3d12-native-readback.env"
$browserEnv = Join-Path $BuildDir "windows-d3d12-browser-backing.env"
$pixEnv = Join-Path $BuildDir "windows-d3d12-pix.env"
$compareEnv = Join-Path $BuildDir "evidence.env"
$reportPath = Join-Path $BuildDir "report.md"
$directxOut = Join-Path $BuildDir "directx-refresh.out"
$directxErr = Join-Path $BuildDir "directx-refresh.err"

if ($Mode -eq "--refresh-directx") {
    $ps = Command-Source "powershell.exe"
    $args = @(
        "-ExecutionPolicy", "Bypass",
        "-File", "scripts\setup\setup-gui-web-2d-directx-env.ps1",
        "--gpu-capture",
        "-BuildDir", (Join-Path $BuildDir "directx-diagnostic"),
        "-Width", "$Width",
        "-Height", "$Height",
        "-TimeoutSecs", "$TimeoutSecs"
    )
    $refreshCode = Invoke-ProcessBound $ps $args $directxOut $directxErr $TimeoutSecs
    $DirectxEvidencePath = Join-Path $BuildDir "directx-diagnostic\evidence.env"
} else {
    $refreshCode = -1
}

$directx = Read-KeyValueFile $DirectxEvidencePath
$directxStatus = Value-Or $directx @("gui_web_2d_directx_browser_backing_status", "gui_web_2d_directx_native_readback_gate_status", "gui_web_2d_directx_native_readback_status") "missing"
$directxNativeApi = Value-Or $directx @("directx_native_readback_api", "gui_web_2d_directx_native_readback_api", "gui_web_2d_directx_requested_angle", "gui_web_2d_directx_requested_api") "d3d11"
$directxCaptureStatus = Value-Or $directx @("gui_web_2d_directx_gpu_debugger_capture_status") "missing"
$directxEventStatus = Value-Or $directx @("gui_web_2d_directx_browser_event_status") "missing"
$directxStrictDiagnosticStatus = if ($directxStatus -eq "pass" -and $directxEventStatus -eq "pass" -and $directxCaptureStatus -eq "pass") { "pass" } else { "fail" }
$pixTool = Latest-PixTool
$dxcapTool = Command-Source "DXCap.exe"

$nativeRows = New-Object System.Collections.Generic.List[string]
Add-Row $nativeRows "windows_d3d12_native_readback_status" "unavailable"
Add-Row $nativeRows "windows_d3d12_native_readback_reason" "missing-native-d3d12-readback-probe"
Add-Row $nativeRows "windows_d3d12_native_readback_api" "missing"
Add-Row $nativeRows "windows_d3d12_native_readback_source" "missing"
Add-Row $nativeRows "windows_d3d12_native_readback_backend_handle" "0"
Add-Row $nativeRows "windows_d3d12_native_readback_expected_checksum" "0"
Add-Row $nativeRows "windows_d3d12_native_readback_actual_checksum" "-1"
Add-Row $nativeRows "windows_d3d12_native_readback_wrapper_gate_status" "fail"
Add-Row $nativeRows "windows_d3d12_native_readback_directx_diagnostic_env" "$DirectxEvidencePath"
Add-Row $nativeRows "windows_d3d12_native_readback_directx_diagnostic_status" "$directxStatus"
Add-Row $nativeRows "windows_d3d12_native_readback_directx_diagnostic_event_status" "$directxEventStatus"
Add-Row $nativeRows "windows_d3d12_native_readback_directx_strict_diagnostic_status" "$directxStrictDiagnosticStatus"
Add-Row $nativeRows "windows_d3d12_native_readback_directx_diagnostic_api" "$directxNativeApi"
Write-Rows $nativeEnv $nativeRows

$browserRows = New-Object System.Collections.Generic.List[string]
Add-Row $browserRows "windows_d3d12_electron_browser_backing_status" "unavailable"
Add-Row $browserRows "windows_d3d12_electron_browser_backing_reason" "missing-d3d12-browser-backing-probe"
Add-Row $browserRows "windows_d3d12_chrome_browser_backing_status" "unavailable"
Add-Row $browserRows "windows_d3d12_chrome_browser_backing_reason" "missing-d3d12-browser-backing-probe"
Add-Row $browserRows "windows_d3d12_browser_backing_status" "unavailable"
Add-Row $browserRows "windows_d3d12_browser_backing_reason" "missing-d3d12-browser-backing-probe"
Add-Row $browserRows "windows_d3d12_pixel_comparison_status" "missing"
Add-Row $browserRows "windows_d3d12_pixel_comparison_mode" "missing"
Add-Row $browserRows "windows_d3d12_electron_chrome_pairwise_diff_status" "missing"
Add-Row $browserRows "windows_d3d12_electron_simple_pairwise_diff_status" "missing"
Add-Row $browserRows "windows_d3d12_chrome_simple_pairwise_diff_status" "missing"
foreach ($source in @("simple", "chrome", "electron")) {
    Add-Row $browserRows "windows_d3d12_${source}_argb_width" "0"
    Add-Row $browserRows "windows_d3d12_${source}_argb_height" "0"
    Add-Row $browserRows "windows_d3d12_${source}_argb_nonblank_pixel_count" "0"
    Add-Row $browserRows "windows_d3d12_${source}_argb_checksum" "missing"
}
Add-Row $browserRows "windows_d3d12_browser_backing_directx_diagnostic_env" "$DirectxEvidencePath"
Add-Row $browserRows "windows_d3d12_browser_backing_directx_diagnostic_status" "$directxStatus"
Add-Row $browserRows "windows_d3d12_browser_backing_directx_diagnostic_event_status" "$directxEventStatus"
Add-Row $browserRows "windows_d3d12_browser_backing_directx_strict_diagnostic_status" "$directxStrictDiagnosticStatus"
Write-Rows $browserEnv $browserRows

$pixRows = New-Object System.Collections.Generic.List[string]
Add-Row $pixRows "windows_d3d12_pix_capture_status" "unavailable"
Add-Row $pixRows "windows_d3d12_pix_capture_reason" "missing-pix-d3d12-capture"
Add-Row $pixRows "windows_d3d12_pix_capture_tool" "$pixTool"
Add-Row $pixRows "windows_d3d12_pix_capture_artifact" ""
Add-Row $pixRows "windows_d3d12_pix_capture_artifact_magic" "missing"
Add-Row $pixRows "windows_d3d12_gpu_debugger_capture_status" "unavailable"
Add-Row $pixRows "windows_d3d12_gpu_debugger_capture_reason" "dxcap-d3d11-diagnostic-not-d3d12"
Add-Row $pixRows "windows_d3d12_gpu_debugger_capture_tool" "$dxcapTool"
Add-Row $pixRows "windows_d3d12_gpu_debugger_capture_artifact" ""
Add-Row $pixRows "windows_d3d12_gpu_debugger_directx_diagnostic_status" "$directxCaptureStatus"
Add-Row $pixRows "windows_d3d12_gpu_debugger_directx_diagnostic_event_status" "$directxEventStatus"
Add-Row $pixRows "windows_d3d12_gpu_debugger_directx_strict_diagnostic_status" "$directxStrictDiagnosticStatus"
Write-Rows $pixEnv $pixRows

$blocked = @(
    "windows-d3d12-native-readback",
    "browser-d3d12-backing",
    "pairwise-argb-diff",
    "argb-source-evidence",
    "pix-or-gpu-debugger"
)
$reason = "windows-d3d12-native-readback-unavailable;electron-d3d12-backing-unavailable;chrome-d3d12-backing-unavailable;browser-d3d12-backing-unavailable;pixel-comparison-missing;pairwise-diff-incomplete-or-fail;windows-d3d12-pix-or-gpu-debugger-unavailable"

$compareRows = New-Object System.Collections.Generic.List[string]
Add-Row $compareRows "windows_d3d12_render_log_compare_status" "fail"
Add-Row $compareRows "windows_d3d12_render_log_compare_reason" "$reason"
Add-Row $compareRows "windows_d3d12_render_log_compare_blocked_gate_count" "$($blocked.Count)"
Add-Row $compareRows "windows_d3d12_render_log_compare_blocked_gates" "$($blocked -join ',')"
Add-Row $compareRows "windows_d3d12_render_log_compare_native_readback_gate_status" "fail"
Add-Row $compareRows "windows_d3d12_render_log_compare_browser_backing_gate_status" "fail"
Add-Row $compareRows "windows_d3d12_render_log_compare_pairwise_gate_status" "fail"
Add-Row $compareRows "windows_d3d12_render_log_compare_argb_source_gate_status" "fail"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status" "fail"
Add-Row $compareRows "windows_d3d12_render_log_compare_required_api" "d3d12"
Add-Row $compareRows "windows_d3d12_render_log_compare_native_readback_env" "$nativeEnv"
Add-Row $compareRows "windows_d3d12_render_log_compare_native_readback_env_file_status" "$(File-Status $nativeEnv)"
Add-Row $compareRows "windows_d3d12_render_log_compare_browser_env" "$browserEnv"
Add-Row $compareRows "windows_d3d12_render_log_compare_browser_env_file_status" "$(File-Status $browserEnv)"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_env" "$pixEnv"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_env_file_status" "$(File-Status $pixEnv)"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_diagnostic_env" "$DirectxEvidencePath"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_diagnostic_env_file_status" "$(File-Status $DirectxEvidencePath)"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_diagnostic_status" "$directxStatus"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_diagnostic_event_status" "$directxEventStatus"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_diagnostic_gpu_capture_status" "$directxCaptureStatus"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_strict_diagnostic_status" "$directxStrictDiagnosticStatus"
Add-Row $compareRows "windows_d3d12_render_log_compare_directx_diagnostic_api" "$directxNativeApi"
Add-Row $compareRows "windows_d3d12_render_log_compare_pairwise_status" "missing"
Add-Row $compareRows "windows_d3d12_render_log_compare_argb_checksum_reason" "missing-argb-checksum"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_status" "unavailable"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_artifact" ""
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_artifact_file_status" "missing"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_artifact_magic" "missing"
Add-Row $compareRows "windows_d3d12_render_log_compare_pix_artifact_file_magic" "missing"
Add-Row $compareRows "windows_d3d12_render_log_compare_gpu_debugger_status" "unavailable"
Add-Row $compareRows "windows_d3d12_render_log_compare_gpu_debugger_artifact" ""
Add-Row $compareRows "windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status" "missing"
Add-Row $compareRows "windows_d3d12_render_log_compare_refresh_directx_exit_code" "$refreshCode"
Write-Rows $compareEnv $compareRows

$reportRows = @(
    "# Windows D3D12 Render Log Environment",
    "",
    "- status: fail",
    "- reason: $reason",
    "- native env: $nativeEnv",
    "- browser env: $browserEnv",
    "- pix env: $pixEnv",
    "- DirectX/D3D11 diagnostic env: $DirectxEvidencePath",
    "",
    "D3D11/DXCap diagnostics are intentionally not promoted to D3D12 completion evidence."
)
Set-Content -LiteralPath $reportPath -Value $reportRows -Encoding utf8

Get-Content -LiteralPath $compareEnv
exit 1
