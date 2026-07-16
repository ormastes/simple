param(
    [string]$EvidencePath = "build\windows-d3d12-render-log-env-strict-current\evidence.env",
    [switch]$RequireD3D12Completion
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

function Read-KeyValueFile([string]$path) {
    $path = Resolve-RepoPath $path
    $map = @{}
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return $map
    }
    Get-Content -LiteralPath $path | ForEach-Object {
        $line = $_.Trim()
        if ($line -eq "" -or $line.StartsWith("#")) { return }
        $idx = $line.IndexOf("=")
        if ($idx -le 0) { return }
        $map[$line.Substring(0, $idx)] = $line.Substring($idx + 1)
    }
    return $map
}

function Value-Or($map, [string]$key, [string]$defaultValue = "") {
    if ($map.ContainsKey($key) -and "$($map[$key])" -ne "") {
        return "$($map[$key])"
    }
    return $defaultValue
}

function Has-FileMagic([string]$path, [string]$magic) {
    $path = Resolve-RepoPath $path
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $false }
    $stream = [System.IO.File]::OpenRead($path)
    try {
        if ($stream.Length -lt $magic.Length) { return $false }
        $bytes = New-Object byte[] $magic.Length
        [void]$stream.Read($bytes, 0, $magic.Length)
        return ([System.Text.Encoding]::ASCII.GetString($bytes) -eq $magic)
    } finally {
        $stream.Dispose()
    }
}

$evidence = Read-KeyValueFile $EvidencePath
$compareStatus = Value-Or $evidence "windows_d3d12_render_log_compare_status" "missing"
$requiredApi = Value-Or $evidence "windows_d3d12_render_log_compare_required_api" "missing"
$blockedGateCount = Value-Or $evidence "windows_d3d12_render_log_compare_blocked_gate_count" "missing"
$blockedGates = Value-Or $evidence "windows_d3d12_render_log_compare_blocked_gates" "missing"
$nativeGate = Value-Or $evidence "windows_d3d12_render_log_compare_native_readback_gate_status" "missing"
$browserGate = Value-Or $evidence "windows_d3d12_render_log_compare_browser_backing_gate_status" "missing"
$pairwiseGate = Value-Or $evidence "windows_d3d12_render_log_compare_pairwise_gate_status" "missing"
$argbGate = Value-Or $evidence "windows_d3d12_render_log_compare_argb_source_gate_status" "missing"
$pixGate = Value-Or $evidence "windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status" "missing"
$directxStrict = Value-Or $evidence "windows_d3d12_render_log_compare_directx_strict_diagnostic_status" "missing"
$directxEvent = Value-Or $evidence "windows_d3d12_render_log_compare_directx_diagnostic_event_status" "missing"
$directxGpu = Value-Or $evidence "windows_d3d12_render_log_compare_directx_diagnostic_gpu_capture_status" "missing"
$directxApi = Value-Or $evidence "windows_d3d12_render_log_compare_directx_diagnostic_api" "missing"
$pixStatus = Value-Or $evidence "windows_d3d12_render_log_compare_pix_status" "missing"
$pixArtifact = Value-Or $evidence "windows_d3d12_render_log_compare_pix_artifact" ""
$gpuDebuggerStatus = Value-Or $evidence "windows_d3d12_render_log_compare_gpu_debugger_status" "missing"
$gpuDebuggerArtifact = Value-Or $evidence "windows_d3d12_render_log_compare_gpu_debugger_artifact" ""
$pixMagic = if ($RequireD3D12Completion) { if (Has-FileMagic $pixArtifact "WPIX") { "WPIX" } else { "missing-or-invalid" } } else { "not-required" }
$gpuMagic = if ($RequireD3D12Completion) { if (Has-FileMagic $gpuDebuggerArtifact "GFXA") { "GFXA" } else { "missing-or-invalid" } } else { "not-required" }

$failures = New-Object System.Collections.Generic.List[string]
if ($requiredApi -ne "d3d12") { $failures.Add("required-api") | Out-Null }
if ($directxStrict -ne "pass" -or $directxEvent -ne "pass" -or $directxGpu -ne "pass") { $failures.Add("strict-directx-diagnostic") | Out-Null }
if ($RequireD3D12Completion) {
    if ($compareStatus -ne "pass") { $failures.Add("compare-status") | Out-Null }
    if ($nativeGate -ne "pass") { $failures.Add("native-d3d12-readback") | Out-Null }
    if ($browserGate -ne "pass") { $failures.Add("browser-d3d12-backing") | Out-Null }
    if ($pairwiseGate -ne "pass") { $failures.Add("pairwise-argb-diff") | Out-Null }
    if ($argbGate -ne "pass") { $failures.Add("argb-source-evidence") | Out-Null }
    if ($pixGate -ne "pass") { $failures.Add("pix-gpu-debugger-gate") | Out-Null }
    if ($pixStatus -ne "pass" -and $gpuDebuggerStatus -ne "pass") { $failures.Add("pix-or-gpu-debugger-status") | Out-Null }
    if ($pixMagic -ne "WPIX" -and $gpuMagic -ne "GFXA") { $failures.Add("pix-or-gpu-debugger-artifact") | Out-Null }
} else {
    if ($compareStatus -ne "fail") { $failures.Add("fail-closed-status") | Out-Null }
    if ($blockedGateCount -eq "missing" -or $blockedGates -eq "missing") { $failures.Add("blocked-gate-summary") | Out-Null }
}

$status = if ($failures.Count -eq 0) { "pass" } else { "fail" }
$reason = if ($failures.Count -eq 0) { "pass" } else { $failures -join "," }

Write-Output "windows_d3d12_render_log_evidence_status=$status"
Write-Output "windows_d3d12_render_log_evidence_reason=$reason"
Write-Output "windows_d3d12_render_log_evidence_path=$EvidencePath"
Write-Output "windows_d3d12_render_log_evidence_completion_required=$($RequireD3D12Completion.IsPresent)"
Write-Output "windows_d3d12_render_log_evidence_compare_status=$compareStatus"
Write-Output "windows_d3d12_render_log_evidence_required_api=$requiredApi"
Write-Output "windows_d3d12_render_log_evidence_blocked_gate_count=$blockedGateCount"
Write-Output "windows_d3d12_render_log_evidence_blocked_gates=$blockedGates"
Write-Output "windows_d3d12_render_log_evidence_native_gate_status=$nativeGate"
Write-Output "windows_d3d12_render_log_evidence_browser_gate_status=$browserGate"
Write-Output "windows_d3d12_render_log_evidence_pairwise_gate_status=$pairwiseGate"
Write-Output "windows_d3d12_render_log_evidence_argb_gate_status=$argbGate"
Write-Output "windows_d3d12_render_log_evidence_pix_gpu_debugger_gate_status=$pixGate"
Write-Output "windows_d3d12_render_log_evidence_directx_strict_diagnostic_status=$directxStrict"
Write-Output "windows_d3d12_render_log_evidence_directx_event_status=$directxEvent"
Write-Output "windows_d3d12_render_log_evidence_directx_gpu_capture_status=$directxGpu"
Write-Output "windows_d3d12_render_log_evidence_directx_api=$directxApi"
Write-Output "windows_d3d12_render_log_evidence_pix_status=$pixStatus"
Write-Output "windows_d3d12_render_log_evidence_pix_artifact=$pixArtifact"
Write-Output "windows_d3d12_render_log_evidence_pix_artifact_magic=$pixMagic"
Write-Output "windows_d3d12_render_log_evidence_gpu_debugger_status=$gpuDebuggerStatus"
Write-Output "windows_d3d12_render_log_evidence_gpu_debugger_artifact=$gpuDebuggerArtifact"
Write-Output "windows_d3d12_render_log_evidence_gpu_debugger_artifact_magic=$gpuMagic"

if ($status -eq "pass") { exit 0 }
exit 1
