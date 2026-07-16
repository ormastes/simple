param(
    [string]$EvidencePath = "build\gui-web-2d-directx-env-windows-event-strict-gpucap\evidence.env",
    [switch]$RequireGpuCapture
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

function Has-GfxaMagic([string]$path) {
    $path = Resolve-RepoPath $path
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $false }
    $stream = [System.IO.File]::OpenRead($path)
    try {
        if ($stream.Length -lt 4) { return $false }
        $bytes = New-Object byte[] 4
        [void]$stream.Read($bytes, 0, 4)
        return ([System.Text.Encoding]::ASCII.GetString($bytes) -eq "GFXA")
    } finally {
        $stream.Dispose()
    }
}

$evidence = Read-KeyValueFile $EvidencePath
$nativeStatus = Value-Or $evidence "gui_web_2d_directx_native_readback_status" "missing"
$nativeGate = Value-Or $evidence "gui_web_2d_directx_native_readback_gate_status" "missing"
$browserBackingStatus = Value-Or $evidence "gui_web_2d_directx_browser_backing_status" "missing"
$browserEventStatus = Value-Or $evidence "gui_web_2d_directx_browser_event_status" "missing"
$electronEventStatus = Value-Or $evidence "gui_web_2d_directx_electron_event_status" "missing"
$chromeEventStatus = Value-Or $evidence "gui_web_2d_directx_chrome_event_status" "missing"
$gpuCaptureStatus = Value-Or $evidence "gui_web_2d_directx_gpu_debugger_capture_status" $(if ($RequireGpuCapture) { "missing" } else { "not-required" })
$gpuArtifact = Value-Or $evidence "gui_web_2d_directx_gpu_debugger_capture_artifact" ""
$gpuArtifactMagic = if ($RequireGpuCapture) { if (Has-GfxaMagic $gpuArtifact) { "GFXA" } else { "missing-or-invalid" } } else { "not-required" }

$failures = New-Object System.Collections.Generic.List[string]
if ($nativeStatus -ne "pass" -or $nativeGate -ne "pass") { $failures.Add("native-readback") | Out-Null }
if ($browserBackingStatus -ne "pass") { $failures.Add("browser-backing") | Out-Null }
if ($browserEventStatus -ne "pass" -or $electronEventStatus -ne "pass" -or $chromeEventStatus -ne "pass") { $failures.Add("browser-events") | Out-Null }
if ($RequireGpuCapture -and ($gpuCaptureStatus -ne "pass" -or $gpuArtifactMagic -ne "GFXA")) { $failures.Add("gpu-capture") | Out-Null }

$status = if ($failures.Count -eq 0) { "pass" } else { "fail" }
$reason = if ($failures.Count -eq 0) { "pass" } else { $failures -join "," }

Write-Output "gui_web_2d_directx_strict_evidence_status=$status"
Write-Output "gui_web_2d_directx_strict_evidence_reason=$reason"
Write-Output "gui_web_2d_directx_strict_evidence_path=$EvidencePath"
Write-Output "gui_web_2d_directx_strict_evidence_native_readback_status=$nativeStatus"
Write-Output "gui_web_2d_directx_strict_evidence_native_gate_status=$nativeGate"
Write-Output "gui_web_2d_directx_strict_evidence_browser_backing_status=$browserBackingStatus"
Write-Output "gui_web_2d_directx_strict_evidence_browser_event_status=$browserEventStatus"
Write-Output "gui_web_2d_directx_strict_evidence_electron_event_status=$electronEventStatus"
Write-Output "gui_web_2d_directx_strict_evidence_chrome_event_status=$chromeEventStatus"
Write-Output "gui_web_2d_directx_strict_evidence_gpu_capture_required=$($RequireGpuCapture.IsPresent)"
Write-Output "gui_web_2d_directx_strict_evidence_gpu_capture_status=$gpuCaptureStatus"
Write-Output "gui_web_2d_directx_strict_evidence_gpu_capture_artifact=$gpuArtifact"
Write-Output "gui_web_2d_directx_strict_evidence_gpu_capture_artifact_magic=$gpuArtifactMagic"

if ($status -eq "pass") { exit 0 }
exit 1
