param(
    [string]$EvidencePath = "build\gui-web-2d-vulkan-env-windows-current-check\evidence.env",
    [switch]$RequireHostReadiness,
    [switch]$RequireBrowserRun,
    [switch]$RequireBrowserBacking,
    [switch]$RequireRenderDoc
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

function Has-RdocMagic([string]$path) {
    $path = Resolve-RepoPath $path
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $false }
    $stream = [System.IO.File]::OpenRead($path)
    try {
        if ($stream.Length -lt 4) { return $false }
        $bytes = New-Object byte[] 4
        [void]$stream.Read($bytes, 0, 4)
        return ([System.Text.Encoding]::ASCII.GetString($bytes) -eq "RDOC")
    } finally {
        $stream.Dispose()
    }
}

function Is-PositiveInt([string]$value) {
    $parsed = 0
    return ([int]::TryParse($value, [ref]$parsed) -and $parsed -gt 0)
}

$evidence = Read-KeyValueFile $EvidencePath
$simpleStatus = Value-Or $evidence "gui_web_2d_vulkan_simple_status" "missing"
$simpleBackend = Value-Or $evidence "gui_web_2d_vulkan_simple_backend_name" "missing"
$simpleWidth = Value-Or $evidence "gui_web_2d_vulkan_simple_argb_width" "0"
$simpleHeight = Value-Or $evidence "gui_web_2d_vulkan_simple_argb_height" "0"
$simplePixelCount = Value-Or $evidence "gui_web_2d_vulkan_simple_argb_pixel_count" "0"
$simpleChecksum = Value-Or $evidence "gui_web_2d_vulkan_simple_argb_checksum" ""
$vulkaninfoStatus = Value-Or $evidence "gui_web_2d_vulkan_vulkaninfo_status" "missing"
$dxcStatus = Value-Or $evidence "gui_web_2d_vulkan_dxc_status" "missing"
$glslangStatus = Value-Or $evidence "gui_web_2d_vulkan_glslang_validator_status" "missing"
$spirvAsStatus = Value-Or $evidence "gui_web_2d_vulkan_spirv_as_status" "missing"
$sdkToolsStatus = Value-Or $evidence "gui_web_2d_vulkan_sdk_tools_status" "missing"
$renderdocStatus = Value-Or $evidence "gui_web_2d_vulkan_renderdoc_status" "missing"
$hostReadinessStatus = Value-Or $evidence "gui_web_2d_vulkan_host_readiness_status" "missing"
$directRunStatus = Value-Or $evidence "gui_web_2d_vulkan_direct_run_status" "missing"
$browserBackingStatus = Value-Or $evidence "gui_web_2d_vulkan_browser_backing_status" "missing"
$browserEventStatus = Value-Or $evidence "gui_web_2d_vulkan_browser_event_status" "missing"
$electronEventStatus = Value-Or $evidence "gui_web_2d_vulkan_electron_event_status" "missing"
$chromeEventStatus = Value-Or $evidence "gui_web_2d_vulkan_chrome_event_status" "missing"
$renderdocCaptureStatus = Value-Or $evidence "gui_web_2d_vulkan_renderdoc_capture_status" "missing"
$renderdocRdc = Value-Or $evidence "gui_web_2d_vulkan_renderdoc_capture_rdc" ""
$renderdocRdcMagic = if ($RequireRenderDoc) { if (Has-RdocMagic $renderdocRdc) { "RDOC" } else { "missing-or-invalid" } } else { "not-required" }
$simpleMetricsStatus = if ((Is-PositiveInt $simpleWidth) -and (Is-PositiveInt $simpleHeight) -and (Is-PositiveInt $simplePixelCount)) { "pass" } else { "invalid-simple-vulkan-readback-metrics" }

$failures = New-Object System.Collections.Generic.List[string]
if ($simpleStatus -ne "pass" -or $simpleBackend -ne "vulkan" -or $simpleChecksum -eq "") { $failures.Add("simple-vulkan-readback") | Out-Null }
if ($simpleMetricsStatus -ne "pass") { $failures.Add("simple-vulkan-readback-metrics") | Out-Null }
if ($vulkaninfoStatus -ne "pass") { $failures.Add("vulkaninfo") | Out-Null }
if ($dxcStatus -ne "pass") { $failures.Add("dxc") | Out-Null }
if ($RequireHostReadiness -and ($glslangStatus -ne "pass" -or $spirvAsStatus -ne "pass" -or $sdkToolsStatus -ne "pass")) { $failures.Add("sdk-tools") | Out-Null }
if ($RequireHostReadiness -and $renderdocStatus -ne "pass") { $failures.Add("renderdoc-tools") | Out-Null }
if ($RequireHostReadiness -and $hostReadinessStatus -ne "pass") { $failures.Add("host-readiness") | Out-Null }
if ($RequireBrowserRun -and $directRunStatus -ne "pass") { $failures.Add("browser-run") | Out-Null }
if ($RequireBrowserRun -and ($browserEventStatus -ne "pass" -or $electronEventStatus -ne "pass" -or $chromeEventStatus -ne "pass")) { $failures.Add("browser-events") | Out-Null }
if ($RequireBrowserBacking -and $browserBackingStatus -ne "pass") { $failures.Add("browser-backing") | Out-Null }
if ($RequireRenderDoc -and ($renderdocCaptureStatus -ne "pass" -or $renderdocRdcMagic -ne "RDOC")) { $failures.Add("renderdoc-capture") | Out-Null }

$status = if ($failures.Count -eq 0) { "pass" } else { "fail" }
$reason = if ($failures.Count -eq 0) { "pass" } else { $failures -join "," }

Write-Output "gui_web_2d_vulkan_strict_evidence_status=$status"
Write-Output "gui_web_2d_vulkan_strict_evidence_reason=$reason"
Write-Output "gui_web_2d_vulkan_strict_evidence_path=$EvidencePath"
Write-Output "gui_web_2d_vulkan_strict_evidence_simple_status=$simpleStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_simple_backend=$simpleBackend"
Write-Output "gui_web_2d_vulkan_strict_evidence_simple_metrics_status=$simpleMetricsStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_simple_argb_width=$simpleWidth"
Write-Output "gui_web_2d_vulkan_strict_evidence_simple_argb_height=$simpleHeight"
Write-Output "gui_web_2d_vulkan_strict_evidence_simple_argb_pixel_count=$simplePixelCount"
Write-Output "gui_web_2d_vulkan_strict_evidence_vulkaninfo_status=$vulkaninfoStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_dxc_status=$dxcStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_glslang_status=$glslangStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_spirv_as_status=$spirvAsStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_sdk_tools_status=$sdkToolsStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_renderdoc_status=$renderdocStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_host_readiness_status=$hostReadinessStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_browser_run_required=$($RequireBrowserRun.IsPresent)"
Write-Output "gui_web_2d_vulkan_strict_evidence_direct_run_status=$directRunStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_browser_event_status=$browserEventStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_electron_event_status=$electronEventStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_chrome_event_status=$chromeEventStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_browser_backing_required=$($RequireBrowserBacking.IsPresent)"
Write-Output "gui_web_2d_vulkan_strict_evidence_browser_backing_status=$browserBackingStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_renderdoc_required=$($RequireRenderDoc.IsPresent)"
Write-Output "gui_web_2d_vulkan_strict_evidence_renderdoc_capture_status=$renderdocCaptureStatus"
Write-Output "gui_web_2d_vulkan_strict_evidence_renderdoc_capture_rdc=$renderdocRdc"
Write-Output "gui_web_2d_vulkan_strict_evidence_renderdoc_capture_rdc_magic=$renderdocRdcMagic"

if ($status -eq "pass") { exit 0 }
exit 1
