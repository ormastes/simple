param(
    [string]$DirectXEvidencePath = "build\gui-web-2d-directx-env-windows-event-strict-gpucap\evidence.env",
    [string]$VulkanEvidencePath = "build\gui-web-2d-vulkan-env-windows-current-check\evidence.env",
    [string]$D3D12EvidencePath = "build\windows-d3d12-render-log-env-strict-current\evidence.env",
    [switch]$RequireFullCompletion
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)

function Invoke-Checker([string]$scriptPath, [string[]]$argsList) {
    $output = & powershell -NoProfile -ExecutionPolicy Bypass -File $scriptPath @argsList 2>&1
    return @{
        ExitCode = $LASTEXITCODE
        Output = @($output | ForEach-Object { "$_" })
    }
}

function Read-OutputValue([string[]]$lines, [string]$key, [string]$defaultValue = "missing") {
    foreach ($line in $lines) {
        if ($line.StartsWith("$key=")) {
            return $line.Substring($key.Length + 1)
        }
    }
    return $defaultValue
}

$directxScript = Join-Path $repoRoot "scripts\check\check-gui-web-2d-directx-strict-evidence.ps1"
$vulkanScript = Join-Path $repoRoot "scripts\check\check-gui-web-2d-vulkan-strict-evidence.ps1"
$d3d12Script = Join-Path $repoRoot "scripts\check\check-windows-d3d12-render-log-evidence.ps1"

$directx = Invoke-Checker $directxScript @("-EvidencePath", $DirectXEvidencePath, "-RequireGpuCapture")
$vulkanPartial = Invoke-Checker $vulkanScript @("-EvidencePath", $VulkanEvidencePath)
$vulkanFull = Invoke-Checker $vulkanScript @("-EvidencePath", $VulkanEvidencePath, "-RequireHostReadiness", "-RequireBrowserRun", "-RequireBrowserBacking", "-RequireRenderDoc")
$d3d12Current = Invoke-Checker $d3d12Script @("-EvidencePath", $D3D12EvidencePath)
$d3d12Full = Invoke-Checker $d3d12Script @("-EvidencePath", $D3D12EvidencePath, "-RequireD3D12Completion")

$directxStatus = Read-OutputValue $directx.Output "gui_web_2d_directx_strict_evidence_status"
$directxReason = Read-OutputValue $directx.Output "gui_web_2d_directx_strict_evidence_reason"
$vulkanPartialStatus = Read-OutputValue $vulkanPartial.Output "gui_web_2d_vulkan_strict_evidence_status"
$vulkanPartialReason = Read-OutputValue $vulkanPartial.Output "gui_web_2d_vulkan_strict_evidence_reason"
$vulkanFullStatus = Read-OutputValue $vulkanFull.Output "gui_web_2d_vulkan_strict_evidence_status"
$vulkanFullReason = Read-OutputValue $vulkanFull.Output "gui_web_2d_vulkan_strict_evidence_reason"
$d3d12CurrentStatus = Read-OutputValue $d3d12Current.Output "windows_d3d12_render_log_evidence_status"
$d3d12CurrentReason = Read-OutputValue $d3d12Current.Output "windows_d3d12_render_log_evidence_reason"
$d3d12FullStatus = Read-OutputValue $d3d12Full.Output "windows_d3d12_render_log_evidence_status"
$d3d12FullReason = Read-OutputValue $d3d12Full.Output "windows_d3d12_render_log_evidence_reason"

$failures = New-Object System.Collections.Generic.List[string]
if ($directx.ExitCode -ne 0 -or $directxStatus -ne "pass") { $failures.Add("directx-strict") | Out-Null }
if ($vulkanPartial.ExitCode -ne 0 -or $vulkanPartialStatus -ne "pass") { $failures.Add("vulkan-partial") | Out-Null }
if ($d3d12Current.ExitCode -ne 0 -or $d3d12CurrentStatus -ne "pass") { $failures.Add("d3d12-current") | Out-Null }
if ($RequireFullCompletion) {
    if ($vulkanFull.ExitCode -ne 0 -or $vulkanFullStatus -ne "pass") { $failures.Add("vulkan-full") | Out-Null }
    if ($d3d12Full.ExitCode -ne 0 -or $d3d12FullStatus -ne "pass") { $failures.Add("d3d12-full") | Out-Null }
}

$status = if ($failures.Count -eq 0) { "pass" } else { "fail" }
$reason = if ($failures.Count -eq 0) { "pass" } else { $failures -join "," }
$vulkanFullGate = if ($vulkanFullStatus -eq "pass") { "pass" } else { "blocked" }
$d3d12FullGate = if ($d3d12FullStatus -eq "pass") { "pass" } else { "blocked" }

Write-Output "windows_gui_web_2d_evidence_bundle_status=$status"
Write-Output "windows_gui_web_2d_evidence_bundle_reason=$reason"
Write-Output "windows_gui_web_2d_evidence_bundle_full_completion_required=$($RequireFullCompletion.IsPresent)"
Write-Output "windows_gui_web_2d_evidence_bundle_directx_strict_status=$directxStatus"
Write-Output "windows_gui_web_2d_evidence_bundle_directx_strict_reason=$directxReason"
Write-Output "windows_gui_web_2d_evidence_bundle_vulkan_partial_status=$vulkanPartialStatus"
Write-Output "windows_gui_web_2d_evidence_bundle_vulkan_partial_reason=$vulkanPartialReason"
Write-Output "windows_gui_web_2d_evidence_bundle_vulkan_full_gate_status=$vulkanFullGate"
Write-Output "windows_gui_web_2d_evidence_bundle_vulkan_full_reason=$vulkanFullReason"
Write-Output "windows_gui_web_2d_evidence_bundle_d3d12_current_status=$d3d12CurrentStatus"
Write-Output "windows_gui_web_2d_evidence_bundle_d3d12_current_reason=$d3d12CurrentReason"
Write-Output "windows_gui_web_2d_evidence_bundle_d3d12_full_gate_status=$d3d12FullGate"
Write-Output "windows_gui_web_2d_evidence_bundle_d3d12_full_reason=$d3d12FullReason"
Write-Output "windows_gui_web_2d_evidence_bundle_directx_evidence_path=$DirectXEvidencePath"
Write-Output "windows_gui_web_2d_evidence_bundle_vulkan_evidence_path=$VulkanEvidencePath"
Write-Output "windows_gui_web_2d_evidence_bundle_d3d12_evidence_path=$D3D12EvidencePath"

if ($status -eq "pass") { exit 0 }
exit 1
