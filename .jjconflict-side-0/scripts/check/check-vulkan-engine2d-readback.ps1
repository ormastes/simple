param(
    [string]$SimpleBinary = "bin\simple.exe",
    [string]$WorkDir = "build\vulkan-engine2d-readback",
    [string]$EvidencePath = "",
    [int]$TimeoutSeconds = 180,
    [int]$MaxExistingSimpleProcesses = 128,
    [switch]$PreflightOnly,
    [switch]$AllowHighSimpleProcessCount
)

$ErrorActionPreference = "Stop"

function Read-KeyValueFile([string]$path) {
    $map = @{}
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return $map
    }
    Get-Content -LiteralPath $path | ForEach-Object {
        $line = $_.Trim()
        if ($line -eq "" -or -not $line.Contains("=")) {
            return
        }
        $idx = $line.IndexOf("=")
        $map[$line.Substring(0, $idx)] = $line.Substring($idx + 1)
    }
    return $map
}

function Value-Or([hashtable]$map, [string]$key, [string]$fallback = "") {
    if ($map.ContainsKey($key) -and -not [string]::IsNullOrWhiteSpace($map[$key])) {
        return [string]$map[$key]
    }
    return $fallback
}

function Write-Env([string]$status, [string]$reason, [string]$specStatus) {
    $e = Read-KeyValueFile $EvidenceLog
    $rows = @(
        "vulkan_engine2d_readback_status=$status",
        "vulkan_engine2d_readback_reason=$reason",
        "vulkan_engine2d_readback_spec_status=$specStatus",
        "vulkan_engine2d_readback_exit_code=$script:EvidenceCode",
        "vulkan_engine2d_readback_preflight_only=$($PreflightOnly.IsPresent.ToString().ToLower())",
        "vulkan_engine2d_readback_timeout_seconds=$TimeoutSeconds",
        "vulkan_engine2d_readback_existing_simple_process_count=$script:ExistingSimpleProcessCount",
        "vulkan_engine2d_readback_existing_simple_process_limit=$MaxExistingSimpleProcesses",
        "vulkan_engine2d_readback_probe_status=$(Value-Or $e 'vulkan_probe_status')",
        "vulkan_engine2d_readback_available=$(Value-Or $e 'vulkan_available')",
        "vulkan_engine2d_readback_backend_name=$(Value-Or $e 'backend_name')",
        "vulkan_engine2d_readback_present_exercised=$(Value-Or $e 'present_exercised')",
        "vulkan_engine2d_readback_readback_exercised=$(Value-Or $e 'readback_exercised')",
        "vulkan_engine2d_readback_clear_status=$(Value-Or $e 'clear_status')",
        "vulkan_engine2d_readback_clear_pixels=$(Value-Or $e 'clear_readback_pixels')",
        "vulkan_engine2d_readback_clear_expected_checksum=$(Value-Or $e 'clear_expected_checksum')",
        "vulkan_engine2d_readback_clear_actual_checksum=$(Value-Or $e 'clear_actual_checksum')",
        "vulkan_engine2d_readback_clear_mismatches=$(Value-Or $e 'clear_mismatches')",
        "vulkan_engine2d_readback_rect_status=$(Value-Or $e 'rect_status')",
        "vulkan_engine2d_readback_rect_pixels=$(Value-Or $e 'rect_readback_pixels')",
        "vulkan_engine2d_readback_rect_expected_checksum=$(Value-Or $e 'rect_expected_checksum')",
        "vulkan_engine2d_readback_rect_actual_checksum=$(Value-Or $e 'rect_actual_checksum')",
        "vulkan_engine2d_readback_rect_mismatches=$(Value-Or $e 'rect_mismatches')",
        "vulkan_engine2d_readback_blur_or_tolerance_used=false",
        "vulkan_engine2d_readback_vulkan_strict_exit_code=$script:StrictCode",
        "vulkan_engine2d_readback_cpu_vulkan_parity_exit_code=$script:ParityCode",
        "vulkan_engine2d_readback_evidence_log=$EvidenceLog",
        "vulkan_engine2d_readback_vulkan_strict_log=$StrictLog",
        "vulkan_engine2d_readback_cpu_vulkan_parity_log=$ParityLog",
        "simpleos_engine2d_runtime_backend=$(Value-Or $e 'backend_name')",
        "simpleos_engine2d_scene=$(if ((Value-Or $e 'backend_name') -eq 'vulkan') { 'vulkan-engine2d' } else { '' })",
        "simpleos_engine2d_viewport_width=16",
        "simpleos_engine2d_viewport_height=16",
        "simpleos_engine2d_readback_checksum=$(Value-Or $e 'rect_actual_checksum')",
        "gui_web_2d_vulkan_simple_status=$status",
        "gui_web_2d_vulkan_simple_reason=$reason",
        "gui_web_2d_vulkan_simple_exit_code=$script:EvidenceCode",
        "gui_web_2d_vulkan_simple_probe_status=$(Value-Or $e 'vulkan_probe_status')",
        "gui_web_2d_vulkan_simple_backend_name=$(Value-Or $e 'backend_name')",
        "gui_web_2d_vulkan_simple_argb_width=16",
        "gui_web_2d_vulkan_simple_argb_height=16",
        "gui_web_2d_vulkan_simple_argb_checksum=$(Value-Or $e 'rect_actual_checksum')"
    )
    $rows | Set-Content -Encoding ASCII -Path $EvidencePath
    $rows | ForEach-Object { Write-Output $_ }
}

function Invoke-SimpleWithTimeout([string[]]$arguments, [string]$stdoutPath) {
    Remove-Item -LiteralPath $stdoutPath -Force -ErrorAction SilentlyContinue
    $stderrPath = "$stdoutPath.stderr"
    Remove-Item -LiteralPath $stderrPath -Force -ErrorAction SilentlyContinue
    $previousSimpleLib = $env:SIMPLE_LIB
    $env:SIMPLE_LIB = "src"
    $proc = Start-Process -FilePath (Resolve-Path -LiteralPath $SimpleBinary) -ArgumentList $arguments -WorkingDirectory $RepoRoot -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath -NoNewWindow -PassThru
    $completed = $proc.WaitForExit($TimeoutSeconds * 1000)
    if (-not $completed) {
        try { $proc.Kill($true) } catch { }
        Add-Content -Encoding ASCII -Path $stdoutPath -Value "timeout_seconds=$TimeoutSeconds"
        if ($null -eq $previousSimpleLib) {
            Remove-Item Env:\SIMPLE_LIB -ErrorAction SilentlyContinue
        } else {
            $env:SIMPLE_LIB = $previousSimpleLib
        }
        return 124
    }
    $proc.WaitForExit()
    $proc.Refresh()
    if ($null -eq $previousSimpleLib) {
        Remove-Item Env:\SIMPLE_LIB -ErrorAction SilentlyContinue
    } else {
        $env:SIMPLE_LIB = $previousSimpleLib
    }
    if ((Test-Path -LiteralPath $stderrPath) -and (Get-Item -LiteralPath $stderrPath).Length -gt 0) {
        Get-Content -LiteralPath $stderrPath | Add-Content -Encoding ASCII -Path $stdoutPath
    }
    if ($null -ne $proc.ExitCode) {
        return $proc.ExitCode
    }
    if ($proc.HasExited) {
        return 0
    }
    return 1
}

$ScriptDir = Split-Path -Parent $PSCommandPath
$RepoRoot = Resolve-Path -LiteralPath (Join-Path $ScriptDir "..\..")
Set-Location $RepoRoot

if ([string]::IsNullOrWhiteSpace($EvidencePath)) {
    $EvidencePath = Join-Path $WorkDir "evidence.env"
}
New-Item -ItemType Directory -Force -Path $WorkDir | Out-Null
$EvidenceLog = Join-Path $WorkDir "evidence.log"
$StrictLog = Join-Path $WorkDir "vulkan_strict.json"
$ParityLog = Join-Path $WorkDir "engine2d_cpu_vulkan_parity.json"
$EvidenceSource = "scripts/check/vulkan_engine2d_readback_evidence.spl"
$script:StrictCode = ""
$script:ParityCode = ""
$script:EvidenceCode = ""
$script:ExistingSimpleProcessCount = ""

Write-Output "check=vulkan_engine2d_readback"
Write-Output "simple_bin=$SimpleBinary"
Write-Output "timeout_secs=$TimeoutSeconds"
Write-Output "evidence_source=$EvidenceSource"

if (-not (Test-Path -LiteralPath $SimpleBinary)) {
    "error=missing_executable:$SimpleBinary" | Set-Content -Encoding ASCII -Path $EvidenceLog
    Write-Env "fail" "missing-simple-binary" "not_run"
    exit 1
}

try {
    $script:ExistingSimpleProcessCount = (Get-Process -Name simple -ErrorAction SilentlyContinue | Measure-Object).Count.ToString()
} catch {
    $script:ExistingSimpleProcessCount = "unknown"
}
if (-not $AllowHighSimpleProcessCount -and
    $script:ExistingSimpleProcessCount -ne "unknown" -and
    [int]$script:ExistingSimpleProcessCount -gt $MaxExistingSimpleProcesses) {
    @(
        "simple_process_count=$script:ExistingSimpleProcessCount",
        "simple_process_limit=$MaxExistingSimpleProcesses",
        "error=existing-simple-process-count-high"
    ) | Set-Content -Encoding ASCII -Path $EvidenceLog
    $script:EvidenceCode = "not-run"
    Write-Env "fail" "existing-simple-process-count-high" "not_run"
    exit 1
}
if ($PreflightOnly) {
    @(
        "simple_process_count=$script:ExistingSimpleProcessCount",
        "simple_process_limit=$MaxExistingSimpleProcesses",
        "preflight_only=true"
    ) | Set-Content -Encoding ASCII -Path $EvidenceLog
    $script:EvidenceCode = "not-run"
    Write-Env "blocked" "preflight-only" "not_run"
    exit 1
}

$evidenceCode = Invoke-SimpleWithTimeout -arguments @($EvidenceSource, "--mode=interpreter", "--clean") -stdoutPath $EvidenceLog
$script:EvidenceCode = "$evidenceCode"
Get-Content -LiteralPath $EvidenceLog | ForEach-Object { Write-Output $_ }
Write-Output "evidence_exit_code=$evidenceCode"

if ($evidenceCode -ne 0) {
    $reason = if ($evidenceCode -eq 124) { "evidence-program-timeout" } else { "evidence-program-failed" }
    Write-Env "fail" $reason "not_run"
    exit 1
}

$evidence = Read-KeyValueFile $EvidenceLog
if ((Value-Or $evidence "overall") -ne "pass") {
    Write-Env "fail" "evidence-status-not-pass" "not_run"
    exit 1
}

$script:StrictCode = Invoke-SimpleWithTimeout -arguments @("test", "test/02_integration/rendering/vulkan_strict_spec.spl", "--mode=interpreter", "--clean", "--format", "json") -stdoutPath $StrictLog
$script:ParityCode = Invoke-SimpleWithTimeout -arguments @("test", "test/02_integration/rendering/engine2d_cpu_vulkan_parity_spec.spl", "--mode=interpreter", "--clean", "--format", "json") -stdoutPath $ParityLog
Write-Output "vulkan_strict_exit_code=$script:StrictCode"
Write-Output "engine2d_cpu_vulkan_parity_exit_code=$script:ParityCode"

if ($script:StrictCode -ne 0 -or $script:ParityCode -ne 0) {
    Write-Env "fail" "focused-specs-failed" "fail"
    exit 1
}

Write-Env "pass" "pass" "pass"
exit 0
