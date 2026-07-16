param(
    [string]$EvidencePath = "build/simpleos_multiconfig_live_evidence/engine2d-renderdoc.env",
    [string]$BaseEvidencePath = "",
    [string]$Engine2dEvidencePath = "build/gui-web-2d-vulkan-env/evidence.env",
    [string]$RuntimeBackend = "",
    [string]$VulkanDeviceName = "",
    [int]$ViewportWidth = 0,
    [int]$ViewportHeight = 0,
    [string]$ReadbackChecksum = "",
    [string]$QemuReadbackPath = "build/os/systest/qemu-riscv64-desktop/qemu-screendump.ppm",
    [string]$SimpleRdcPath = "build/os/systest/qemu-riscv64-desktop/simpleos-wm.rdc",
    [string]$CaptureLogPath = "build/os/systest/qemu-riscv64-desktop/renderdoc-capture.log",
    [string]$QemuRenderdocLogPath = "build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log",
    [string]$HostRenderdocLogPath = "build/os/systest/qemu-riscv64-desktop/host-wm-renderdoc.log",
    [string]$SceneName = "vulkan-engine2d",
    [switch]$RunSimpleVulkanProbe,
    [string]$SimpleBinary = "bin\simple.exe",
    [string]$SimpleVulkanProbeWorkDir = "build\vulkan-engine2d-readback-windows",
    [string]$SimpleVulkanProbeEvidencePath = "",
    [int]$SimpleVulkanProbeTimeoutSeconds = 180,
    [int]$SimpleVulkanProbeMaxExistingSimpleProcesses = 128,
    [switch]$SimpleVulkanProbePreflightOnly,
    [switch]$AllowHighSimpleProcessCount,
    [switch]$ProbeHostVulkan,
    [string]$HostVulkanLogPath = "build/simpleos_multiconfig_live_evidence/windows-vulkan-host.log"
)

$ErrorActionPreference = "Stop"

function Write-Row($rows, [string]$key, [string]$value) {
    $prefix = "$key="
    for ($i = $rows.Count - 1; $i -ge 0; $i--) {
        if ($rows[$i].StartsWith($prefix)) {
            $rows.RemoveAt($i)
        }
    }
    $rows.Add("$key=$value") | Out-Null
}

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
        $key = $line.Substring(0, $idx)
        $value = $line.Substring($idx + 1)
        $map[$key] = $value
    }
    return $map
}

function Value-Or([hashtable]$map, [string[]]$keys, [string]$fallback) {
    foreach ($key in $keys) {
        if ($map.ContainsKey($key) -and -not [string]::IsNullOrWhiteSpace($map[$key])) {
            return [string]$map[$key]
        }
    }
    return $fallback
}

function Test-FileNonEmpty([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return $false
    }
    return ((Get-Item -LiteralPath $path).Length -gt 0)
}

function Test-FileContains([string]$path, [string]$pattern) {
    if (-not (Test-Path -LiteralPath $path)) {
        return $false
    }
    $text = Get-Content -Raw -LiteralPath $path
    return $text.Contains($pattern)
}

function Read-RdcMagic([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return ""
    }
    $stream = [System.IO.File]::OpenRead((Resolve-Path -LiteralPath $path))
    try {
        $buffer = New-Object byte[] 4
        $count = $stream.Read($buffer, 0, 4)
        if ($count -lt 4) {
            return ""
        }
        return [System.Text.Encoding]::ASCII.GetString($buffer, 0, 4)
    } finally {
        $stream.Close()
    }
}

function Get-FileSizeText([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return "0"
    }
    return ((Get-Item -LiteralPath $path).Length).ToString()
}

function Test-PpmNonblank([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return "missing"
    }
    $bytes = [System.IO.File]::ReadAllBytes((Resolve-Path -LiteralPath $path))
    if ($bytes.Length -le 32) {
        return "blocked:ppm-too-small"
    }
    if ($bytes[0] -ne [byte][char]'P' -or $bytes[1] -ne [byte][char]'6') {
        return "blocked:not-p6-ppm"
    }
    $first = $bytes[$bytes.Length - 1]
    $start = [Math]::Max(0, $bytes.Length - 4096)
    for ($i = $start; $i -lt $bytes.Length; $i++) {
        if ($bytes[$i] -ne $first) {
            return "pass"
        }
    }
    return "blocked:blank-ppm"
}

function Read-PpmDimensions([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return @{ width = 0; height = 0; status = "missing" }
    }
    $bytes = [System.IO.File]::ReadAllBytes((Resolve-Path -LiteralPath $path))
    if ($bytes.Length -lt 16 -or $bytes[0] -ne [byte][char]'P' -or $bytes[1] -ne [byte][char]'6') {
        return @{ width = 0; height = 0; status = "blocked:not-p6-ppm" }
    }
    $tokens = [System.Collections.Generic.List[string]]::new()
    $token = ""
    $i = 2
    while ($i -lt $bytes.Length -and $tokens.Count -lt 3) {
        $ch = [char]$bytes[$i]
        if ($ch -eq '#') {
            while ($i -lt $bytes.Length -and [char]$bytes[$i] -ne "`n") {
                $i++
            }
        } elseif ([char]::IsWhiteSpace($ch)) {
            if ($token -ne "") {
                $tokens.Add($token) | Out-Null
                $token = ""
            }
        } else {
            $token += $ch
        }
        $i++
    }
    if ($token -ne "" -and $tokens.Count -lt 3) {
        $tokens.Add($token) | Out-Null
    }
    if ($tokens.Count -lt 3) {
        return @{ width = 0; height = 0; status = "blocked:bad-ppm-header" }
    }
    return @{ width = [int]$tokens[0]; height = [int]$tokens[1]; status = "pass" }
}

function Checksum-FileTail([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return ""
    }
    $bytes = [System.IO.File]::ReadAllBytes((Resolve-Path -LiteralPath $path))
    $start = [Math]::Max(0, $bytes.Length - 4096)
    [UInt64]$sum = 0
    for ($i = $start; $i -lt $bytes.Length; $i++) {
        $sum = ($sum + [UInt64]$bytes[$i] * [UInt64]($i - $start + 1)) -band [UInt64]::MaxValue
    }
    return $sum.ToString()
}

function Command-Source-OrEmpty([string]$name) {
    $cmd = Get-Command $name -ErrorAction SilentlyContinue
    if ($cmd) {
        return $cmd.Source
    }
    return ""
}

function Command-Status([string]$name) {
    if ((Command-Source-OrEmpty $name) -ne "") {
        return "pass"
    }
    return "missing"
}

function First-Match-OrEmpty([string]$text, [string]$pattern) {
    $m = [regex]::Match($text, $pattern)
    if ($m.Success -and $m.Groups.Count -gt 1) {
        return $m.Groups[1].Value.Trim()
    }
    return ""
}

function Source-Evidence-Usability([hashtable]$source, [string]$runtimeBackend, [string]$readbackChecksum) {
    if ($source.Count -eq 0) {
        return @{ status = "missing"; reason = "missing-source-evidence" }
    }
    $directReadbackStatus = Value-Or $source @("vulkan_engine2d_readback_status") ""
    $directReadbackSpecStatus = Value-Or $source @("vulkan_engine2d_readback_spec_status") ""
    $directReadbackBackend = Value-Or $source @("vulkan_engine2d_readback_backend_name") ""
    if ($directReadbackStatus -eq "pass" -and $directReadbackSpecStatus -eq "pass" -and $directReadbackBackend -eq "vulkan" -and $runtimeBackend -eq "vulkan" -and $readbackChecksum -ne "") {
        return @{ status = "pass"; reason = "direct-simple-vulkan-engine2d-readback" }
    }
    if ($directReadbackStatus -ne "") {
        $directReason = Value-Or $source @("vulkan_engine2d_readback_reason") "direct-simple-vulkan-readback-not-pass"
        return @{ status = "blocked"; reason = "direct-simple-vulkan-readback-$directReason" }
    }
    $mode = Value-Or $source @("gui_web_2d_vulkan_mode") ""
    $simpleStatus = Value-Or $source @("gui_web_2d_vulkan_simple_status") ""
    $simpleBackendName = Value-Or $source @("gui_web_2d_vulkan_simple_backend_name", "simpleos_engine2d_runtime_backend") ""
    $browserBackingStatus = Value-Or $source @("gui_web_2d_vulkan_browser_backing_status") ""
    if ($mode -eq "--browser-backing" -and ($simpleStatus -eq "" -or $simpleStatus -eq "not-run")) {
        return @{ status = "blocked"; reason = "source-browser-backing-only-simple-not-run" }
    }
    if ($browserBackingStatus -eq "fail" -and ($simpleStatus -eq "" -or $simpleStatus -eq "not-run")) {
        return @{ status = "blocked"; reason = "source-browser-backing-failed-simple-not-run" }
    }
    if ($runtimeBackend -ne "vulkan") {
        return @{ status = "blocked"; reason = "source-missing-simple-vulkan-backend" }
    }
    if ($readbackChecksum -eq "") {
        return @{ status = "blocked"; reason = "source-missing-simple-readback-checksum" }
    }
    if ($simpleBackendName -ne "" -and $simpleBackendName -ne "vulkan") {
        return @{ status = "blocked"; reason = "source-simple-backend-not-vulkan" }
    }
    return @{ status = "pass"; reason = "source-simple-vulkan-readback" }
}

function Runtime-Backend-Reason([string]$runtimeBackend, [hashtable]$source) {
    if ($runtimeBackend -eq "vulkan") {
        return "pass"
    }
    if ($source.Count -eq 0) {
        return "missing-source-evidence"
    }
    $simpleStatus = Value-Or $source @("gui_web_2d_vulkan_simple_status") ""
    if ($simpleStatus -eq "not-run") {
        return "simple-vulkan-probe-not-run"
    }
    if ($simpleStatus -ne "") {
        return "simple-vulkan-probe-status:$simpleStatus"
    }
    return "missing-simple-vulkan-backend"
}

function Renderdoc-Artifact-Reason([string]$rdcMagic, [string]$captureLogStatus, [string]$runtimeBackend, [string]$qemuLogPath, [string]$hostLogPath) {
    if ($rdcMagic -ne "RDOC") {
        return "missing-simple-rdoc-magic"
    }
    if ($captureLogStatus -ne "pass") {
        return "missing-renderdoc-capture-log"
    }
    if ($runtimeBackend -ne "vulkan") {
        return "missing-simple-vulkan-runtime"
    }
    if (-not (Test-FileNonEmpty $qemuLogPath)) {
        return "missing-qemu-wm-renderdoc-log"
    }
    if (-not (Test-FileNonEmpty $hostLogPath)) {
        return "missing-host-wm-renderdoc-log"
    }
    return "pass"
}

function Wm-Renderdoc-Log-Compare-Reason([string]$qemuLogPath, [string]$hostLogPath) {
    $qemuPresent = Test-FileNonEmpty $qemuLogPath
    $hostPresent = Test-FileNonEmpty $hostLogPath
    if ($qemuPresent -and $hostPresent) {
        return "ready-for-log-compare"
    }
    if (-not $qemuPresent -and -not $hostPresent) {
        return "missing-qemu-and-host-renderdoc-logs"
    }
    if (-not $qemuPresent) {
        return "missing-qemu-renderdoc-log"
    }
    return "missing-host-renderdoc-log"
}

$scriptDir = Split-Path -Parent $PSCommandPath
$repoRoot = Resolve-Path -LiteralPath (Join-Path $scriptDir "..\..")

function Resolve-RepoPath([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path)) {
        return $path
    }
    if ([System.IO.Path]::IsPathRooted($path)) {
        return $path
    }
    return Join-Path $repoRoot $path
}

$EvidencePath = Resolve-RepoPath $EvidencePath
$BaseEvidencePath = Resolve-RepoPath $BaseEvidencePath
$Engine2dEvidencePath = Resolve-RepoPath $Engine2dEvidencePath
$QemuReadbackPath = Resolve-RepoPath $QemuReadbackPath
$SimpleRdcPath = Resolve-RepoPath $SimpleRdcPath
$CaptureLogPath = Resolve-RepoPath $CaptureLogPath
$QemuRenderdocLogPath = Resolve-RepoPath $QemuRenderdocLogPath
$HostRenderdocLogPath = Resolve-RepoPath $HostRenderdocLogPath
$SimpleBinary = Resolve-RepoPath $SimpleBinary
$SimpleVulkanProbeWorkDir = Resolve-RepoPath $SimpleVulkanProbeWorkDir
$SimpleVulkanProbeEvidencePath = Resolve-RepoPath $SimpleVulkanProbeEvidencePath
$HostVulkanLogPath = Resolve-RepoPath $HostVulkanLogPath

if ([string]::IsNullOrWhiteSpace($SimpleVulkanProbeEvidencePath)) {
    $SimpleVulkanProbeEvidencePath = Join-Path $SimpleVulkanProbeWorkDir "evidence.env"
}
if ($RunSimpleVulkanProbe) {
    $probeScript = Join-Path $scriptDir "check-vulkan-engine2d-readback.ps1"
    if (Test-Path -LiteralPath $probeScript) {
        $probeArgs = @(
            "-NoProfile", "-ExecutionPolicy", "Bypass",
            "-File", $probeScript,
            "-SimpleBinary", $SimpleBinary,
            "-WorkDir", $SimpleVulkanProbeWorkDir,
            "-EvidencePath", $SimpleVulkanProbeEvidencePath,
            "-TimeoutSeconds", "$SimpleVulkanProbeTimeoutSeconds",
            "-MaxExistingSimpleProcesses", "$SimpleVulkanProbeMaxExistingSimpleProcesses"
        )
        if ($SimpleVulkanProbePreflightOnly) {
            $probeArgs += "-PreflightOnly"
        }
        if ($AllowHighSimpleProcessCount) {
            $probeArgs += "-AllowHighSimpleProcessCount"
        }
        & powershell @probeArgs
        $probeExit = $LASTEXITCODE
        Write-Output "simpleos_engine2d_direct_readback_probe_exit_code=$probeExit"
        $Engine2dEvidencePath = $SimpleVulkanProbeEvidencePath
    } else {
        Write-Output "simpleos_engine2d_direct_readback_probe_exit_code=missing-wrapper"
    }
}

$rows = [System.Collections.Generic.List[string]]::new()
if (-not [string]::IsNullOrWhiteSpace($BaseEvidencePath) -and (Test-Path -LiteralPath $BaseEvidencePath)) {
    Get-Content -LiteralPath $BaseEvidencePath | ForEach-Object {
        if (-not [string]::IsNullOrWhiteSpace($_)) {
            $rows.Add($_) | Out-Null
        }
    }
}

$source = Read-KeyValueFile $Engine2dEvidencePath
$qemuEntryPath = "examples/09_embedded/simple_os/arch/riscv64/desktop_service_entry.spl"
$baremetalCorePath = "src/os/compositor/engine2d_baremetal_rect_core.spl"
$virtioSurfacePath = "src/lib/gc_async_mut/gpu/engine2d/virtio_gpu_surface.spl"
$vulkanSessionPath = "src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl"
$qemuEntryFullPath = Join-Path $repoRoot $qemuEntryPath
$baremetalCoreFullPath = Join-Path $repoRoot $baremetalCorePath
$virtioSurfaceFullPath = Join-Path $repoRoot $virtioSurfacePath
$vulkanSessionFullPath = Join-Path $repoRoot $vulkanSessionPath
$sourceQemuEntryStatus = if (Test-FileContains $qemuEntryFullPath "rect_core_draw_rect_filled") { "pass" } else { "missing" }
$sourceBaremetalCoreStatus = if (Test-FileContains $baremetalCoreFullPath "gui_fill4") { "pass" } else { "missing" }
$sourceVirtioSurfaceStatus = if (Test-FileContains $virtioSurfaceFullPath "trait VirtioGpu2DSurface") { "pass" } else { "missing" }
$sourceVulkanSessionStatus = if (Test-FileContains $vulkanSessionFullPath "class VulkanSession") { "pass" } else { "missing" }
$sourceCurrentDrawPath = if ($sourceQemuEntryStatus -eq "pass") { "freestanding-engine2d-baremetal-core" } else { "unknown" }
$sourceTargetProcessingBackend = "vulkan"
$sourceBridgeAuditStatus = "blocked:desktop-service-not-wired-to-engine2d-baremetal-core"
if ($sourceQemuEntryStatus -ne "pass") {
    $sourceBridgeAuditStatus = "blocked:missing-qemu-desktop-service-engine2d-entry"
} elseif ($sourceBaremetalCoreStatus -ne "pass") {
    $sourceBridgeAuditStatus = "blocked:missing-baremetal-engine2d-core"
} elseif ($sourceVirtioSurfaceStatus -ne "pass") {
    $sourceBridgeAuditStatus = "blocked:missing-engine2d-virtio-surface-contract"
} elseif ($sourceVulkanSessionStatus -ne "pass") {
    $sourceBridgeAuditStatus = "blocked:missing-engine2d-vulkan-session"
} else {
    $sourceBridgeAuditStatus = "pass"
}
if ($RuntimeBackend -eq "") {
    $RuntimeBackend = Value-Or $source @(
        "simpleos_engine2d_runtime_backend",
        "vulkan_engine2d_readback_backend_name",
        "gui_web_2d_vulkan_simple_backend",
        "gui_web_2d_vulkan_simple_backend_status",
        "gui_web_2d_vulkan_simple_evidence_backend"
    ) "missing"
}
if ($RuntimeBackend -eq "pass") {
    $RuntimeBackend = "vulkan"
}
if ($VulkanDeviceName -eq "") {
    $VulkanDeviceName = Value-Or $source @(
        "simpleos_engine2d_vulkan_device_name",
        "gui_web_2d_vulkan_device",
        "vulkan_device_name"
    ) ""
}
if ($ViewportWidth -le 0) {
    $ViewportWidth = [int](Value-Or $source @("simpleos_engine2d_viewport_width", "simple_argb_width", "gui_web_2d_vulkan_simple_argb_width") "0")
    if ($ViewportWidth -le 0 -and (Value-Or $source @("vulkan_engine2d_readback_rect_pixels") "") -eq "256") {
        $ViewportWidth = 16
    }
}
if ($ViewportHeight -le 0) {
    $ViewportHeight = [int](Value-Or $source @("simpleos_engine2d_viewport_height", "simple_argb_height", "gui_web_2d_vulkan_simple_argb_height") "0")
    if ($ViewportHeight -le 0 -and (Value-Or $source @("vulkan_engine2d_readback_rect_pixels") "") -eq "256") {
        $ViewportHeight = 16
    }
}
if ($ReadbackChecksum -eq "") {
    $ReadbackChecksum = Value-Or $source @(
        "simpleos_engine2d_readback_checksum",
        "vulkan_engine2d_readback_rect_actual_checksum",
        "simple_argb_checksum",
        "gui_web_2d_vulkan_simple_argb_checksum"
    ) ""
}

$qemuReadbackStatus = Test-PpmNonblank $QemuReadbackPath
$qemuReadbackDimensions = Read-PpmDimensions $QemuReadbackPath
if ($ViewportWidth -le 0 -and $qemuReadbackDimensions.status -eq "pass") {
    $ViewportWidth = [int]$qemuReadbackDimensions.width
}
if ($ViewportHeight -le 0 -and $qemuReadbackDimensions.status -eq "pass") {
    $ViewportHeight = [int]$qemuReadbackDimensions.height
}
if ($ReadbackChecksum -eq "" -and $qemuReadbackStatus -eq "pass") {
    $ReadbackChecksum = Checksum-FileTail $QemuReadbackPath
}
$sourceUsability = Source-Evidence-Usability $source $RuntimeBackend $ReadbackChecksum
$engineReadbackNonblankStatus = if ($sourceUsability.status -eq "pass" -and $ReadbackChecksum -ne "") { "pass" } elseif ($ReadbackChecksum -ne "") { "blocked:source-evidence-not-usable" } else { "missing" }
$simple2dCommandStatus = if ($RuntimeBackend -eq "vulkan" -and $ReadbackChecksum -ne "") { "pass" } else { "missing" }
$runtimeBackendReason = Runtime-Backend-Reason $RuntimeBackend $source
$rdcMagic = Read-RdcMagic $SimpleRdcPath
$captureLogStatus = if (Test-FileNonEmpty $CaptureLogPath) { "pass" } else { "missing" }
$renderdocRuntimeBackend = if ($rdcMagic -eq "RDOC") { "vulkan" } else { "missing" }
$renderdocScene = if ($rdcMagic -eq "RDOC") { $SceneName } else { "" }
$renderdocArtifactReason = Renderdoc-Artifact-Reason $rdcMagic $captureLogStatus $renderdocRuntimeBackend $QemuRenderdocLogPath $HostRenderdocLogPath
$wmRenderdocLogCompareReason = Wm-Renderdoc-Log-Compare-Reason $QemuRenderdocLogPath $HostRenderdocLogPath
$hostProbeAttempted = if ($ProbeHostVulkan) { "true" } else { "false" }
$vulkanInfoStatus = "not-requested"
$vulkanInstanceVersion = ""
$vulkanDeviceName = ""
$sdkToolsStatus = "not-requested"
$chromeStatus = "not-requested"
$electronStatus = "not-requested"
$renderdocStatus = "not-requested"
$browserBackingStatus = "fail"
$browserBackingReason = "missing-focused-browser-backing"
$browserBackingMode = "focused-browser-backing-required"
$hostReadinessStatus = "not-requested"

if ($ProbeHostVulkan) {
    $hostLogDir = Split-Path -Parent $HostVulkanLogPath
    if (-not [string]::IsNullOrWhiteSpace($hostLogDir)) {
        New-Item -ItemType Directory -Force -Path $hostLogDir | Out-Null
    }
    $vulkanInfoPath = Command-Source-OrEmpty "vulkaninfo"
    if ($vulkanInfoPath -ne "") {
        try {
            $stdoutPath = "$HostVulkanLogPath.stdout"
            $stderrPath = "$HostVulkanLogPath.stderr"
            Remove-Item -LiteralPath $stdoutPath -Force -ErrorAction SilentlyContinue
            Remove-Item -LiteralPath $stderrPath -Force -ErrorAction SilentlyContinue
            $process = Start-Process -FilePath $vulkanInfoPath -ArgumentList @("--summary") -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath -NoNewWindow -Wait -PassThru
            $stdout = if (Test-Path -LiteralPath $stdoutPath) { Get-Content -Raw -LiteralPath $stdoutPath } else { "" }
            $stderr = if (Test-Path -LiteralPath $stderrPath) { Get-Content -Raw -LiteralPath $stderrPath } else { "" }
            $vulkanText = $stdout + "`r`n" + $stderr
            $vulkanText | Set-Content -Encoding ASCII -Path $HostVulkanLogPath
            Remove-Item -LiteralPath $stdoutPath -Force -ErrorAction SilentlyContinue
            Remove-Item -LiteralPath $stderrPath -Force -ErrorAction SilentlyContinue
            $vulkanInfoStatus = if ($process.ExitCode -eq 0) { "pass" } else { "blocked:vulkaninfo-exit-$($process.ExitCode)" }
            $vulkanInstanceVersion = First-Match-OrEmpty $vulkanText 'Vulkan Instance Version:\s*([^\r\n]+)'
            $vulkanDeviceName = First-Match-OrEmpty $vulkanText 'deviceName\s*=\s*([^\r\n]+)'
        } catch {
            $vulkanInfoStatus = "blocked:vulkaninfo-error"
            $_.Exception.Message | Set-Content -Encoding ASCII -Path $HostVulkanLogPath
        }
    } else {
        $vulkanInfoStatus = "missing"
        "vulkaninfo missing" | Set-Content -Encoding ASCII -Path $HostVulkanLogPath
    }
    $glslangStatus = Command-Status "glslangValidator"
    $spirvAsStatus = Command-Status "spirv-as"
    $dxcStatus = Command-Status "dxc"
    $sdkToolsStatus = if ($glslangStatus -eq "pass" -and $spirvAsStatus -eq "pass" -and $dxcStatus -eq "pass") { "pass" } else { "blocked:sdk-tools-missing" }
    $chromePath = "C:\Program Files\Google\Chrome\Application\chrome.exe"
    $chromeStatus = if (Test-Path -LiteralPath $chromePath) { "pass" } else { "missing" }
    $electronStatus = Command-Status "electron"
    $renderdocStatus = if ((Command-Status "renderdoccmd") -eq "pass" -or (Command-Status "qrenderdoc") -eq "pass") { "pass" } else { "missing" }
    if ($vulkanInfoStatus -eq "pass" -and $sdkToolsStatus -eq "pass" -and $chromeStatus -eq "pass" -and $electronStatus -eq "pass" -and $renderdocStatus -eq "pass") {
        $hostReadinessStatus = "host-ready-browser-simple-proof-required"
    } elseif ($vulkanInfoStatus -ne "pass") {
        $hostReadinessStatus = "blocked:vulkaninfo-missing-or-failed"
    } elseif ($sdkToolsStatus -ne "pass") {
        $hostReadinessStatus = "blocked:sdk-tools-missing"
    } elseif ($renderdocStatus -ne "pass") {
        $hostReadinessStatus = "blocked:renderdoc-tools-missing"
    } else {
        $hostReadinessStatus = "blocked:host-tools-incomplete"
    }
}

$evidenceDir = Split-Path -Parent $EvidencePath
if (-not [string]::IsNullOrWhiteSpace($evidenceDir)) {
    New-Item -ItemType Directory -Force -Path $evidenceDir | Out-Null
}

Write-Row $rows "simpleos_engine2d_renderdoc_wrapper" "check-simpleos-engine2d-renderdoc-evidence.ps1"
Write-Row $rows "simpleos_engine2d_source_evidence_path" "$Engine2dEvidencePath"
Write-Row $rows "simpleos_engine2d_source_evidence_status" $(if (Test-FileNonEmpty $Engine2dEvidencePath) { "pass" } else { "missing" })
Write-Row $rows "simpleos_engine2d_source_evidence_mode" (Value-Or $source @("gui_web_2d_vulkan_mode") "")
Write-Row $rows "simpleos_engine2d_source_simple_status" (Value-Or $source @("gui_web_2d_vulkan_simple_status") "")
Write-Row $rows "simpleos_engine2d_source_browser_backing_status" (Value-Or $source @("gui_web_2d_vulkan_browser_backing_status") "")
Write-Row $rows "simpleos_engine2d_direct_readback_status" (Value-Or $source @("vulkan_engine2d_readback_status") "")
Write-Row $rows "simpleos_engine2d_direct_readback_reason" (Value-Or $source @("vulkan_engine2d_readback_reason") "")
Write-Row $rows "simpleos_engine2d_direct_readback_exit_code" (Value-Or $source @("vulkan_engine2d_readback_exit_code") "")
Write-Row $rows "simpleos_engine2d_direct_readback_preflight_only" (Value-Or $source @("vulkan_engine2d_readback_preflight_only") "")
Write-Row $rows "simpleos_engine2d_direct_readback_existing_simple_process_count" (Value-Or $source @("vulkan_engine2d_readback_existing_simple_process_count") "")
Write-Row $rows "simpleos_engine2d_direct_readback_existing_simple_process_limit" (Value-Or $source @("vulkan_engine2d_readback_existing_simple_process_limit") "")
Write-Row $rows "simpleos_engine2d_source_evidence_usable_status" "$($sourceUsability.status)"
Write-Row $rows "simpleos_engine2d_source_evidence_usable_reason" "$($sourceUsability.reason)"
Write-Row $rows "simpleos_engine2d_source_qemu_entry_path" "$qemuEntryPath"
Write-Row $rows "simpleos_engine2d_source_qemu_entry_status" "$sourceQemuEntryStatus"
Write-Row $rows "simpleos_engine2d_source_baremetal_core_path" "$baremetalCorePath"
Write-Row $rows "simpleos_engine2d_source_baremetal_core_status" "$sourceBaremetalCoreStatus"
Write-Row $rows "simpleos_engine2d_source_virtio_surface_path" "$virtioSurfacePath"
Write-Row $rows "simpleos_engine2d_source_virtio_surface_status" "$sourceVirtioSurfaceStatus"
Write-Row $rows "simpleos_engine2d_source_vulkan_session_path" "$vulkanSessionPath"
Write-Row $rows "simpleos_engine2d_source_vulkan_session_status" "$sourceVulkanSessionStatus"
Write-Row $rows "simpleos_engine2d_source_current_draw_path" "$sourceCurrentDrawPath"
Write-Row $rows "simpleos_engine2d_source_target_processing_backend" "$sourceTargetProcessingBackend"
Write-Row $rows "simpleos_engine2d_source_bridge_audit_status" "$sourceBridgeAuditStatus"
Write-Row $rows "simpleos_windows_vulkan_host_probe_attempted" "$hostProbeAttempted"
Write-Row $rows "simpleos_windows_vulkan_host_log_path" "$HostVulkanLogPath"
Write-Row $rows "simpleos_windows_vulkaninfo_status" "$vulkanInfoStatus"
Write-Row $rows "simpleos_windows_vulkan_instance_version" "$vulkanInstanceVersion"
Write-Row $rows "simpleos_windows_vulkan_device_name" "$vulkanDeviceName"
Write-Row $rows "simpleos_windows_vulkan_sdk_tools_status" "$sdkToolsStatus"
Write-Row $rows "simpleos_windows_glslang_validator_status" $(if ($ProbeHostVulkan) { $glslangStatus } else { "not-requested" })
Write-Row $rows "simpleos_windows_spirv_as_status" $(if ($ProbeHostVulkan) { $spirvAsStatus } else { "not-requested" })
Write-Row $rows "simpleos_windows_dxc_status" $(if ($ProbeHostVulkan) { $dxcStatus } else { "not-requested" })
Write-Row $rows "simpleos_windows_chrome_status" "$chromeStatus"
Write-Row $rows "simpleos_windows_electron_status" "$electronStatus"
Write-Row $rows "simpleos_windows_renderdoc_tool_status" "$renderdocStatus"
Write-Row $rows "simpleos_windows_vulkan_host_readiness_status" "$hostReadinessStatus"
Write-Row $rows "gui_web_2d_vulkan_browser_backing_status" "$browserBackingStatus"
Write-Row $rows "gui_web_2d_vulkan_browser_backing_reason" "$browserBackingReason"
Write-Row $rows "gui_web_2d_vulkan_browser_backing_mode" "$browserBackingMode"
Write-Row $rows "simpleos_engine2d_bridge_profile" "qemu-riscv64-desktop"
Write-Row $rows "simpleos_engine2d_drawing_backend" "virtio_gpu"
Write-Row $rows "simpleos_engine2d_processing_backend" $(if ($RuntimeBackend -eq "vulkan") { "vulkan" } else { "$RuntimeBackend" })
Write-Row $rows "simpleos_engine2d_qemu_gpu_device" "virtio-gpu-pci,disable-modern=on,disable-legacy=off"
Write-Row $rows "simpleos_engine2d_runtime_backend" "$RuntimeBackend"
Write-Row $rows "simpleos_engine2d_runtime_backend_reason" "$runtimeBackendReason"
Write-Row $rows "simpleos_engine2d_scene" $(if ($RuntimeBackend -eq "vulkan") { $SceneName } else { "" })
Write-Row $rows "simpleos_simple2d_command_status" "$simple2dCommandStatus"
Write-Row $rows "simpleos_simple2d_command_path" "draw_ir-to-engine2d"
Write-Row $rows "simpleos_engine2d_device_readback_required" "true"
Write-Row $rows "simpleos_qemu_qmp_screendump_required" "true"
Write-Row $rows "simpleos_engine2d_vulkan_device_name" "$VulkanDeviceName"
Write-Row $rows "simpleos_engine2d_viewport_width" "$ViewportWidth"
Write-Row $rows "simpleos_engine2d_viewport_height" "$ViewportHeight"
Write-Row $rows "simpleos_engine2d_readback_checksum" "$ReadbackChecksum"
Write-Row $rows "simpleos_engine2d_readback_nonblank_status" "$engineReadbackNonblankStatus"
Write-Row $rows "simpleos_qemu_gpu_readback_status" $(if ($qemuReadbackStatus -eq "pass") { "pass" } else { "missing" })
Write-Row $rows "simpleos_qemu_gpu_readback_reason" "$qemuReadbackStatus"
Write-Row $rows "simpleos_qemu_gpu_readback_path" "$QemuReadbackPath"
Write-Row $rows "simpleos_qemu_gpu_readback_width" "$($qemuReadbackDimensions.width)"
Write-Row $rows "simpleos_qemu_gpu_readback_height" "$($qemuReadbackDimensions.height)"
Write-Row $rows "simpleos_qemu_gpu_readback_dimensions_status" "$($qemuReadbackDimensions.status)"

Write-Row $rows "simpleos_renderdoc_capture_mode" "capture-simple"
Write-Row $rows "simpleos_renderdoc_rdc_path" "$SimpleRdcPath"
Write-Row $rows "simpleos_renderdoc_rdc_magic" "$rdcMagic"
Write-Row $rows "simpleos_renderdoc_rdc_magic_status" $(if ($rdcMagic -eq "RDOC") { "pass" } else { "missing" })
Write-Row $rows "simpleos_renderdoc_rdc_status" $(if ($rdcMagic -eq "RDOC") { "pass" } else { "missing" })
Write-Row $rows "simpleos_renderdoc_rdc_size_bytes" (Get-FileSizeText $SimpleRdcPath)
Write-Row $rows "simpleos_renderdoc_capture_log_path" "$CaptureLogPath"
Write-Row $rows "simpleos_renderdoc_capture_log_status" "$captureLogStatus"
Write-Row $rows "simpleos_renderdoc_simple_runtime_backend" "$renderdocRuntimeBackend"
Write-Row $rows "simpleos_renderdoc_simple_scene" "$renderdocScene"
Write-Row $rows "simpleos_renderdoc_helper_status" "$captureLogStatus"
Write-Row $rows "simpleos_renderdoc_qemu_wm_log_path" $(if (Test-FileNonEmpty $QemuRenderdocLogPath) { $QemuRenderdocLogPath } else { "" })
Write-Row $rows "simpleos_renderdoc_host_wm_log_path" $(if (Test-FileNonEmpty $HostRenderdocLogPath) { $HostRenderdocLogPath } else { "" })
Write-Row $rows "simpleos_renderdoc_artifact_blocker_reason" "$renderdocArtifactReason"
Write-Row $rows "simpleos_wm_renderdoc_log_compare_reason" "$wmRenderdocLogCompareReason"
Write-Row $rows "simpleos_wm_compare_scene" "simpleos-desktop-four-windows"

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
$rows | ForEach-Object { Write-Output $_ }
Write-Output "simpleos_engine2d_renderdoc_evidence_path=$EvidencePath"

if ($RuntimeBackend -eq "vulkan" -and
    $simple2dCommandStatus -eq "pass" -and
    $VulkanDeviceName -ne "" -and
    $ViewportWidth -gt 0 -and
    $ViewportHeight -gt 0 -and
    $ReadbackChecksum -ne "" -and
    $engineReadbackNonblankStatus -eq "pass" -and
    $qemuReadbackStatus -eq "pass" -and
    $rdcMagic -eq "RDOC" -and
    $captureLogStatus -eq "pass" -and
    (Test-FileNonEmpty $QemuRenderdocLogPath) -and
    (Test-FileNonEmpty $HostRenderdocLogPath)) {
    exit 0
}
exit 1
