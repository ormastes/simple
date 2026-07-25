param(
    [string]$EvidencePath = "build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env",
    [string]$ArtifactDir = "build/simpleos_multiconfig_live_evidence",
    [string]$QemuArtifactDir = "build/os/systest/qemu-riscv64-desktop",
    [string]$QemuEvidencePath = "",
    [string]$FpgaEvidencePath = "",
    [string]$FpgaSerialPortInventoryPath = "",
    [string]$WmEvidencePath = "",
    [string]$Engine2dEvidencePath = "",
    [string]$SimpleProcessInventoryEvidencePath = "",
    [switch]$RunLiveBoot,
    [switch]$KeepQemu,
    [switch]$AttemptBuild,
    [switch]$ProbeHostVulkan,
    [switch]$RunSimpleVulkanProbe,
    [int]$SimpleVulkanProbeTimeoutSeconds = 180,
    [int]$SimpleVulkanProbeMaxExistingSimpleProcesses = 128,
    [switch]$SimpleVulkanProbePreflightOnly,
    [switch]$RunSimpleProcessInventory,
    [int]$SimpleProcessInventoryLimit = 128,
    [int]$SimpleProcessInventorySampleLimit = 20,
    [switch]$AllowHighSimpleProcessCount,
    [switch]$AttemptHostWmCapture,
    [int]$HostCaptureTimeoutSeconds = 20,
    [int]$BootTimeoutSeconds = 60,
    [int]$QmpPort = 4444,
    [string]$SimpleBinary = "src\compiler_rust\target\debug\simple.exe",
    [string]$BuildBackend = $env:SIMPLE_OS_BUILD_BACKEND,
    [string]$BuildCc = $env:CC,
    [string]$NestedSimpleBinary = "",
    [switch]$BuildDesktopServiceKernel,
    [switch]$BuildFpgaSerialKernel,
    [switch]$ProbeFpgaSerialPorts,
    [switch]$CaptureFpgaSerial,
    [int]$FpgaSerialCaptureTimeoutSeconds = 20,
    [int]$FpgaSerialCaptureBaudRate = 115200,
    [string]$FpgaSerialDevice = $env:SIMPLEOS_FPGA_SERIAL_DEVICE,
    [string]$FpgaSerialLogPath = $env:SIMPLEOS_FPGA_SERIAL_LOG,
    [switch]$BuildDiskImage,
    [string]$DiskImageBuilderCompiler = "",
    [switch]$SkipAggregate
)

$ErrorActionPreference = "Stop"

function Write-Or-ReplaceRow($rows, [string]$key, [string]$value) {
    $prefix = "$key="
    for ($i = $rows.Count - 1; $i -ge 0; $i--) {
        if ($rows[$i].StartsWith($prefix)) {
            $rows.RemoveAt($i)
        }
    }
    $rows.Add("$key=$value") | Out-Null
}

function Add-Or-ReplaceRows([string]$path, [hashtable]$newRows) {
    $rows = [System.Collections.Generic.List[string]]::new()
    if (Test-Path -LiteralPath $path) {
        Get-Content -LiteralPath $path | ForEach-Object {
            if (-not [string]::IsNullOrWhiteSpace($_)) {
                $rows.Add($_) | Out-Null
            }
        }
    }
    foreach ($key in $newRows.Keys) {
        Write-Or-ReplaceRow $rows $key ([string]$newRows[$key])
    }
    $rows | Set-Content -Encoding ASCII -Path $path
}

function Merge-EvidenceRowsFromPath([string]$targetPath, [string]$sourcePath) {
    if ([string]::IsNullOrWhiteSpace($sourcePath) -or -not (Test-Path -LiteralPath $sourcePath)) {
        return
    }
    $newRows = @{}
    Get-Content -LiteralPath $sourcePath | ForEach-Object {
        $line = $_.Trim()
        if ($line -ne "" -and $line.Contains("=")) {
            $idx = $line.IndexOf("=")
            $key = $line.Substring(0, $idx)
            $value = $line.Substring($idx + 1)
            $newRows[$key] = $value
        }
    }
    if ($newRows.Count -gt 0) {
        Add-Or-ReplaceRows $targetPath $newRows
    }
}

function Invoke-EvidenceScript([string]$scriptPath, [string[]]$arguments) {
    $powershellCommand = Get-Command powershell -ErrorAction SilentlyContinue
    if (-not $powershellCommand) {
        Write-Output "simpleos_multiconfig_windows_wrapper_blocker=missing-powershell"
        return 127
    }
    $processArgs = @("-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $scriptPath) + $arguments
    $process = Start-Process -FilePath $powershellCommand.Source -ArgumentList $processArgs -WorkingDirectory $repoRoot -NoNewWindow -Wait -PassThru
    return $process.ExitCode
}

$scriptDir = Split-Path -Parent $PSCommandPath
$repoRoot = Resolve-Path -LiteralPath (Join-Path $scriptDir "..\..")
Set-Location $repoRoot

if ([string]::IsNullOrWhiteSpace($QemuEvidencePath)) {
    $QemuEvidencePath = Join-Path $ArtifactDir "qemu-rv64-desktop.env"
}
if ([string]::IsNullOrWhiteSpace($FpgaEvidencePath)) {
    $FpgaEvidencePath = Join-Path $ArtifactDir "fpga-rv64-serial.env"
}
if ([string]::IsNullOrWhiteSpace($FpgaSerialPortInventoryPath)) {
    $FpgaSerialPortInventoryPath = Join-Path $ArtifactDir "fpga-rv64-serial-ports.env"
}
if ([string]::IsNullOrWhiteSpace($WmEvidencePath)) {
    $WmEvidencePath = Join-Path $ArtifactDir "wm-host-compare.env"
}
if ([string]::IsNullOrWhiteSpace($Engine2dEvidencePath)) {
    $Engine2dEvidencePath = $EvidencePath
}
if ([string]::IsNullOrWhiteSpace($SimpleProcessInventoryEvidencePath)) {
    $SimpleProcessInventoryEvidencePath = Join-Path $ArtifactDir "simple-process-inventory.env"
}

New-Item -ItemType Directory -Force -Path $ArtifactDir | Out-Null
$finalDir = Split-Path -Parent $EvidencePath
if (-not [string]::IsNullOrWhiteSpace($finalDir)) {
    New-Item -ItemType Directory -Force -Path $finalDir | Out-Null
}

$inventoryExit = ""
if ($RunSimpleProcessInventory) {
    $inventoryArgs = @(
        "-EvidencePath", $SimpleProcessInventoryEvidencePath,
        "-ProcessLimit", "$SimpleProcessInventoryLimit",
        "-MaxSample", "$SimpleProcessInventorySampleLimit"
    )
    $inventoryExit = Invoke-EvidenceScript (Join-Path $scriptDir "check-simple-process-inventory.ps1") $inventoryArgs
}

$qemuArgs = @(
    "-EvidencePath", $QemuEvidencePath,
    "-ArtifactDir", $QemuArtifactDir,
    "-BootTimeoutSeconds", "$BootTimeoutSeconds",
    "-QmpPort", "$QmpPort"
)
if ($RunLiveBoot) {
    $qemuArgs += "-RunLiveBoot"
}
if ($KeepQemu) {
    $qemuArgs += "-KeepQemu"
}
if ($AttemptBuild) {
    $qemuArgs += "-AttemptBuild"
    $qemuArgs += "-BuildSimpleBinary"
    $qemuArgs += $SimpleBinary
    if (-not [string]::IsNullOrWhiteSpace($BuildBackend)) {
        $qemuArgs += "-BuildBackend"
        $qemuArgs += $BuildBackend
    }
    if (-not [string]::IsNullOrWhiteSpace($BuildCc)) {
        $qemuArgs += "-BuildCc"
        $qemuArgs += $BuildCc
    }
    if (-not [string]::IsNullOrWhiteSpace($NestedSimpleBinary)) {
        $qemuArgs += "-NestedSimpleBinary"
        $qemuArgs += $NestedSimpleBinary
    }
}
if ($BuildDesktopServiceKernel) {
    $qemuArgs += "-BuildDesktopServiceKernel"
    $qemuArgs += "-BuildSimpleBinary"
    $qemuArgs += $SimpleBinary
    if (-not [string]::IsNullOrWhiteSpace($BuildBackend)) {
        $qemuArgs += "-BuildBackend"
        $qemuArgs += $BuildBackend
    }
    if (-not [string]::IsNullOrWhiteSpace($BuildCc)) {
        $qemuArgs += "-BuildCc"
        $qemuArgs += $BuildCc
    }
}
if ($BuildDiskImage) {
    $qemuArgs += "-BuildDiskImage"
    if (-not [string]::IsNullOrWhiteSpace($DiskImageBuilderCompiler)) {
        $qemuArgs += "-DiskImageBuilderCompiler"
        $qemuArgs += $DiskImageBuilderCompiler
    } elseif (-not [string]::IsNullOrWhiteSpace($BuildCc)) {
        $qemuArgs += "-DiskImageBuilderCompiler"
        $qemuArgs += $BuildCc
    }
}

$qemuExit = Invoke-EvidenceScript (Join-Path $scriptDir "check-simpleos-qemu-rv64-desktop-evidence.ps1") $qemuArgs
$fpgaArgs = @(
    "-EvidencePath", $FpgaEvidencePath,
    "-BaseEvidencePath", $QemuEvidencePath
)
if ($BuildFpgaSerialKernel) {
    $fpgaArgs += "-BuildFpgaSerialKernel"
    $fpgaArgs += "-BuildSimpleBinary"
    $fpgaArgs += $SimpleBinary
    if (-not [string]::IsNullOrWhiteSpace($BuildBackend)) {
        $fpgaArgs += "-BuildBackend"
        $fpgaArgs += $BuildBackend
    }
    if (-not [string]::IsNullOrWhiteSpace($BuildCc)) {
        $fpgaArgs += "-BuildCc"
        $fpgaArgs += $BuildCc
    }
}
if ($ProbeFpgaSerialPorts) {
    $fpgaArgs += "-ProbeSerialPorts"
    $fpgaArgs += "-SerialPortInventoryPath"
    $fpgaArgs += $FpgaSerialPortInventoryPath
}
if ($CaptureFpgaSerial) {
    $fpgaArgs += "-CaptureSerial"
    $fpgaArgs += "-CaptureTimeoutSeconds"
    $fpgaArgs += "$FpgaSerialCaptureTimeoutSeconds"
    $fpgaArgs += "-CaptureBaudRate"
    $fpgaArgs += "$FpgaSerialCaptureBaudRate"
}
if (-not [string]::IsNullOrWhiteSpace($FpgaSerialDevice)) {
    $fpgaArgs += "-SerialDevice"
    $fpgaArgs += $FpgaSerialDevice
}
if (-not [string]::IsNullOrWhiteSpace($FpgaSerialLogPath)) {
    $fpgaArgs += "-SerialLogPath"
    $fpgaArgs += $FpgaSerialLogPath
}
$fpgaExit = Invoke-EvidenceScript (Join-Path $scriptDir "check-simpleos-fpga-rv64-serial-evidence.ps1") $fpgaArgs
$wmArgs = @(
    "-EvidencePath", $WmEvidencePath,
    "-BaseEvidencePath", $FpgaEvidencePath
)
if ($AttemptHostWmCapture) {
    $wmArgs += "-AttemptHostWmCapture"
    $wmArgs += "-SimpleBinary"
    $wmArgs += $SimpleBinary
    $wmArgs += "-HostCaptureTimeoutSeconds"
    $wmArgs += "$HostCaptureTimeoutSeconds"
}
$wmExit = Invoke-EvidenceScript (Join-Path $scriptDir "check-simpleos-wm-host-compare-evidence.ps1") $wmArgs
$engineArgs = @(
    "-EvidencePath", $Engine2dEvidencePath,
    "-BaseEvidencePath", $WmEvidencePath
)
if ($ProbeHostVulkan) {
    $engineArgs += "-ProbeHostVulkan"
}
if ($RunSimpleVulkanProbe) {
    $engineArgs += "-RunSimpleVulkanProbe"
    $engineArgs += "-SimpleBinary"
    $engineArgs += $SimpleBinary
    $engineArgs += "-SimpleVulkanProbeTimeoutSeconds"
    $engineArgs += "$SimpleVulkanProbeTimeoutSeconds"
    $engineArgs += "-SimpleVulkanProbeMaxExistingSimpleProcesses"
    $engineArgs += "$SimpleVulkanProbeMaxExistingSimpleProcesses"
    if ($SimpleVulkanProbePreflightOnly) {
        $engineArgs += "-SimpleVulkanProbePreflightOnly"
    }
    if ($AllowHighSimpleProcessCount) {
        $engineArgs += "-AllowHighSimpleProcessCount"
    }
}
$engineExit = Invoke-EvidenceScript (Join-Path $scriptDir "check-simpleos-engine2d-renderdoc-evidence.ps1") $engineArgs

if ($Engine2dEvidencePath -ne $EvidencePath) {
    Copy-Item -LiteralPath $Engine2dEvidencePath -Destination $EvidencePath -Force
}
if ($RunSimpleProcessInventory) {
    Merge-EvidenceRowsFromPath $EvidencePath $SimpleProcessInventoryEvidencePath
}

$statusRows = @{
    "simpleos_multiconfig_windows_wrapper" = "check-simpleos-multiconfig-live-evidence.ps1"
    "simpleos_multiconfig_windows_wrapper_artifact_dir" = $ArtifactDir
    "simpleos_multiconfig_windows_wrapper_qemu_evidence_path" = $QemuEvidencePath
    "simpleos_multiconfig_windows_wrapper_fpga_evidence_path" = $FpgaEvidencePath
    "simpleos_multiconfig_windows_wrapper_fpga_serial_port_inventory_path" = $FpgaSerialPortInventoryPath
    "simpleos_multiconfig_windows_wrapper_wm_evidence_path" = $WmEvidencePath
    "simpleos_multiconfig_windows_wrapper_engine2d_evidence_path" = $Engine2dEvidencePath
    "simpleos_multiconfig_windows_wrapper_simple_process_inventory_evidence_path" = $SimpleProcessInventoryEvidencePath
    "simpleos_multiconfig_windows_wrapper_simple_process_inventory_exit_code" = "$inventoryExit"
    "simpleos_multiconfig_windows_wrapper_qemu_exit_code" = "$qemuExit"
    "simpleos_multiconfig_windows_wrapper_fpga_exit_code" = "$fpgaExit"
    "simpleos_multiconfig_windows_wrapper_wm_exit_code" = "$wmExit"
    "simpleos_multiconfig_windows_wrapper_engine2d_exit_code" = "$engineExit"
}
Add-Or-ReplaceRows $EvidencePath $statusRows

Write-Output "simpleos_multiconfig_windows_wrapper_evidence_path=$EvidencePath"
Write-Output "simpleos_multiconfig_windows_wrapper_qemu_exit_code=$qemuExit"
Write-Output "simpleos_multiconfig_windows_wrapper_fpga_exit_code=$fpgaExit"
Write-Output "simpleos_multiconfig_windows_wrapper_wm_exit_code=$wmExit"
Write-Output "simpleos_multiconfig_windows_wrapper_engine2d_exit_code=$engineExit"

if ($SkipAggregate) {
    Write-Output "simpleos_multiconfig_windows_wrapper_aggregate_status=skipped"
    exit 1
}

if (-not (Test-Path -LiteralPath $SimpleBinary)) {
    Add-Or-ReplaceRows $EvidencePath @{
        "simpleos_multiconfig_windows_wrapper_aggregate_status" = "blocked:missing-simple-debug-binary"
        "simpleos_multiconfig_windows_wrapper_simple_binary" = $SimpleBinary
    }
    Write-Output "simpleos_multiconfig_windows_wrapper_aggregate_status=blocked:missing-simple-debug-binary"
    exit 1
}

$env:SIMPLE_LIB = "src"
Push-Location $repoRoot
try {
    & $SimpleBinary scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence $EvidencePath --mode=interpreter
    $aggregateExit = $LASTEXITCODE
} finally {
    Pop-Location
}

Add-Or-ReplaceRows $EvidencePath @{
    "simpleos_multiconfig_windows_wrapper_aggregate_status" = $(if ($aggregateExit -eq 0) { "pass" } else { "blocked" })
    "simpleos_multiconfig_windows_wrapper_aggregate_exit_code" = "$aggregateExit"
    "simpleos_multiconfig_windows_wrapper_simple_binary" = $SimpleBinary
}
Write-Output "simpleos_multiconfig_windows_wrapper_aggregate_exit_code=$aggregateExit"
exit $aggregateExit
