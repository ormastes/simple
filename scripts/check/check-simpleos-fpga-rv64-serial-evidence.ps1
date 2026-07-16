param(
    [string]$EvidencePath = "build/simpleos_multiconfig_live_evidence/fpga-rv64-serial.env",
    [string]$BaseEvidencePath = "",
    [string]$BoardProfile = "fpga-riscv64-serial",
    [string]$SerialDevice = $env:SIMPLEOS_FPGA_SERIAL_DEVICE,
    [string]$SerialLogPath = $env:SIMPLEOS_FPGA_SERIAL_LOG,
    [string]$BootMarker = "SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT",
    [string]$ExpectedEntry = "examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl",
    [string]$ExpectedKernelPath = "build/os/simpleos_riscv64_fpga.elf",
    [switch]$BuildFpgaSerialKernel,
    [string]$BuildSimpleBinary = "src\compiler_rust\target\debug\simple.exe",
    [string]$BuildBackend = $env:SIMPLE_OS_BUILD_BACKEND,
    [string]$BuildCc = $env:CC,
    [string]$BuildLogPath = "",
    [string]$ToolchainStatus = $env:SIMPLEOS_FPGA_TOOLCHAIN_STATUS,
    [string]$BitstreamPath = $env:SIMPLEOS_FPGA_BITSTREAM,
    [string]$BitstreamStatus = $env:SIMPLEOS_FPGA_BITSTREAM_STATUS,
    [switch]$ProbeSerialPorts,
    [string]$SerialPortInventoryPath = "",
    [switch]$CaptureSerial,
    [int]$CaptureTimeoutSeconds = 20,
    [int]$CaptureBaudRate = 115200
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

function Test-FileNonEmpty([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return $false
    }
    return ((Get-Item -LiteralPath $path).Length -gt 0)
}

function Read-BootMarker([string]$path, [string]$marker) {
    if (-not (Test-FileNonEmpty $path)) {
        return ""
    }
    $text = Read-TextFileOrEmpty $path
    if ($text.Contains($marker)) {
        return $marker
    }
    return ""
}

function Read-TextFileOrEmpty([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return ""
    }
    try {
        $stream = [System.IO.FileStream]::new(
            (Resolve-Path -LiteralPath $path).Path,
            [System.IO.FileMode]::Open,
            [System.IO.FileAccess]::Read,
            [System.IO.FileShare]::ReadWrite -bor [System.IO.FileShare]::Delete
        )
        try {
            $reader = [System.IO.StreamReader]::new($stream, [System.Text.Encoding]::UTF8, $true)
            try {
                return $reader.ReadToEnd()
            } finally {
                $reader.Dispose()
            }
        } finally {
            if ($stream) {
                $stream.Dispose()
            }
        }
    } catch {
        return ""
    }
}

function Get-SerialPortNames() {
    try {
        $ports = [System.IO.Ports.SerialPort]::GetPortNames()
        if ($null -eq $ports) {
            $ports = @()
        }
        return [pscustomobject]@{
            Ok = $true
            Ports = @($ports | Sort-Object)
        }
    } catch {
        return [pscustomobject]@{
            Ok = $false
            Ports = @()
        }
    }
}

function Capture-SerialLog([string]$device, [string]$path, [int]$baudRate, [int]$timeoutSeconds, [string]$marker) {
    if ([string]::IsNullOrWhiteSpace($device)) {
        return [pscustomobject]@{
            Status = "blocked:missing-serial-device"
            Reason = "missing-serial-device"
            Bytes = 0
            MarkerSeen = "false"
        }
    }
    if ([string]::IsNullOrWhiteSpace($path)) {
        return [pscustomobject]@{
            Status = "blocked:missing-serial-log-path"
            Reason = "missing-serial-log-path"
            Bytes = 0
            MarkerSeen = "false"
        }
    }
    $dir = Split-Path -Parent $path
    if (-not [string]::IsNullOrWhiteSpace($dir)) {
        New-Item -ItemType Directory -Force -Path $dir | Out-Null
    }
    $port = $null
    $writer = $null
    $bytesSeen = 0
    $textSeen = ""
    try {
        $port = [System.IO.Ports.SerialPort]::new($device, $baudRate, [System.IO.Ports.Parity]::None, 8, [System.IO.Ports.StopBits]::One)
        $port.ReadTimeout = 250
        $port.WriteTimeout = 250
        $port.Open()
        $writer = [System.IO.StreamWriter]::new($path, $false, [System.Text.Encoding]::ASCII)
        $deadline = [DateTime]::UtcNow.AddSeconds($timeoutSeconds)
        while ([DateTime]::UtcNow -lt $deadline) {
            try {
                $chunk = $port.ReadExisting()
                if (-not [string]::IsNullOrEmpty($chunk)) {
                    $writer.Write($chunk)
                    $writer.Flush()
                    $bytesSeen += [System.Text.Encoding]::ASCII.GetByteCount($chunk)
                    $textSeen += $chunk
                    if ($textSeen.Contains($marker)) {
                        return [pscustomobject]@{
                            Status = "pass"
                            Reason = "boot-marker-seen"
                            Bytes = $bytesSeen
                            MarkerSeen = "true"
                        }
                    }
                    if ($textSeen.Length -gt 4096) {
                        $textSeen = $textSeen.Substring($textSeen.Length - 4096)
                    }
                }
            } catch [System.TimeoutException] {
            }
            Start-Sleep -Milliseconds 100
        }
        return [pscustomobject]@{
            Status = "blocked:timeout"
            Reason = "boot-marker-timeout"
            Bytes = $bytesSeen
            MarkerSeen = "false"
        }
    } catch {
        return [pscustomobject]@{
            Status = "blocked:serial-open-or-read-failed"
            Reason = ($_.Exception.GetType().Name)
            Bytes = $bytesSeen
            MarkerSeen = "false"
        }
    } finally {
        if ($writer) {
            $writer.Dispose()
        }
        if ($port) {
            if ($port.IsOpen) {
                $port.Close()
            }
            $port.Dispose()
        }
    }
}

$scriptDir = Split-Path -Parent $PSCommandPath
$repoRoot = Resolve-Path -LiteralPath (Join-Path $scriptDir "..\..")
Set-Location $repoRoot

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
$SerialLogPath = Resolve-RepoPath $SerialLogPath
$ExpectedEntry = Resolve-RepoPath $ExpectedEntry
$ExpectedKernelPath = Resolve-RepoPath $ExpectedKernelPath
$BuildSimpleBinary = Resolve-RepoPath $BuildSimpleBinary
$BuildLogPath = Resolve-RepoPath $BuildLogPath
$SerialPortInventoryPath = Resolve-RepoPath $SerialPortInventoryPath

$rows = [System.Collections.Generic.List[string]]::new()
if (-not [string]::IsNullOrWhiteSpace($BaseEvidencePath) -and (Test-Path -LiteralPath $BaseEvidencePath)) {
    Get-Content -LiteralPath $BaseEvidencePath | ForEach-Object {
        if (-not [string]::IsNullOrWhiteSpace($_)) {
            $rows.Add($_) | Out-Null
        }
    }
}

$evidenceDir = Split-Path -Parent $EvidencePath
if (-not [string]::IsNullOrWhiteSpace($evidenceDir)) {
    New-Item -ItemType Directory -Force -Path $evidenceDir | Out-Null
}
if ([string]::IsNullOrWhiteSpace($BuildLogPath)) {
    $BuildLogPath = Join-Path $evidenceDir "fpga-rv64-serial-build.log"
}
if ([string]::IsNullOrWhiteSpace($SerialPortInventoryPath)) {
    $SerialPortInventoryPath = Join-Path $evidenceDir "fpga-rv64-serial-ports.env"
}
if ($CaptureSerial -and [string]::IsNullOrWhiteSpace($SerialLogPath)) {
    $SerialLogPath = Join-Path $evidenceDir "fpga-rv64-serial-capture.log"
}

$buildAttempted = $false
$buildStatus = "not-requested"
$buildExitCode = ""
$buildCommand = "$BuildSimpleBinary native-build --source build/os/generated --source examples/09_embedded/simple_os/arch/riscv64 --backend cranelift --opt-level=aggressive --log on --timeout 180 --entry-closure --entry $ExpectedEntry --target riscv64-unknown-none -o $ExpectedKernelPath --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld"

if ($BuildFpgaSerialKernel) {
    $buildAttempted = $true
    if ([string]::IsNullOrWhiteSpace($BuildSimpleBinary) -or -not (Test-Path -LiteralPath $BuildSimpleBinary)) {
        $buildStatus = "blocked:missing-simple-build-binary"
    } elseif ([string]::IsNullOrWhiteSpace($BuildCc) -or -not (Test-Path -LiteralPath $BuildCc)) {
        $buildStatus = "blocked:missing-build-cc"
    } elseif (-not (Test-Path -LiteralPath $ExpectedEntry)) {
        $buildStatus = "blocked:missing-fpga-serial-entry"
    } else {
        $oldBackend = $env:SIMPLE_OS_BUILD_BACKEND
        $oldSimpleLib = $env:SIMPLE_LIB
        $oldCc = $env:CC
        try {
            $backend = $(if ([string]::IsNullOrWhiteSpace($BuildBackend)) { "cranelift" } else { $BuildBackend })
            $env:SIMPLE_OS_BUILD_BACKEND = $backend
            $env:SIMPLE_LIB = "src"
            $env:CC = $BuildCc
            $stdoutPath = "$BuildLogPath.stdout"
            $stderrPath = "$BuildLogPath.stderr"
            Remove-Item -LiteralPath $stdoutPath, $stderrPath, $BuildLogPath -Force -ErrorAction SilentlyContinue
            $args = @(
                "native-build",
                "--source", "build/os/generated",
                "--source", "examples/09_embedded/simple_os/arch/riscv64",
                "--backend", $backend,
                "--opt-level=aggressive",
                "--log", "on",
                "--timeout", "180",
                "--entry-closure",
                "--entry", $ExpectedEntry,
                "--target", "riscv64-unknown-none",
                "-o", $ExpectedKernelPath,
                "--linker-script", "examples/09_embedded/simple_os/arch/riscv64/linker.ld"
            )
            $process = Start-Process -FilePath $BuildSimpleBinary -ArgumentList $args -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath -NoNewWindow -Wait -PassThru
            $buildExitCode = "$($process.ExitCode)"
            $stdout = if (Test-Path -LiteralPath $stdoutPath) { Get-Content -Raw -LiteralPath $stdoutPath } else { "" }
            $stderr = if (Test-Path -LiteralPath $stderrPath) { Get-Content -Raw -LiteralPath $stderrPath } else { "" }
            ($stdout + "`r`n" + $stderr) | Set-Content -Encoding ASCII -Path $BuildLogPath
            Remove-Item -LiteralPath $stdoutPath, $stderrPath -Force -ErrorAction SilentlyContinue
            if ($process.ExitCode -eq 0 -and (Test-FileNonEmpty $ExpectedKernelPath)) {
                $buildStatus = "pass"
            } else {
                $buildStatus = "blocked:fpga-serial-build-exit-$($process.ExitCode)"
            }
        } catch {
            $buildStatus = "blocked:fpga-serial-build-launch-failed"
        } finally {
            if ($null -eq $oldBackend) { Remove-Item Env:SIMPLE_OS_BUILD_BACKEND -ErrorAction SilentlyContinue } else { $env:SIMPLE_OS_BUILD_BACKEND = $oldBackend }
            if ($null -eq $oldSimpleLib) { Remove-Item Env:SIMPLE_LIB -ErrorAction SilentlyContinue } else { $env:SIMPLE_LIB = $oldSimpleLib }
            if ($null -eq $oldCc) { Remove-Item Env:CC -ErrorAction SilentlyContinue } else { $env:CC = $oldCc }
        }
    }
}

$serialCaptureAttempted = if ($CaptureSerial) { "true" } else { "false" }
$serialCaptureStatus = "not-requested"
$serialCaptureReason = "not-requested"
$serialCaptureBytes = ""
$serialCaptureMarkerSeen = "false"
if ($CaptureSerial) {
    $capture = Capture-SerialLog $SerialDevice $SerialLogPath $CaptureBaudRate $CaptureTimeoutSeconds $BootMarker
    $serialCaptureStatus = $capture.Status
    $serialCaptureReason = $capture.Reason
    $serialCaptureBytes = "$($capture.Bytes)"
    $serialCaptureMarkerSeen = $capture.MarkerSeen
}

$serialDeviceStatus = if ([string]::IsNullOrWhiteSpace($SerialDevice)) { "missing" } else { "pass" }
$serialLogText = Read-TextFileOrEmpty $SerialLogPath
$bootMarkerSeen = Read-BootMarker $SerialLogPath $BootMarker
$bootMarkerStatus = if ($bootMarkerSeen -ne "") { "pass" } else { "missing" }
$rv64BootMarkerStatus = if ($serialLogText.Contains("SimpleOS RV64 boot OK")) { "pass" } else { "missing" }
$testPassedMarkerStatus = if ($serialLogText.Contains("TEST PASSED")) { "pass" } else { "missing" }
$uartTerminalStatus = if ($serialDeviceStatus -eq "pass" -and $bootMarkerStatus -eq "pass") { "pass" } else { "blocked" }
$serialPortProbeAttempted = if ($ProbeSerialPorts) { "true" } else { "false" }
$serialPortProbeStatus = "not-requested"
$serialPortProbeCount = ""
$serialPortProbePorts = ""
$serialDeviceCandidateStatus = if ([string]::IsNullOrWhiteSpace($SerialDevice)) { "not-requested" } else { "not-probed" }
if ($ProbeSerialPorts) {
    $serialPortProbe = Get-SerialPortNames
    $serialPorts = @($serialPortProbe.Ports)
    if (-not $serialPortProbe.Ok) {
        $serialPortProbeStatus = "blocked:probe-error"
        $serialPortProbeCount = "0"
        $serialPortProbePorts = ""
        if (-not [string]::IsNullOrWhiteSpace($SerialDevice)) {
            $serialDeviceCandidateStatus = "unknown:probe-error"
        }
    } else {
        $serialPortProbeCount = "$($serialPorts.Count)"
        $serialPortProbePorts = [string]::Join(";", $serialPorts)
        $serialPortProbeStatus = if ($serialPorts.Count -gt 0) { "pass" } else { "missing" }
        if ([string]::IsNullOrWhiteSpace($SerialDevice)) {
            $serialDeviceCandidateStatus = "not-requested"
        } elseif ($serialPorts -contains $SerialDevice) {
            $serialDeviceCandidateStatus = "present"
        } else {
            $serialDeviceCandidateStatus = "missing"
        }
    }
}

if ([string]::IsNullOrWhiteSpace($ToolchainStatus)) {
    $ToolchainStatus = "missing"
}

if ([string]::IsNullOrWhiteSpace($BitstreamStatus)) {
    $BitstreamStatus = if (Test-FileNonEmpty $BitstreamPath) { "pass" } else { "missing" }
}

Write-Row $rows "simpleos_fpga_serial_wrapper" "check-simpleos-fpga-rv64-serial-evidence.ps1"
Write-Row $rows "simpleos_fpga_board_profile" "$BoardProfile"
Write-Row $rows "simpleos_fpga_build_attempted" $(if ($buildAttempted) { "true" } else { "false" })
Write-Row $rows "simpleos_fpga_build_status" "$buildStatus"
Write-Row $rows "simpleos_fpga_build_exit_code" "$buildExitCode"
Write-Row $rows "simpleos_fpga_build_command" "$buildCommand"
Write-Row $rows "simpleos_fpga_build_log_path" "$BuildLogPath"
Write-Row $rows "simpleos_fpga_expected_entry" "$ExpectedEntry"
Write-Row $rows "simpleos_fpga_expected_entry_status" $(if (Test-Path -LiteralPath $ExpectedEntry) { "pass" } else { "missing" })
Write-Row $rows "simpleos_fpga_expected_kernel_path" "$ExpectedKernelPath"
Write-Row $rows "simpleos_fpga_expected_kernel_status" $(if (Test-FileNonEmpty $ExpectedKernelPath) { "pass" } else { "missing" })
Write-Row $rows "simpleos_fpga_uart_terminal_status" "$uartTerminalStatus"
Write-Row $rows "simpleos_fpga_uart_terminal_reason" $(if ($uartTerminalStatus -eq "pass") { "pass" } else { "missing-serial-device-or-boot-marker" })
Write-Row $rows "simpleos_fpga_serial_device" $(if ($serialDeviceStatus -eq "pass") { "$SerialDevice" } else { "" })
Write-Row $rows "simpleos_fpga_serial_device_status" "$serialDeviceStatus"
Write-Row $rows "simpleos_fpga_serial_port_probe_attempted" "$serialPortProbeAttempted"
Write-Row $rows "simpleos_fpga_serial_port_probe_status" "$serialPortProbeStatus"
Write-Row $rows "simpleos_fpga_serial_port_probe_count" "$serialPortProbeCount"
Write-Row $rows "simpleos_fpga_serial_port_probe_ports" "$serialPortProbePorts"
Write-Row $rows "simpleos_fpga_serial_port_probe_log_path" "$SerialPortInventoryPath"
Write-Row $rows "simpleos_fpga_serial_device_candidate_status" "$serialDeviceCandidateStatus"
Write-Row $rows "simpleos_fpga_serial_inventory_evidence_status" "diagnostic"
Write-Row $rows "simpleos_fpga_serial_capture_attempted" "$serialCaptureAttempted"
Write-Row $rows "simpleos_fpga_serial_capture_status" "$serialCaptureStatus"
Write-Row $rows "simpleos_fpga_serial_capture_reason" "$serialCaptureReason"
Write-Row $rows "simpleos_fpga_serial_capture_timeout_seconds" "$CaptureTimeoutSeconds"
Write-Row $rows "simpleos_fpga_serial_capture_baud_rate" "$CaptureBaudRate"
Write-Row $rows "simpleos_fpga_serial_capture_bytes" "$serialCaptureBytes"
Write-Row $rows "simpleos_fpga_serial_capture_boot_marker_seen" "$serialCaptureMarkerSeen"
Write-Row $rows "simpleos_fpga_serial_log_path" "$SerialLogPath"
Write-Row $rows "simpleos_fpga_serial_log_status" $(if (Test-FileNonEmpty $SerialLogPath) { "pass" } else { "missing" })
Write-Row $rows "simpleos_fpga_serial_boot_marker" "$bootMarkerSeen"
Write-Row $rows "simpleos_fpga_serial_boot_marker_status" "$bootMarkerStatus"
Write-Row $rows "simpleos_fpga_rv64_boot_marker_status" "$rv64BootMarkerStatus"
Write-Row $rows "simpleos_fpga_test_passed_marker_status" "$testPassedMarkerStatus"
Write-Row $rows "simpleos_fpga_toolchain_status" "$ToolchainStatus"
Write-Row $rows "simpleos_fpga_bitstream_path" "$BitstreamPath"
Write-Row $rows "simpleos_fpga_bitstream_status" "$BitstreamStatus"
Write-Row $rows "simpleos_fpga_ssh_status" "blocked"
Write-Row $rows "simpleos_fpga_http_status" "blocked"
Write-Row $rows "simpleos_fpga_gpu_status" "blocked"
Write-Row $rows "simpleos_fpga_wm_status" "blocked"
Write-Row $rows "simpleos_fpga_vulkan_status" "blocked"
Write-Row $rows "simpleos_fpga_renderdoc_status" "blocked"

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
if ($ProbeSerialPorts) {
    $inventoryRows = [System.Collections.Generic.List[string]]::new()
    Write-Row $inventoryRows "simpleos_fpga_serial_port_probe_attempted" "$serialPortProbeAttempted"
    Write-Row $inventoryRows "simpleos_fpga_serial_port_probe_status" "$serialPortProbeStatus"
    Write-Row $inventoryRows "simpleos_fpga_serial_port_probe_count" "$serialPortProbeCount"
    Write-Row $inventoryRows "simpleos_fpga_serial_port_probe_ports" "$serialPortProbePorts"
    Write-Row $inventoryRows "simpleos_fpga_serial_device_candidate_status" "$serialDeviceCandidateStatus"
    Write-Row $inventoryRows "simpleos_fpga_serial_inventory_evidence_status" "diagnostic"
    $inventoryRows | Set-Content -Encoding ASCII -Path $SerialPortInventoryPath
}
$rows | ForEach-Object { Write-Output $_ }
Write-Output "simpleos_fpga_serial_evidence_path=$EvidencePath"

if ($BoardProfile -eq "fpga-riscv64-serial" -and
    $uartTerminalStatus -eq "pass" -and
    $serialDeviceStatus -eq "pass" -and
    $bootMarkerStatus -eq "pass" -and
    $ToolchainStatus -eq "pass" -and
    $BitstreamStatus -eq "pass") {
    exit 0
}
exit 1
