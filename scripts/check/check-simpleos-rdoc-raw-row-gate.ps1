param(
    [string]$EvidenceDir = "build/simpleos_multiconfig_live_evidence/rdoc-raw-row-gate",
    [string]$SimpleBinary = "src\compiler_rust\target\debug\simple.exe",
    [string]$AggregateScript = "scripts\check\check_simpleos_multiconfig_live_evidence.spl",
    [string]$SummaryPath = ""
)

$ErrorActionPreference = "Stop"

function Write-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
}

function Write-EvidenceFile([string]$path, [bool]$includeMagicStatus) {
    $rows = [System.Collections.Generic.List[string]]::new()
    Write-Row $rows "simpleos_qemu_serial_console_status" "pass"
    Write-Row $rows "simpleos_qemu_rv64_ssh_banner" "SimpleOS synthetic ssh"
    Write-Row $rows "simpleos_qemu_rv64_ssh_probe_status" "pass"
    Write-Row $rows "simpleos_qemu_rv64_http_status_code" "200"
    Write-Row $rows "simpleos_qemu_rv64_http_probe_status" "pass"
    Write-Row $rows "simpleos_qemu_gpu_readback_status" "pass"
    Write-Row $rows "simpleos_qemu_wm_marker_status" "pass"

    Write-Row $rows "simpleos_fpga_board_profile" "fpga-riscv64-serial"
    Write-Row $rows "simpleos_fpga_uart_terminal_status" "pass"
    Write-Row $rows "simpleos_fpga_serial_device" "COM_SYNTHETIC"
    Write-Row $rows "simpleos_fpga_serial_boot_marker" "simpleos-rv64-boot"
    Write-Row $rows "simpleos_fpga_toolchain_status" "pass"
    Write-Row $rows "simpleos_fpga_bitstream_status" "pass"
    Write-Row $rows "simpleos_fpga_ssh_status" "blocked"
    Write-Row $rows "simpleos_fpga_http_status" "blocked"
    Write-Row $rows "simpleos_fpga_gpu_status" "blocked"
    Write-Row $rows "simpleos_fpga_wm_status" "blocked"
    Write-Row $rows "simpleos_fpga_vulkan_status" "blocked"
    Write-Row $rows "simpleos_fpga_renderdoc_status" "blocked"

    Write-Row $rows "simpleos_engine2d_bridge_profile" "qemu-riscv64-desktop"
    Write-Row $rows "simpleos_engine2d_drawing_backend" "virtio_gpu"
    Write-Row $rows "simpleos_engine2d_processing_backend" "vulkan"
    Write-Row $rows "simpleos_engine2d_qemu_gpu_device" "virtio-gpu-pci,disable-modern=on,disable-legacy=off"
    Write-Row $rows "simpleos_engine2d_runtime_backend" "vulkan"
    Write-Row $rows "simpleos_engine2d_scene" "vulkan-engine2d"
    Write-Row $rows "simpleos_simple2d_command_status" "pass"
    Write-Row $rows "simpleos_simple2d_command_path" "draw_ir-to-engine2d"
    Write-Row $rows "simpleos_engine2d_device_readback_required" "true"
    Write-Row $rows "simpleos_qemu_qmp_screendump_required" "true"
    Write-Row $rows "simpleos_engine2d_vulkan_device_name" "synthetic-vulkan"
    Write-Row $rows "simpleos_engine2d_viewport_width" "16"
    Write-Row $rows "simpleos_engine2d_viewport_height" "16"
    Write-Row $rows "simpleos_engine2d_readback_checksum" "synthetic-checksum"
    Write-Row $rows "simpleos_engine2d_readback_nonblank_status" "pass"
    Write-Row $rows "simpleos_simple2d_readback_status" "pass"

    Write-Row $rows "simpleos_renderdoc_capture_mode" "capture-simple"
    Write-Row $rows "simpleos_renderdoc_rdc_path" "build/synthetic/simpleos-wm.rdc"
    Write-Row $rows "simpleos_renderdoc_rdc_magic" "RDOC"
    if ($includeMagicStatus) {
        Write-Row $rows "simpleos_renderdoc_rdc_magic_status" "pass"
    }
    Write-Row $rows "simpleos_renderdoc_rdc_size_bytes" "8"
    Write-Row $rows "simpleos_renderdoc_capture_log_path" "build/synthetic/renderdoc-capture.log"
    Write-Row $rows "simpleos_renderdoc_capture_log_status" "pass"
    Write-Row $rows "simpleos_renderdoc_simple_runtime_backend" "vulkan"
    Write-Row $rows "simpleos_renderdoc_simple_scene" "vulkan-engine2d"
    Write-Row $rows "simpleos_renderdoc_helper_status" "pass"
    Write-Row $rows "simpleos_renderdoc_qemu_wm_log_path" "build/synthetic/qemu-wm-renderdoc.log"
    Write-Row $rows "simpleos_renderdoc_host_wm_log_path" "build/synthetic/host-wm-renderdoc.log"

    Write-Row $rows "simpleos_wm_qemu_scene" "simpleos-desktop-four-windows"
    Write-Row $rows "simpleos_wm_host_scene" "simpleos-desktop-four-windows"
    Write-Row $rows "simpleos_wm_qemu_window_count" "4"
    Write-Row $rows "simpleos_wm_host_window_count" "4"
    Write-Row $rows "simpleos_wm_qemu_focus_id" "terminal"
    Write-Row $rows "simpleos_wm_host_focus_id" "terminal"
    Write-Row $rows "simpleos_wm_qemu_titlebar_status" "pass"
    Write-Row $rows "simpleos_wm_host_titlebar_status" "pass"
    Write-Row $rows "simpleos_wm_qemu_taskbar_status" "pass"
    Write-Row $rows "simpleos_wm_host_taskbar_status" "pass"
    Write-Row $rows "simpleos_wm_renderdoc_log_compare_status" "pass"
    Write-Row $rows "simpleos_wm_argb_diff_status" "pass"
    Write-Row $rows "simpleos_wm_argb_mismatch_count" "0"
    Write-Row $rows "simpleos_qemu_wm_evidence_status" "pass"
    Write-Row $rows "simpleos_host_wm_evidence_status" "pass"
    Write-Row $rows "simpleos_wm_qemu_host_compare_status" "pass"
    Write-Row $rows "simpleos_wm_compare_scene" "simpleos-desktop-four-windows"

    $rows | Set-Content -Encoding ASCII -Path $path
}

function Get-RowValue([string[]]$lines, [string]$key) {
    $prefix = "$key="
    for ($i = $lines.Count - 1; $i -ge 0; $i--) {
        if ($lines[$i].StartsWith($prefix)) {
            return $lines[$i].Substring($prefix.Length).Trim()
        }
    }
    return ""
}

function Invoke-Aggregate([string]$evidencePath, [string]$logPath) {
    $oldSimpleLib = $env:SIMPLE_LIB
    $env:SIMPLE_LIB = "src"
    try {
        $output = & $script:ResolvedSimpleBinary $script:ResolvedAggregateScript --evidence $evidencePath --mode=interpreter 2>&1
        $exitCode = $LASTEXITCODE
    } finally {
        if ($null -eq $oldSimpleLib) {
            Remove-Item Env:SIMPLE_LIB -ErrorAction SilentlyContinue
        } else {
            $env:SIMPLE_LIB = $oldSimpleLib
        }
    }
    $lines = @($output | ForEach-Object { "$_" })
    $lines | Set-Content -Encoding ASCII -Path $logPath
    return @{ exit_code = $exitCode; lines = $lines }
}

function Test-CaseResult($case, [int]$expectedExit, [string]$expectedArtifact, [string]$expectedWm, [string]$expectedLive) {
    $artifact = Get-RowValue $case.lines "simpleos_renderdoc_artifact_evidence_status"
    $wm = Get-RowValue $case.lines "simpleos_wm_renderdoc_evidence_status"
    $live = Get-RowValue $case.lines "simpleos_multiconfig_live_status"
    return @{
        pass = ($case.exit_code -eq $expectedExit -and $artifact -eq $expectedArtifact -and $wm -eq $expectedWm -and $live -eq $expectedLive)
        artifact = $artifact
        wm = $wm
        live = $live
    }
}

New-Item -ItemType Directory -Force -Path $EvidenceDir | Out-Null
if ([string]::IsNullOrWhiteSpace($SummaryPath)) {
    $SummaryPath = Join-Path $EvidenceDir "rdoc-raw-row-gate.env"
}

$script:ResolvedSimpleBinary = (Resolve-Path -LiteralPath $SimpleBinary).Path
$script:ResolvedAggregateScript = (Resolve-Path -LiteralPath $AggregateScript).Path

$missingStatusEvidence = Join-Path $EvidenceDir "rdoc-raw-missing-status.env"
$withStatusEvidence = Join-Path $EvidenceDir "rdoc-raw-with-status.env"
$missingStatusLog = Join-Path $EvidenceDir "rdoc-raw-missing-status.log"
$withStatusLog = Join-Path $EvidenceDir "rdoc-raw-with-status.log"

Write-EvidenceFile $missingStatusEvidence $false
Write-EvidenceFile $withStatusEvidence $true

$missingCase = Invoke-Aggregate $missingStatusEvidence $missingStatusLog
$withCase = Invoke-Aggregate $withStatusEvidence $withStatusLog

$missingCheck = Test-CaseResult $missingCase 1 "blocked:missing-simple-rdoc-magic" "blocked:missing-simple-rdoc-magic" "blocked:renderdoc-artifact:blocked:missing-simple-rdoc-magic"
$withCheck = Test-CaseResult $withCase 0 "pass" "pass" "pass"
$gateStatus = if ($missingCheck.pass -and $withCheck.pass) { "pass" } else { "fail" }

$summary = [System.Collections.Generic.List[string]]::new()
Write-Row $summary "simpleos_rdoc_raw_row_gate_wrapper" "check-simpleos-rdoc-raw-row-gate.ps1"
Write-Row $summary "simpleos_rdoc_raw_row_gate_missing_status_evidence_path" "$missingStatusEvidence"
Write-Row $summary "simpleos_rdoc_raw_row_gate_missing_status_log_path" "$missingStatusLog"
Write-Row $summary "simpleos_rdoc_raw_row_gate_missing_status_exit_code" "$($missingCase.exit_code)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_missing_status_artifact_status" "$($missingCheck.artifact)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_missing_status_wm_status" "$($missingCheck.wm)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_missing_status_live_status" "$($missingCheck.live)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_with_status_evidence_path" "$withStatusEvidence"
Write-Row $summary "simpleos_rdoc_raw_row_gate_with_status_log_path" "$withStatusLog"
Write-Row $summary "simpleos_rdoc_raw_row_gate_with_status_exit_code" "$($withCase.exit_code)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_with_status_artifact_status" "$($withCheck.artifact)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_with_status_wm_status" "$($withCheck.wm)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_with_status_live_status" "$($withCheck.live)"
Write-Row $summary "simpleos_rdoc_raw_row_gate_status" "$gateStatus"
$summary | Set-Content -Encoding ASCII -Path $SummaryPath
$summary | ForEach-Object { Write-Output $_ }

if ($gateStatus -eq "pass") {
    exit 0
}
exit 1
