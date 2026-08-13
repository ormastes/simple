# Fail-closed Windows peer for the SOSIX/SimpleOS QEMU matrix.
#
# This script deliberately performs host admission and artifact readiness only.
# It never starts a guest.  A Windows executor may only add a guest-run phase
# after it retains the same nonce-bound evidence protocol as the POSIX runner.
[CmdletBinding()]
param(
    [ValidateSet('x86_32', 'x86_64', 'arm32', 'arm64', 'riscv32', 'riscv64')]
    [string]$Guest,
    [switch]$AllGuests,
    [switch]$Parallel,
    [switch]$Run,
    [switch]$Preflight,
    [switch]$SelfTest
)

$ErrorActionPreference = 'Stop'

function Fail-Usage([string]$Message) {
    [Console]::Error.WriteLine("check-sosix-qemu-matrix.ps1: $Message")
    exit 64
}

function Get-RepoRoot {
    return (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))
}

function Get-StorageRoot([string]$RepoRoot) {
    if (-not [string]::IsNullOrWhiteSpace($env:SIMPLE_BIG_STORAGE_ROOT)) {
        return $env:SIMPLE_BIG_STORAGE_ROOT
    }
    $config = if ($env:SIMPLE_BIG_STORAGE_CONFIG) { $env:SIMPLE_BIG_STORAGE_CONFIG } else { Join-Path $RepoRoot '.simple-big-storage-root' }
    if (Test-Path -LiteralPath $config -PathType Leaf) {
        $value = (Get-Content -LiteralPath $config -Raw).Trim()
        if (-not [string]::IsNullOrWhiteSpace($value)) { return $value }
    }
    # Match the POSIX resolver's conservative fallback without inventing a
    # temporary location that another agent cannot find.
    return (Join-Path $HOME '.simple')
}

function Get-RowDescriptors([string]$RepoRoot) {
    $build = Join-Path $RepoRoot 'build/os'
    $spec = Join-Path $RepoRoot 'test/03_system/os/qemu'
    $qemuDir = $env:SIMPLE_QEMU_BIN_DIR
    function Get-QemuName([string]$Name) {
        $fileName = "$Name.exe"
        if (-not [string]::IsNullOrWhiteSpace($qemuDir)) { return (Join-Path $qemuDir $fileName) }
        return $fileName
    }
    return @(
        [pscustomobject]@{ Guest='x86_32'; Qemu=(Get-QemuName 'qemu-system-x86_64'); Kernel=(Join-Path $build 'simpleos_x86_32_initrd_fs_exec_probe.elf'); Image=(Join-Path $build 'fat32-x86_32.img'); Spec=(Join-Path $spec 'sys_qemu_x86_32_fs_exec_spec.spl') },
        [pscustomobject]@{ Guest='x86_64'; Qemu=(Get-QemuName 'qemu-system-x86_64'); Kernel=(Join-Path $build 'simpleos_x86_64_fs_exec.elf'); Image=(Join-Path $build 'fat32-x86_64.img'); Spec=(Join-Path $spec 'sys_qemu_x86_64_fs_exec_spec.spl') },
        [pscustomobject]@{ Guest='arm32'; Qemu=(Get-QemuName 'qemu-system-arm'); Kernel=(Join-Path $build 'simpleos_arm32_fs_exec.elf'); Image=(Join-Path $build 'fat32-arm32.img'); Spec=(Join-Path $spec 'sys_qemu_arm32_fs_exec_spec.spl') },
        [pscustomobject]@{ Guest='arm64'; Qemu=(Get-QemuName 'qemu-system-aarch64'); Kernel=(Join-Path $build 'simpleos_arm64_fs_exec.elf'); Image=(Join-Path $build 'fat32-arm64.img'); Spec=(Join-Path $spec 'sys_qemu_arm64_fs_exec_spec.spl') },
        [pscustomobject]@{ Guest='riscv32'; Qemu=(Get-QemuName 'qemu-system-riscv32'); Kernel=(Join-Path $build 'simpleos_riscv32_smf_fs.elf'); Image=(Join-Path $build 'fat32-riscv32.img'); Spec=(Join-Path $spec 'sys_qemu_riscv32_fs_exec_spec.spl') },
        [pscustomobject]@{ Guest='riscv64'; Qemu=(Get-QemuName 'qemu-system-riscv64'); Kernel=(Join-Path $build 'simpleos_riscv64_smf_fs.elf'); Image=(Join-Path $build 'fat32-riscv64.img'); Spec=(Join-Path $spec 'sys_qemu_riscv64_fs_exec_spec.spl') }
    )
}

# Match the POSIX runner: use native acceleration only for a compatible guest
# ISA.  QEMU may advertise WHPX globally while rejecting it for a cross-ISA
# machine, so advertising alone must not make an ARM/RISC-V row ready.
function Get-WindowsHostIsa {
    $machine = if ($env:PROCESSOR_ARCHITEW6432) { $env:PROCESSOR_ARCHITEW6432 } else { $env:PROCESSOR_ARCHITECTURE }
    switch -Regex ($machine) {
        '^(AMD64|x86_64)$' { return 'x86_64' }
        '^(x86|X86)$' { return 'x86_32' }
        '^(ARM64|aarch64)$' { return 'arm64' }
        '^(ARM|arm32)$' { return 'arm32' }
        '^(riscv64)$' { return 'riscv64' }
        '^(riscv32)$' { return 'riscv32' }
        default { return 'unknown' }
    }
}

function Get-RowAccelerator([string]$HostIsa, [string]$Guest, [string]$Requested) {
    if ($Requested -ne 'whpx') { return $Requested }
    switch ("$HostIsa`:$Guest") {
        'x86_64:x86_32' { return 'whpx' }
        'x86_64:x86_64' { return 'whpx' }
        'x86_32:x86_32' { return 'whpx' }
        'arm64:arm32' { return 'whpx' }
        'arm64:arm64' { return 'whpx' }
        'arm32:arm32' { return 'whpx' }
        'riscv64:riscv32' { return 'whpx' }
        'riscv64:riscv64' { return 'whpx' }
        'riscv32:riscv32' { return 'whpx' }
        default { return 'tcg' }
    }
}

function Resolve-Executable([string]$Name) {
    if (Test-Path -LiteralPath $Name -PathType Leaf) { return (Resolve-Path -LiteralPath $Name).Path }
    $found = Get-Command $Name -ErrorAction SilentlyContinue
    if ($null -ne $found) { return $found.Source }
    return $null
}

function Test-SelfHostedRuntime([string]$Runtime) {
    if (-not (Test-Path -LiteralPath $Runtime -PathType Leaf)) { return [pscustomobject]@{ Status='blocked'; Reason="missing-spec-runtime:$Runtime" } }
    try {
        $version = & $Runtime --version 2>&1 | Out-String
        if ($LASTEXITCODE -ne 0) { return [pscustomobject]@{ Status='blocked'; Reason="unusable-spec-runtime:$Runtime" } }
        if ($version -match '(?i)bootstrap') { return [pscustomobject]@{ Status='blocked'; Reason="bootstrap-spec-runtime:$Runtime" } }
        return [pscustomobject]@{ Status='pass'; Reason='self-hosted-runtime-usable' }
    } catch {
        return [pscustomobject]@{ Status='blocked'; Reason="unusable-spec-runtime:$Runtime" }
    }
}

if ($SelfTest) {
    $descriptors = Get-RowDescriptors (Get-RepoRoot)
    if ($descriptors.Count -ne 6 -or @($descriptors.Guest | Select-Object -Unique).Count -ne 6) { throw 'matrix self-test: descriptors must be six and unique' }
    if (@($descriptors | Where-Object { $_.Qemu -notmatch '\.exe$' }).Count -ne 0) { throw 'matrix self-test: Windows QEMU descriptors require .exe names' }
    if ((Get-RowAccelerator 'x86_64' 'x86_64' 'whpx') -ne 'whpx') { throw 'matrix self-test: native x86_64 must retain WHPX' }
    if ((Get-RowAccelerator 'x86_64' 'arm64' 'whpx') -ne 'tcg') { throw 'matrix self-test: cross-ISA arm64 must fall back to TCG' }
    if ((Get-RowAccelerator 'arm64' 'arm32' 'whpx') -ne 'whpx') { throw 'matrix self-test: compatible arm32 must retain WHPX' }
    'sosix_qemu_matrix_windows_self_test=pass'
    exit 0
}

if ($AllGuests -and $Guest) { Fail-Usage 'choose -AllGuests or -Guest, not both' }
if (-not $AllGuests -and -not $Guest) { Fail-Usage '-AllGuests or -Guest is required' }
if ($Parallel -and -not $AllGuests) { Fail-Usage '-Parallel requires -AllGuests' }
if ($Run -and $Preflight) { Fail-Usage 'choose -Run or -Preflight, not both' }

$repoRoot = Get-RepoRoot
$mode = if ($Run) { 'run' } else { 'preflight' }
$runId = if ($env:SOSIX_QEMU_RUN_ID) { $env:SOSIX_QEMU_RUN_ID } else { (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ') }
if ($runId -notmatch '^[A-Za-z0-9._:-]+$') { Fail-Usage 'unsafe SOSIX_QEMU_RUN_ID' }
$storageRoot = Get-StorageRoot $repoRoot
$runRoot = Join-Path $storageRoot ("qemu/artifacts/sosix-qemu/windows/matrix/$runId")
New-Item -ItemType Directory -Force -Path $runRoot | Out-Null
$report = Join-Path $runRoot 'matrix.env'
Set-Content -LiteralPath $report -Value $null
function Emit([string]$Line) { $Line; Add-Content -LiteralPath $report -Value $Line }

$accelerator = if ($env:SIMPLE_QEMU_ACCELERATOR) { $env:SIMPLE_QEMU_ACCELERATOR } else { 'whpx' }
if ($accelerator -notin @('whpx', 'tcg')) { Fail-Usage "invalid Windows accelerator: $accelerator" }
$runtime = if ($env:SIMPLE_QEMU_RUNTIME) { $env:SIMPLE_QEMU_RUNTIME } else { Join-Path $repoRoot 'bin/simple.exe' }
$runtimeGate = Test-SelfHostedRuntime $runtime
$isWindows = $env:OS -eq 'Windows_NT'
$hostIsa = Get-WindowsHostIsa
$rows = Get-RowDescriptors $repoRoot
if ($Guest) { $rows = @($rows | Where-Object Guest -eq $Guest) }

Emit 'sosix_qemu_matrix_host=windows'
Emit "sosix_qemu_matrix_mode=$mode"
Emit ("sosix_qemu_matrix_guest_selection=" + $(if ($AllGuests) { 'all' } else { $Guest }))
Emit ("sosix_qemu_matrix_execution=" + $(if ($Parallel) { 'parallel' } else { 'serial' }))
Emit "sosix_qemu_matrix_accelerator=$accelerator"
Emit "sosix_qemu_matrix_host_isa=$hostIsa"
Emit "sosix_qemu_matrix_artifact_root=$runRoot"
Emit "sosix_qemu_matrix_runtime_status=$($runtimeGate.Status)"
Emit "sosix_qemu_matrix_runtime_reason=$($runtimeGate.Reason)"

$blocked = 0
foreach ($row in $rows) {
    $prefix = "sosix_qemu_matrix_windows_$($row.Guest)"
    $qemu = Resolve-Executable $row.Qemu
    $rowAccelerator = Get-RowAccelerator $hostIsa $row.Guest $accelerator
    $reason = $null
    Emit "${prefix}_kernel=$($row.Kernel)"
    Emit "${prefix}_image=$($row.Image)"
    Emit "${prefix}_spec=$($row.Spec)"
    Emit "${prefix}_accelerator=$rowAccelerator"
    Emit ("${prefix}_native_timing_applicable=" + $(if ($rowAccelerator -eq 'tcg') { 'false' } else { 'true' }))
    if (-not $isWindows) { $reason = 'actual-host-is-not-windows' }
    elseif (-not $qemu) { $reason = "missing-qemu:$($row.Qemu)" }
    else {
        try {
            $accels = & $qemu -accel help 2>&1 | Out-String
            if ($LASTEXITCODE -ne 0 -or $accels -notmatch "(?m)^\s*$rowAccelerator\s*$") { $reason = "accelerator-not-admitted:$rowAccelerator" }
        } catch { $reason = "accelerator-probe-failed:$rowAccelerator" }
    }
    if (-not $reason -and $runtimeGate.Status -ne 'pass') { $reason = $runtimeGate.Reason }
    if (-not $reason -and -not (Test-Path -LiteralPath $row.Kernel -PathType Leaf)) { $reason = "missing-kernel:$($row.Kernel)" }
    if (-not $reason -and -not (Test-Path -LiteralPath $row.Image -PathType Leaf)) { $reason = "missing-image:$($row.Image)" }
    if (-not $reason -and -not (Test-Path -LiteralPath $row.Spec -PathType Leaf)) { $reason = "missing-spec:$($row.Spec)" }
    if (-not $reason -and $Run) { $reason = 'guest-execution-not-implemented-by-windows-peer' }
    if ($reason) {
        Emit "${prefix}_status=blocked"
        Emit "${prefix}_reason=$reason"
        $blocked++
    } else {
        Emit "${prefix}_status=ready"
        Emit "${prefix}_reason=host-admitted-artifacts-present"
    }
}
Emit "sosix_qemu_matrix_ready_count=$($rows.Count - $blocked)"
Emit "sosix_qemu_matrix_blocked_count=$blocked"
if ($blocked -ne 0) { Emit 'sosix_qemu_matrix_status=blocked'; exit 1 }
Emit 'sosix_qemu_matrix_status=ready'
