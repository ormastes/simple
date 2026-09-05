# Native Windows peer for the SOSIX/SimpleOS QEMU matrix.
#
# Preflight proves only that the actual Windows host, canonical settings,
# admission record, emulator, kernel, media, and contract are ready.  Run mode
# additionally creates nonce-isolated media, invokes QEMU, validates the real
# serial transcript, and calls the canonical producer.  No preflight path can
# publish a PASS bundle.
[CmdletBinding()]
param(
    [ValidateSet('x86_32', 'x86_64', 'arm32', 'arm64', 'riscv32', 'riscv64')]
    [string]$Guest,
    [switch]$AllGuests,
    [switch]$Parallel,
    [switch]$Run,
    [switch]$Preflight,
    [switch]$SelfTest,
    [ValidateRange(1, 900)]
    [int]$TimeoutSeconds = 90
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$descriptorOwner = Join-Path $PSScriptRoot 'sosix-qemu-windows-descriptors.ps1'
if (-not (Test-Path -LiteralPath $descriptorOwner -PathType Leaf)) { throw "missing-descriptor-owner:$descriptorOwner" }
. $descriptorOwner

function Fail-Usage([string]$Message) {
    [Console]::Error.WriteLine("check-sosix-qemu-matrix.ps1: $Message")
    exit 64
}

function Write-SosixLfAsciiRecord {
    param(
        [Parameter(Mandatory=$true)][string]$Path,
        [Parameter(Mandatory=$true)][string[]]$Lines
    )
    foreach ($line in $Lines) {
        if ($line -match "[`r`n]" -or $line -notmatch '^[\x00-\x7F]*$') {
            throw "noncanonical-record-line:$Path"
        }
    }
    [IO.File]::WriteAllText($Path, (($Lines -join "`n") + "`n"), [Text.Encoding]::ASCII)
}

function Get-RepoRoot {
    return (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))
}

function Resolve-Executable([string]$Name) {
    if (Test-Path -LiteralPath $Name -PathType Leaf) {
        return (Resolve-Path -LiteralPath $Name).Path
    }
    $found = Get-Command $Name -ErrorAction SilentlyContinue
    if ($null -ne $found) { return $found.Source }
    return $null
}

function Resolve-SosixShell {
    foreach ($candidate in @('sh.exe', 'sh')) {
        $resolved = Resolve-Executable $candidate
        if ($resolved) { return $resolved }
    }
    throw 'missing-posix-shell: the canonical QEMU owners require sh.exe'
}

function Invoke-SosixShellTool {
    param(
        [Parameter(Mandatory=$true)][string]$Script,
        [string[]]$Arguments = @(),
        [hashtable]$Environment = @{}
    )

    $shell = Resolve-SosixShell
    $saved = @{}
    foreach ($key in $Environment.Keys) {
        $saved[$key] = [Environment]::GetEnvironmentVariable($key, 'Process')
        [Environment]::SetEnvironmentVariable($key, [string]$Environment[$key], 'Process')
    }
    Push-Location $script:RepoRoot
    try {
        $raw = @(& $shell $Script @Arguments 2>&1)
        $exitCode = $LASTEXITCODE
    } finally {
        Pop-Location
        foreach ($key in $Environment.Keys) {
            [Environment]::SetEnvironmentVariable($key, $saved[$key], 'Process')
        }
    }
    $lines = @($raw | ForEach-Object { [string]$_ })
    return [pscustomobject]@{ ExitCode=[int]$exitCode; Lines=$lines }
}

function ConvertFrom-SosixEnvRecord {
    param(
        [Parameter(Mandatory=$true)][string[]]$Lines,
        [string[]]$AllowedKeys = @()
    )

    $record = @{}
    foreach ($line in $Lines) {
        if ([string]::IsNullOrWhiteSpace($line)) { continue }
        if ($line -notmatch '^([A-Za-z0-9_]+)=(.*)$') {
            throw "malformed-record-line:$line"
        }
        $key = $Matches[1]
        if ($record.ContainsKey($key)) { throw "duplicate-record-field:$key" }
        if ($AllowedKeys.Count -ne 0 -and $key -notin $AllowedKeys) {
            throw "open-record-field:$key"
        }
        $record[$key] = $Matches[2]
    }
    return $record
}

function Get-RequiredRecordField([hashtable]$Record, [string]$Key) {
    if (-not $Record.ContainsKey($Key) -or [string]::IsNullOrWhiteSpace([string]$Record[$Key])) {
        throw "missing-record-field:$Key"
    }
    return [string]$Record[$Key]
}

function Convert-ToNativePath([string]$Path) {
    if ($env:OS -ne 'Windows_NT') { return $Path }
    if ($Path -match '^[A-Za-z]:[\\/]') { return $Path }
    $cygpath = Resolve-Executable 'cygpath.exe'
    if (-not $cygpath) { throw "missing-cygpath-for-shared-path:$Path" }
    $converted = @(& $cygpath -w -- $Path 2>&1)
    if ($LASTEXITCODE -ne 0 -or $converted.Count -ne 1) {
        throw "cannot-convert-shared-path:$Path"
    }
    return [string]$converted[0]
}

function Convert-ToSharedPath([string]$Path) {
    $absolute = [IO.Path]::GetFullPath($Path)
    if ($env:OS -ne 'Windows_NT') { return $absolute.Replace('\', '/') }
    $cygpath = Resolve-Executable 'cygpath.exe'
    if (-not $cygpath) { throw "missing-cygpath-for-native-path:$absolute" }
    $converted = @(& $cygpath -u -- $absolute 2>&1)
    if ($LASTEXITCODE -ne 0 -or $converted.Count -ne 1) {
        throw "cannot-convert-native-path:$absolute"
    }
    return [string]$converted[0]
}

function Get-SosixSharedSettings([string]$Accelerator) {
    $allowed = @(
        'simple_qemu_host', 'simple_qemu_accelerator',
        'simple_qemu_native_timing_applicable', 'simple_qemu_storage_root',
        'simple_qemu_image_root', 'simple_qemu_overlay_root',
        'simple_qemu_artifact_root', 'simple_qemu_cache_root',
        'simple_qemu_x86_32_bin', 'simple_qemu_x86_64_bin',
        'simple_qemu_arm32_bin', 'simple_qemu_arm64_bin',
        'simple_qemu_riscv32_bin', 'simple_qemu_riscv64_bin'
    )
    $result = Invoke-SosixShellTool `
        -Script 'scripts/qemu/simple-qemu-settings.shs' `
        -Arguments @('--print') `
        -Environment @{ SIMPLE_QEMU_HOST='windows'; SIMPLE_QEMU_ACCELERATOR=$Accelerator }
    if ($result.ExitCode -ne 0) {
        throw "shared-settings-failed:$($result.Lines -join ';')"
    }
    $settings = ConvertFrom-SosixEnvRecord -Lines $result.Lines -AllowedKeys $allowed
    if ((Get-RequiredRecordField $settings 'simple_qemu_host') -ne 'windows') {
        throw 'shared-settings-host-is-not-windows'
    }
    return $settings
}

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

function Write-SosixRowReceipt {
    param(
        [Parameter(Mandatory=$true)][string]$Path,
        [Parameter(Mandatory=$true)][string]$AcceptanceId,
        [Parameter(Mandatory=$true)][string]$Mode,
        [Parameter(Mandatory=$true)][ValidateSet('ready','blocked','failed','pass')][string]$Status,
        [Parameter(Mandatory=$true)][string]$Reason,
        [string]$CanonicalBundle = 'none'
    )
    foreach ($value in @($AcceptanceId, $Mode, $Status, $Reason, $CanonicalBundle)) {
        if ($value -match "[`r`n]") { throw 'receipt-value-contains-newline' }
    }
    $parent = Split-Path -Parent $Path
    New-Item -ItemType Directory -Force -Path $parent | Out-Null
    $tmp = "$Path.tmp"
    $lines = @(
        'schema_version=1'
        "acceptance_id=$AcceptanceId"
        "mode=$Mode"
        "status=$Status"
        "reason=$Reason"
        "canonical_bundle=$CanonicalBundle"
    )
    Write-SosixLfAsciiRecord -Path $tmp -Lines $lines
    Move-Item -LiteralPath $tmp -Destination $Path -Force
}

function Assert-SosixKernelContract([object]$Row) {
    $kernel = Convert-ToSharedPath $Row.Kernel
    $base = Invoke-SosixShellTool `
        -Script 'scripts/check/check-simpleos-fs-exec-kernel-elf.shs' `
        -Arguments @($Row.Guest, $kernel)
    if ($base.ExitCode -ne 0) {
        throw "kernel-elf-contract-failed:$($Row.Guest):$($base.Lines -join ';')"
    }
    if ($Row.Guest -eq 'arm64') {
        $arm64 = Invoke-SosixShellTool `
            -Script 'scripts/check/check-simpleos-arm64-fs-exec-elf.shs' `
            -Arguments @($kernel)
        if ($arm64.ExitCode -ne 0) {
            throw "arm64-kernel-elf-contract-failed:$($arm64.Lines -join ';')"
        }
    }
    if ($Row.Guest -eq 'x86_32') {
        $lifecycle = Invoke-SosixShellTool `
            -Script 'scripts/check/check-x86-32-cpl3-lifecycle-contract.shs' `
            -Arguments @('--admit', $kernel)
        if ($lifecycle.ExitCode -ne 0) {
            throw "x86-32-cpl3-lifecycle-not-admitted:$($lifecycle.Lines -join ';')"
        }
    }
    if ($Row.Guest -eq 'arm32') {
        $lifecycle = Invoke-SosixShellTool `
            -Script 'scripts/check/check-arm32-user-lifecycle-contract.shs' `
            -Arguments @('--admit', $kernel)
        if ($lifecycle.ExitCode -ne 0) {
            throw "arm32-el0-lifecycle-not-admitted:$($lifecycle.Lines -join ';')"
        }
    }
}

function New-SosixWindowsAdmission {
    param(
        [Parameter(Mandatory=$true)][object]$Row,
        [Parameter(Mandatory=$true)][hashtable]$Settings,
        [Parameter(Mandatory=$true)][string]$Accelerator,
        [Parameter(Mandatory=$true)][string]$AdmissionPath
    )
    $configured = Get-RequiredRecordField $Settings $Row.QemuKey
    $qemuNative = Resolve-Executable $configured
    if (-not $qemuNative) { throw "missing-qemu:$configured" }
    $qemuShared = Convert-ToSharedPath $qemuNative
    $result = Invoke-SosixShellTool `
        -Script 'scripts/qemu/simple-qemu-host-admission.shs' `
        -Arguments @('--host','windows','--arch',$Row.Guest,'--accelerator',$Accelerator,'--qemu-binary',$qemuShared)
    if ($result.ExitCode -ne 0) {
        throw "host-or-accelerator-admission-failed:$($result.Lines -join ';')"
    }
    $allowed = @(
        'detected_host','requested_host','host_identity_status','host_identity_reason',
        'qemu_binary','qemu_binary_resolved','qemu_sha256','qemu_version',
        'requested_accelerator','accelerator_advertised_status','accelerator_advertised_reason',
        'accelerator_probe_status','accelerator_probe_reason','native_timing_applicable',
        'simple_qemu_storage_root'
    )
    $record = ConvertFrom-SosixEnvRecord -Lines $result.Lines -AllowedKeys $allowed
    foreach ($field in @('detected_host','requested_host','host_identity_status','accelerator_advertised_status','accelerator_probe_status')) {
        [void](Get-RequiredRecordField $record $field)
    }
    if ($record['detected_host'] -ne 'windows' -or $record['requested_host'] -ne 'windows' -or
        $record['host_identity_status'] -ne 'pass' -or
        $record['accelerator_advertised_status'] -ne 'pass' -or
        $record['accelerator_probe_status'] -ne 'pass') {
        throw 'admission-record-is-not-pass'
    }
    Write-SosixLfAsciiRecord -Path $AdmissionPath -Lines $result.Lines
    return [pscustomobject]@{
        NativeQemu=$qemuNative
        SharedQemu=$qemuShared
        Record=$record
        Path=$AdmissionPath
    }
}

function Copy-SosixFsExecProgram {
    param(
        [Parameter(Mandatory=$true)][string]$Image,
        [Parameter(Mandatory=$true)][string]$Receipt,
        [Parameter(Mandatory=$true)][string]$Output,
        [Parameter(Mandatory=$true)][string]$WorkloadNonce,
        [Parameter(Mandatory=$true)][string]$CollectorNonce
    )
    $allowed = @('contract','nonce','collector_nonce','nonce_slot_bytes','elf_offset','elf_size','elf_sha256','image_sha256','readback')
    $record = ConvertFrom-SosixEnvRecord -Lines @(Get-Content -LiteralPath $Receipt) -AllowedKeys $allowed
    if ($record['contract'] -ne 'simpleos-fs-exec-run-v1' -or $record['nonce'] -ne $WorkloadNonce -or
        $record['collector_nonce'] -ne $CollectorNonce -or $record['readback'] -ne 'pass') {
        throw 'nonce-media-receipt-mismatch'
    }
    $actualImageHash = (Get-FileHash -LiteralPath $Image -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($record['image_sha256'] -ne $actualImageHash) { throw 'nonce-media-image-hash-mismatch' }
    [Int64]$offset = 0
    [Int64]$size = 0
    if (-not [Int64]::TryParse($record['elf_offset'], [ref]$offset) -or
        -not [Int64]::TryParse($record['elf_size'], [ref]$size) -or
        $offset -lt 0 -or $size -le 0) {
        throw 'nonce-media-invalid-program-extent'
    }
    $input = [IO.File]::OpenRead($Image)
    try {
        if ($offset + $size -gt $input.Length) { throw 'nonce-media-program-extent-out-of-bounds' }
        [void]$input.Seek($offset, [IO.SeekOrigin]::Begin)
        $outputStream = [IO.File]::Create($Output)
        try {
            $buffer = New-Object byte[] 65536
            [Int64]$remaining = $size
            while ($remaining -gt 0) {
                $want = [Math]::Min([Int64]$buffer.Length, $remaining)
                $read = $input.Read($buffer, 0, [int]$want)
                if ($read -le 0) { throw 'nonce-media-program-short-read' }
                $outputStream.Write($buffer, 0, $read)
                $remaining -= $read
            }
        } finally {
            $outputStream.Dispose()
        }
    } finally {
        $input.Dispose()
    }
    $actualProgramHash = (Get-FileHash -LiteralPath $Output -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($record['elf_sha256'] -ne $actualProgramHash) { throw 'nonce-media-program-hash-mismatch' }
}

function New-SosixWindowsNonceMedia {
    param(
        [Parameter(Mandatory=$true)][object]$Row,
        [Parameter(Mandatory=$true)][string]$RowRoot,
        [Parameter(Mandatory=$true)][string]$WorkloadNonce,
        [Parameter(Mandatory=$true)][string]$CollectorNonce
    )
    $runImage = Join-Path $RowRoot "$($Row.Guest).nonce.img"
    $program = Join-Path $RowRoot 'program.elf'
    if ([IO.Path]::GetFullPath($Row.Image) -eq [IO.Path]::GetFullPath($runImage)) {
        throw 'source-and-run-image-alias'
    }
    $result = Invoke-SosixShellTool `
        -Script 'scripts/os/prepare_qemu_nonce_media.shs' `
        -Arguments @(
            (Convert-ToSharedPath $Row.Image),
            (Convert-ToSharedPath $runImage),
            $WorkloadNonce,
            $CollectorNonce
        )
    if ($result.ExitCode -ne 0) {
        throw "nonce-media-preparation-failed:$($result.Lines -join ';')"
    }
    $receipt = "$runImage.fs-exec-receipt"
    if (-not (Test-Path -LiteralPath $runImage -PathType Leaf) -or
        -not (Test-Path -LiteralPath $receipt -PathType Leaf)) {
        throw 'nonce-media-output-missing'
    }
    Copy-SosixFsExecProgram -Image $runImage -Receipt $receipt -Output $program `
        -WorkloadNonce $WorkloadNonce -CollectorNonce $CollectorNonce
    return [pscustomobject]@{ Image=$runImage; Receipt=$receipt; Program=$program }
}

function Quote-WindowsNativeArgument([string]$Argument) {
    if ($Argument.Length -gt 0 -and $Argument -notmatch '[\s"]') { return $Argument }
    $builder = New-Object Text.StringBuilder
    [void]$builder.Append('"')
    $slashes = 0
    foreach ($character in $Argument.ToCharArray()) {
        if ($character -eq '\') {
            $slashes++
        } elseif ($character -eq '"') {
            [void]$builder.Append(('\' * ($slashes * 2 + 1)))
            [void]$builder.Append('"')
            $slashes = 0
        } else {
            if ($slashes -ne 0) { [void]$builder.Append(('\' * $slashes)); $slashes = 0 }
            [void]$builder.Append($character)
        }
    }
    if ($slashes -ne 0) { [void]$builder.Append(('\' * ($slashes * 2))) }
    [void]$builder.Append('"')
    return $builder.ToString()
}

function Get-SosixFirmware([object]$Row) {
    if ($Row.FirmwareMode -eq 'direct-kernel') {
        return [pscustomobject]@{ Native='none'; Shared='none'; Id='none'; Version='none'; Stages='guest-entry' }
    }
    if ($Row.Guest -ne 'riscv64') { throw "unsupported-firmware-mode:$($Row.FirmwareMode)" }
    if ([string]::IsNullOrWhiteSpace($env:SOSIX_QEMU_RISCV64_FIRMWARE) -or
        [string]::IsNullOrWhiteSpace($env:SOSIX_QEMU_RISCV64_FIRMWARE_ID) -or
        [string]::IsNullOrWhiteSpace($env:SOSIX_QEMU_RISCV64_FIRMWARE_VERSION)) {
        throw 'missing-riscv64-firmware-binding'
    }
    $native = [IO.Path]::GetFullPath($env:SOSIX_QEMU_RISCV64_FIRMWARE)
    if (-not (Test-Path -LiteralPath $native -PathType Leaf)) { throw "missing-riscv64-firmware:$native" }
    return [pscustomobject]@{
        Native=$native
        Shared=(Convert-ToSharedPath $native)
        Id=$env:SOSIX_QEMU_RISCV64_FIRMWARE_ID
        Version=$env:SOSIX_QEMU_RISCV64_FIRMWARE_VERSION
        Stages='opensbi-entry>opensbi-handoff>guest-entry'
    }
}

function Get-SosixRequiredMarkers {
    param(
        [Parameter(Mandatory=$true)][object]$Row,
        [Parameter(Mandatory=$true)][object]$Firmware,
        [Parameter(Mandatory=$true)][string]$WorkloadNonce,
        [Parameter(Mandatory=$true)][string]$CollectorNonce
    )
    $markers = @()
    if ($Firmware.Stages -ne 'guest-entry') {
        $markers += @($Firmware.Stages -split '>' | Where-Object { $_ -ne 'guest-entry' })
    }
    $markers += "SOSIX_COLLECTOR_RUN_NONCE=$CollectorNonce"
    $markers += 'guest-entry'
    $markers += "SIMPLEOS_QEMU_NONCE=$WorkloadNonce"
    $markers += 'FS_LS_BEGIN path=/SYS/APPS'
    $markers += 'FS_LS_ENTRY name='
    $markers += 'FS_LS_END status=pass'
    $markers += "FS_PROGRAM_BEGIN path=/FSEXEC.ELF arch=$($Row.Guest)"
    $markers += "SIMPLEOS_FS_EXEC_OK arch=$($Row.Guest) nonce=$WorkloadNonce"
    switch ($Row.Guest) {
        'x86_32' {
            $markers += 'FS_PROGRAM_END rc=37 reaped=true'
            $markers += $Row.ExactReap
        }
        'arm32' {
            $markers += $Row.ExactReap
        }
        'arm64' {
            $markers += 'FS_PROGRAM_END rc=37 reaped=true'
            $markers += $Row.ExactReap
        }
        default {
            $markers += $Row.ExactReap
            $markers += 'FS_PROGRAM_END rc=37 reaped=true'
        }
    }
    $markers += 'TEST PASSED'
    return $markers
}

function Assert-SosixOrderedTranscript {
    param(
        [Parameter(Mandatory=$true)][string]$Transcript,
        [Parameter(Mandatory=$true)][string[]]$Markers,
        [Parameter(Mandatory=$true)][string]$WorkloadNonce,
        [Parameter(Mandatory=$true)][string]$CollectorNonce
    )
    $position = 0
    foreach ($marker in $Markers) {
        $found = $Transcript.IndexOf($marker, $position, [StringComparison]::Ordinal)
        if ($found -lt 0) { throw "missing-or-out-of-order-marker:$marker" }
        $position = $found + $marker.Length
    }
    $collectorCount = [regex]::Matches($Transcript, [regex]::Escape($CollectorNonce)).Count
    if ($collectorCount -ne 1) { throw "collector-nonce-count:$collectorCount" }
    $workloadCount = [regex]::Matches($Transcript, [regex]::Escape($WorkloadNonce)).Count
    if ($workloadCount -lt 2) { throw "workload-nonce-count:$workloadCount" }
}

function Invoke-SosixWindowsGuestRow {
    param(
        [Parameter(Mandatory=$true)][object]$Row,
        [Parameter(Mandatory=$true)][object]$Admission,
        [Parameter(Mandatory=$true)][string]$Accelerator,
        [Parameter(Mandatory=$true)][string]$RowRoot,
        [Parameter(Mandatory=$true)][string]$WorkloadNonce,
        [Parameter(Mandatory=$true)][string]$CollectorNonce,
        [Parameter(Mandatory=$true)][int]$Timeout
    )
    if (-not $Row.CollectorNonceEcho) {
        throw "collector-nonce-echo-not-implemented:$($Row.Guest)"
    }
    if (-not $Row.RunContractReady) {
        throw "guest-run-contract-not-implemented:$($Row.Guest)"
    }
    $media = New-SosixWindowsNonceMedia -Row $Row -RowRoot $RowRoot `
        -WorkloadNonce $WorkloadNonce -CollectorNonce $CollectorNonce
    $firmware = Get-SosixFirmware $Row
    $transcript = Join-Path $RowRoot 'transcript.log'
    $stdout = Join-Path $RowRoot 'qemu.stdout.log'
    $stderr = Join-Path $RowRoot 'qemu.stderr.log'
    $runImageArg = ([IO.Path]::GetFullPath($media.Image)).Replace('\', '/')
    $serialArg = 'file:' + ([IO.Path]::GetFullPath($transcript)).Replace('\', '/')
    $arguments = @()
    for ($index = 0; $index -lt $Row.Args.Count; $index++) {
        $arg = [string]$Row.Args[$index]
        if ($arg -eq '-nographic') { continue }
        $arg = $arg.Replace($Row.ImageArg, $runImageArg)
        if ($arg -eq '__SOSIX_RISCV64_FIRMWARE__') { $arg = $firmware.Native.Replace('\', '/') }
        $arguments += $arg
    }
    $arguments += @('-display','none','-monitor','none','-serial',$serialArg,'-accel',$Accelerator)
    $argumentLine = (($arguments | ForEach-Object { Quote-WindowsNativeArgument $_ }) -join ' ')
    $argvFile = Join-Path $RowRoot 'qemu.argv'
    $versionFile = Join-Path $RowRoot 'qemu.version'
    $markersFile = Join-Path $RowRoot 'required-markers.txt'
    $markers = Get-SosixRequiredMarkers -Row $Row -Firmware $firmware `
        -WorkloadNonce $WorkloadNonce -CollectorNonce $CollectorNonce
    Write-SosixLfAsciiRecord -Path $argvFile -Lines @(
        (Quote-WindowsNativeArgument $Admission.SharedQemu) + ' ' + $argumentLine)
    Write-SosixLfAsciiRecord -Path $versionFile -Lines @(
        (Get-RequiredRecordField $Admission.Record 'qemu_version'))
    Write-SosixLfAsciiRecord -Path $markersFile -Lines $markers

    $process = Start-Process -FilePath $Admission.NativeQemu -ArgumentList $argumentLine `
        -WorkingDirectory $script:RepoRoot -RedirectStandardOutput $stdout `
        -RedirectStandardError $stderr -NoNewWindow -PassThru
    if (-not $process.WaitForExit($Timeout * 1000)) {
        Stop-Process -Id $process.Id -Force -ErrorAction SilentlyContinue
        throw "qemu-timeout:$($Row.Guest):${Timeout}s"
    }
    if (-not (Test-Path -LiteralPath $transcript -PathType Leaf)) {
        throw "missing-qemu-serial-transcript:$transcript"
    }
    $serial = Get-Content -LiteralPath $transcript -Raw
    Assert-SosixOrderedTranscript -Transcript $serial -Markers $markers `
        -WorkloadNonce $WorkloadNonce -CollectorNonce $CollectorNonce
    return [pscustomobject]@{
        Media=$media
        Firmware=$firmware
        Transcript=$transcript
        Argv=$argvFile
        Version=$versionFile
        Markers=$markersFile
        ExitCode=$process.ExitCode
    }
}

function Invoke-SosixWindowsBundleProducer {
    param(
        [Parameter(Mandatory=$true)][object]$Row,
        [Parameter(Mandatory=$true)][object]$Admission,
        [Parameter(Mandatory=$true)][object]$RunResult,
        [Parameter(Mandatory=$true)][string]$Accelerator,
        [Parameter(Mandatory=$true)][string]$CollectorNonce,
        [Parameter(Mandatory=$true)][string]$OutputRoot
    )
    $owner = if ($env:SOSIX_QEMU_OWNER) { $env:SOSIX_QEMU_OWNER } else { 'windows-operator' }
    $reviewer = if ($env:SOSIX_QEMU_REVIEWER) { $env:SOSIX_QEMU_REVIEWER } else { 'root-high' }
    $arguments = @(
        '--host','windows','--guest',$Row.Guest,
        '--output',(Convert-ToSharedPath $OutputRoot),
        '--admission',(Convert-ToSharedPath $Admission.Path),
        '--qemu-binary',$Admission.SharedQemu,
        '--qemu-argv-file',(Convert-ToSharedPath $RunResult.Argv),
        '--qemu-version-file',(Convert-ToSharedPath $RunResult.Version),
        '--accelerator',$Accelerator,
        '--firmware',$RunResult.Firmware.Shared,
        '--firmware-id',$RunResult.Firmware.Id,
        '--firmware-mode',$Row.FirmwareMode,
        '--firmware-version',$RunResult.Firmware.Version,
        '--firmware-stages',$RunResult.Firmware.Stages,
        '--kernel',(Convert-ToSharedPath $Row.Kernel),
        '--image',(Convert-ToSharedPath $RunResult.Media.Image),
        '--program',(Convert-ToSharedPath $RunResult.Media.Program),
        '--transcript',(Convert-ToSharedPath $RunResult.Transcript),
        '--required-markers-file',(Convert-ToSharedPath $RunResult.Markers),
        '--nonce',$CollectorNonce,
        '--owner',$owner,'--reviewer',$reviewer,
        '--compiler-identity','not-in-filesystem',
        '--source',(Convert-ToSharedPath $script:RepoRoot)
    )
    $result = Invoke-SosixShellTool `
        -Script 'scripts/check/produce-sosix-qemu-native-pass-bundle.shs' `
        -Arguments $arguments
    if ($result.ExitCode -ne 0) {
        throw "canonical-producer-failed:$($result.Lines -join ';')"
    }
    $bundleShared = @($result.Lines | Where-Object { $_ -like 'sosix_qemu_native_pass_bundle=*' })
    if ($bundleShared.Count -ne 1) { throw 'canonical-producer-bundle-path-missing-or-duplicate' }
    $bundle = Convert-ToNativePath ($bundleShared[0].Substring('sosix_qemu_native_pass_bundle='.Length))
    if (-not (Test-Path -LiteralPath $bundle -PathType Leaf)) {
        throw "canonical-producer-bundle-missing:$bundle"
    }
    return $bundle
}

if ($SelfTest) {
    $descriptors = Get-RowDescriptors (Get-RepoRoot)
    if ($descriptors.Count -ne 6 -or @($descriptors.Guest | Select-Object -Unique).Count -ne 6) {
        throw 'matrix self-test: descriptors must be six and unique'
    }
    foreach ($row in $descriptors) {
        $mediaReferences = @($row.Args | Where-Object { ([string]$_).Contains($row.ImageArg) }).Count
        if ($mediaReferences -ne 1) { throw "matrix self-test: $($row.Guest) must bind exactly one image argument" }
        if ($row.FirmwareStages -notmatch 'guest-entry$') { throw "matrix self-test: $($row.Guest) lacks guest-entry stage" }
    }
    if (@($descriptors | Where-Object CollectorNonceEcho).Count -ne 6 -or
        @($descriptors | Where-Object { -not $_.CollectorNonceEcho }).Count -ne 0) {
        throw 'matrix self-test: all six source-proven collector nonce echoes must be enabled'
    }
    $runReady = @($descriptors | Where-Object RunContractReady).Guest
    if ($runReady.Count -ne 2 -or $runReady -notcontains 'x86_64' -or $runReady -notcontains 'arm32') {
        throw 'matrix self-test: only x86_64 and arm32 have the complete source-proven run contract'
    }
    if ((Get-RowAccelerator 'x86_64' 'x86_64' 'whpx') -ne 'whpx') { throw 'matrix self-test: native x86_64 must retain WHPX' }
    if ((Get-RowAccelerator 'x86_64' 'arm64' 'whpx') -ne 'tcg') { throw 'matrix self-test: cross-ISA arm64 must fall back to TCG' }
    if ((Get-RowAccelerator 'arm64' 'arm32' 'whpx') -ne 'whpx') { throw 'matrix self-test: compatible arm32 must retain WHPX' }
    $wireFixture = [IO.Path]::GetTempFileName()
    try {
        Write-SosixLfAsciiRecord -Path $wireFixture -Lines @('alpha=1','beta=2')
        $expectedWire = [Text.Encoding]::ASCII.GetBytes("alpha=1`nbeta=2`n")
        $actualWire = [IO.File]::ReadAllBytes($wireFixture)
        if ([Convert]::ToBase64String($actualWire) -ne [Convert]::ToBase64String($expectedWire)) {
            throw 'matrix self-test: shared records must use LF-only ASCII bytes'
        }
    } finally {
        Remove-Item -LiteralPath $wireFixture -Force -ErrorAction SilentlyContinue
    }
    'sosix_qemu_matrix_windows_self_test=pass'
    exit 0
}

if ($AllGuests -and $Guest) { Fail-Usage 'choose -AllGuests or -Guest, not both' }
if (-not $AllGuests -and -not $Guest) { Fail-Usage '-AllGuests or -Guest is required' }
if ($Parallel) { Fail-Usage '-Parallel is not implemented; process-global shell environments require serial rows' }
if ($Run -and $Preflight) { Fail-Usage 'choose -Run or -Preflight, not both' }

$script:RepoRoot = Get-RepoRoot
$mode = if ($Run) { 'run' } else { 'preflight' }
$runId = if ($env:SOSIX_QEMU_RUN_ID) { $env:SOSIX_QEMU_RUN_ID } else { (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ') }
if ($runId -notmatch '^[A-Za-z0-9][A-Za-z0-9._-]{0,47}$') { Fail-Usage 'unsafe or overlong SOSIX_QEMU_RUN_ID' }
$requestedAccelerator = if ($env:SIMPLE_QEMU_ACCELERATOR) { $env:SIMPLE_QEMU_ACCELERATOR } else { 'whpx' }
if ($requestedAccelerator -notin @('whpx', 'tcg')) { Fail-Usage "invalid Windows accelerator: $requestedAccelerator" }

try {
    $settings = Get-SosixSharedSettings $requestedAccelerator
    $artifactRoot = Convert-ToNativePath (Get-RequiredRecordField $settings 'simple_qemu_artifact_root')
} catch {
    [Console]::Error.WriteLine("check-sosix-qemu-matrix.ps1: Validate shared settings: $($_.Exception.Message)")
    exit 1
}

$runRoot = Join-Path $artifactRoot "sosix-qemu/windows/matrix/$runId"
$bundleRoot = Join-Path $artifactRoot 'sosix-qemu/native'
New-Item -ItemType Directory -Force -Path $runRoot | Out-Null
$report = Join-Path $runRoot 'matrix.env'
Set-Content -LiteralPath $report -Value $null
function Emit([string]$Line) { $Line; Add-Content -LiteralPath $report -Value $Line }

$hostIsa = Get-WindowsHostIsa
$rows = Get-RowDescriptors $script:RepoRoot
if ($Guest) { $rows = @($rows | Where-Object Guest -eq $Guest) }

Emit 'sosix_qemu_matrix_host=windows'
Emit "sosix_qemu_matrix_mode=$mode"
Emit ("sosix_qemu_matrix_guest_selection=" + $(if ($AllGuests) { 'all' } else { $Guest }))
Emit 'sosix_qemu_matrix_execution=serial'
Emit "sosix_qemu_matrix_accelerator=$requestedAccelerator"
Emit "sosix_qemu_matrix_host_isa=$hostIsa"
Emit "sosix_qemu_matrix_artifact_root=$runRoot"
Emit 'sosix_qemu_matrix_step_1=Validate shared settings'
Emit 'sosix_qemu_matrix_step_2=Admit the native host row'
Emit 'sosix_qemu_matrix_step_3=Prepare isolated nonce media'
Emit 'sosix_qemu_matrix_step_4=Run mounted filesystem execution'
Emit 'sosix_qemu_matrix_step_5=Produce the canonical row bundle'
Emit 'sosix_qemu_matrix_step_6=Collect exactly 24 rows (parent-only)'

$blocked = 0
$passed = 0
$ready = 0
foreach ($row in $rows) {
    $prefix = "sosix_qemu_matrix_windows_$($row.Guest)"
    $rowRoot = Join-Path $runRoot $row.Guest
    New-Item -ItemType Directory -Force -Path $rowRoot | Out-Null
    $receipt = Join-Path $rowRoot 'row-receipt.env'
    $acceptanceId = "SOSIX-WINDOWS-$($row.Guest.ToUpperInvariant())"
    $rowAccelerator = Get-RowAccelerator $hostIsa $row.Guest $requestedAccelerator
    $workloadNonce = "W-$runId-$($row.Guest)"
    $collectorNonce = "C-$runId-$($row.Guest)"
    Emit "${prefix}_kernel=$($row.Kernel)"
    Emit "${prefix}_image=$($row.Image)"
    Emit "${prefix}_spec=$($row.Spec)"
    Emit "${prefix}_accelerator=$rowAccelerator"
    Emit "${prefix}_receipt=$receipt"
    Emit ("${prefix}_native_timing_applicable=" + $(if ($rowAccelerator -eq 'tcg') { 'false' } else { 'true' }))
    try {
        if ($env:OS -ne 'Windows_NT') { throw 'actual-host-is-not-windows' }
        foreach ($path in @($row.Kernel, $row.Image, $row.Spec)) {
            if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { throw "missing-input:$path" }
        }
        Assert-SosixKernelContract $row
        $admissionPath = Join-Path $rowRoot 'host-admission.env'
        $admission = New-SosixWindowsAdmission -Row $row -Settings $settings `
            -Accelerator $rowAccelerator -AdmissionPath $admissionPath
        if (-not $row.CollectorNonceEcho) {
            throw "collector-nonce-echo-not-implemented:$($row.Guest)"
        }
        if (-not $row.RunContractReady) {
            throw "guest-run-contract-not-implemented:$($row.Guest)"
        }
        if (-not $Run) {
            Write-SosixRowReceipt -Path $receipt -AcceptanceId $acceptanceId -Mode $mode `
                -Status ready -Reason 'host-admitted-artifacts-present'
            Emit "${prefix}_status=ready"
            Emit "${prefix}_reason=host-admitted-artifacts-present"
            $ready++
            continue
        }
        $runResult = Invoke-SosixWindowsGuestRow -Row $row -Admission $admission `
            -Accelerator $rowAccelerator -RowRoot $rowRoot -WorkloadNonce $workloadNonce `
            -CollectorNonce $collectorNonce -Timeout $TimeoutSeconds
        $bundle = Invoke-SosixWindowsBundleProducer -Row $row -Admission $admission `
            -RunResult $runResult -Accelerator $rowAccelerator -CollectorNonce $collectorNonce `
            -OutputRoot $bundleRoot
        Write-SosixRowReceipt -Path $receipt -AcceptanceId $acceptanceId -Mode $mode `
            -Status pass -Reason 'canonical-producer-accepted-real-guest-evidence' `
            -CanonicalBundle $bundle
        Emit "${prefix}_run_status=pass"
        Emit "${prefix}_canonical_bundle=$bundle"
        $passed++
    } catch {
        $reason = $_.Exception.Message.Replace("`r", ' ').Replace("`n", ' ')
        $status = if ($Run) { 'failed' } else { 'blocked' }
        Write-SosixRowReceipt -Path $receipt -AcceptanceId $acceptanceId -Mode $mode `
            -Status $status -Reason $reason
        Emit "${prefix}_status=$status"
        Emit "${prefix}_reason=$reason"
        $blocked++
    }
}

Emit "sosix_qemu_matrix_ready_count=$ready"
Emit "sosix_qemu_matrix_pass_count=$passed"
Emit "sosix_qemu_matrix_blocked_count=$blocked"
if ($blocked -ne 0) {
    Emit ("sosix_qemu_matrix_status=" + $(if ($Run) { 'failed' } else { 'blocked' }))
    exit 1
}
if ($Run) {
    if ($passed -ne $rows.Count) { Emit 'sosix_qemu_matrix_status=failed'; exit 1 }
    Emit 'sosix_qemu_matrix_status=pass'
    exit 0
}
if ($ready -ne $rows.Count) { Emit 'sosix_qemu_matrix_status=blocked'; exit 1 }
Emit 'sosix_qemu_matrix_status=ready'
