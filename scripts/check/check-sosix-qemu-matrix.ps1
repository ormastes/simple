# Native Windows SOSIX/SimpleOS six-guest QEMU matrix preflight and runner.
[CmdletBinding()]
param(
    [ValidateSet("x86_32", "x86_64", "arm32", "arm64", "riscv32", "riscv64")]
    [string]$Guest,
    [switch]$AllGuests,
    [switch]$Preflight,
    [switch]$Run,
    [switch]$Parallel,
    [switch]$SelfTest
)

$ErrorActionPreference = "Stop"
$script:CanonicalGuests = @("x86_32", "x86_64", "arm32", "arm64", "riscv32", "riscv64")
$script:RepoRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot "..\.."))

function Stop-Usage([string]$Message) {
    [Console]::Error.WriteLine("check-sosix-qemu-matrix: $Message")
    exit 64
}

function Test-MatrixArguments(
    [string]$SelectedGuest,
    [bool]$SelectAll,
    [bool]$SelectPreflight,
    [bool]$SelectRun,
    [bool]$SelectParallel,
    [bool]$SelectSelfTest
) {
    if ($SelectSelfTest) {
        if (-not [string]::IsNullOrWhiteSpace($SelectedGuest) -or $SelectAll -or
            $SelectPreflight -or $SelectRun -or $SelectParallel) {
            return "-SelfTest cannot be combined with matrix options"
        }
        return $null
    }
    if ([string]::IsNullOrWhiteSpace($SelectedGuest) -eq (-not $SelectAll)) {
        return "choose exactly one of -Guest or -AllGuests"
    }
    if ($SelectPreflight -and $SelectRun) {
        return "choose -Preflight or -Run, not both"
    }
    if ($SelectParallel -and -not $SelectAll) {
        return "-Parallel requires -AllGuests"
    }
    return $null
}

function Assert-SelfTest([bool]$Condition, [string]$Reason) {
    if (-not $Condition) {
        Write-Output "sosix_qemu_matrix_windows_self_test=failed:$Reason"
        exit 1
    }
}

function Test-WindowsHostAdmission([bool]$IsWindows, [bool]$SelfTestMode) {
    return $SelfTestMode -or $IsWindows
}

function Get-RowAccelerator([string]$GuestName, [string]$RequestedAccelerator) {
    if ($RequestedAccelerator -eq "whpx" -and $GuestName -notin @("x86_32", "x86_64")) {
        return "tcg"
    }
    return $RequestedAccelerator
}

function Get-AggregatedResults([object[]]$Results, [string[]]$ExpectedGuests) {
    $ordered = foreach ($name in $ExpectedGuests) {
        $matches = @($Results | Where-Object { $_.Guest -eq $name })
        if ($matches.Count -eq 1) {
            $matches[0]
        } else {
            [pscustomobject]@{
                Guest = $name
                Passed = $false
                Reason = "aggregation-result-count:$($matches.Count)"
            }
        }
    }
    [pscustomobject]@{
        Results = @($ordered)
        FailedCount = @($ordered | Where-Object { -not $_.Passed }).Count
    }
}

function Invoke-SelfTest {
    Assert-SelfTest (-not (Test-WindowsHostAdmission $false $false)) "non-windows-host-accepted"
    Assert-SelfTest (Test-WindowsHostAdmission $false $true) "non-windows-self-test-rejected"
    Assert-SelfTest (Test-WindowsHostAdmission $true $false) "windows-host-rejected"
    Assert-SelfTest ((Get-RowAccelerator "x86_64" "whpx") -eq "whpx") "native-x86-accelerator-changed"
    Assert-SelfTest ((Get-RowAccelerator "arm64" "whpx") -eq "tcg") "cross-isa-whpx-not-lowered-to-tcg"
    Assert-SelfTest ($null -eq (Test-MatrixArguments "x86_64" $false $true $false $false $false)) "single-selection-rejected"
    Assert-SelfTest ($null -eq (Test-MatrixArguments "" $true $false $true $true $false)) "parallel-all-rejected"
    Assert-SelfTest ($null -ne (Test-MatrixArguments "x86_64" $true $true $false $false $false)) "ambiguous-selection-accepted"
    Assert-SelfTest ($null -ne (Test-MatrixArguments "x86_64" $false $true $false $true $false)) "parallel-single-accepted"
    Assert-SelfTest ($null -ne (Test-MatrixArguments "" $true $true $true $false $false)) "ambiguous-mode-accepted"

    $simulated = @(
        [pscustomobject]@{ Guest = "riscv64"; Passed = $true },
        [pscustomobject]@{ Guest = "arm32"; Passed = $false },
        [pscustomobject]@{ Guest = "x86_64"; Passed = $true },
        [pscustomobject]@{ Guest = "riscv32"; Passed = $true },
        [pscustomobject]@{ Guest = "x86_32"; Passed = $true },
        [pscustomobject]@{ Guest = "arm64"; Passed = $true }
    )
    $aggregate = Get-AggregatedResults $simulated $script:CanonicalGuests
    Assert-SelfTest ($aggregate.Results.Count -eq 6) "aggregation-dropped-row"
    Assert-SelfTest ($aggregate.FailedCount -eq 1) "aggregation-failure-count"
    Assert-SelfTest (($aggregate.Results.Guest -join ",") -eq ($script:CanonicalGuests -join ",")) "aggregation-order"
    $missingAggregate = Get-AggregatedResults @($simulated | Where-Object { $_.Guest -ne "riscv64" }) $script:CanonicalGuests
    Assert-SelfTest ($missingAggregate.FailedCount -eq 2) "aggregation-missing-row-not-failed"
    Assert-SelfTest (($missingAggregate.Results | Where-Object { $_.Guest -eq "riscv64" }).Reason -eq "aggregation-result-count:0") "aggregation-missing-row-reason"
    Write-Output "sosix_qemu_matrix_windows_self_test=pass"
}

$argumentError = Test-MatrixArguments $Guest $AllGuests.IsPresent $Preflight.IsPresent $Run.IsPresent $Parallel.IsPresent $SelfTest.IsPresent
if ($null -ne $argumentError) {
    Stop-Usage $argumentError
}
if ($SelfTest) {
    Invoke-SelfTest
    exit 0
}
$isWindows = [System.Runtime.InteropServices.RuntimeInformation]::IsOSPlatform(
    [System.Runtime.InteropServices.OSPlatform]::Windows
)
if (-not (Test-WindowsHostAdmission $isWindows $false)) {
    [Console]::Error.WriteLine("check-sosix-qemu-matrix: native matrix execution requires Windows")
    exit 2
}
if (-not $Preflight -and -not $Run) {
    $Preflight = $true
}

function Resolve-BigStorageRoot {
    if (-not [string]::IsNullOrWhiteSpace($env:SIMPLE_BIG_STORAGE_ROOT)) {
        $root = $env:SIMPLE_BIG_STORAGE_ROOT
    } else {
        $config = $env:SIMPLE_BIG_STORAGE_CONFIG
        if ([string]::IsNullOrWhiteSpace($config)) {
            $config = Join-Path $script:RepoRoot ".simple-big-storage-root"
        } elseif (-not [System.IO.Path]::IsPathRooted($config)) {
            $config = Join-Path $script:RepoRoot $config
        }
        if (Test-Path -LiteralPath $config -PathType Leaf) {
            $root = (Get-Content -LiteralPath $config -TotalCount 1).Trim()
        } else {
            $root = Join-Path ([Environment]::GetFolderPath("UserProfile")) ".simple"
        }
    }
    if ([string]::IsNullOrWhiteSpace($root) -or -not [System.IO.Path]::IsPathRooted($root)) {
        throw "simple big-storage root must be an absolute path: $root"
    }
    return [System.IO.Path]::GetFullPath($root)
}

function Resolve-Executable([string]$Candidate) {
    if ([string]::IsNullOrWhiteSpace($Candidate)) {
        return $null
    }
    if (Test-Path -LiteralPath $Candidate -PathType Leaf) {
        return (Resolve-Path -LiteralPath $Candidate).Path
    }
    $command = Get-Command $Candidate -CommandType Application -ErrorAction SilentlyContinue
    if ($null -ne $command) {
        return $command.Source
    }
    return $null
}

function Hash([string]$Path) {
    (Get-FileHash -LiteralPath (Resolve-RepoInput $Path) -Algorithm SHA256).Hash.ToLowerInvariant()
}

function Invoke-QemuAcceleratorProbe([string]$QemuPath, [string]$Accelerator) {
    $help = (& $QemuPath -accel help 2>&1 | Out-String)
    if ($LASTEXITCODE -ne 0) {
        return [pscustomobject]@{ Passed = $false; Reason = "accel-help-failed" }
    }
    $advertised = @($help -split "[^A-Za-z0-9_]+" | Where-Object { $_ -eq $Accelerator }).Count -gt 0
    if (-not $advertised) {
        return [pscustomobject]@{ Passed = $false; Reason = "accelerator-not-advertised" }
    }

    $start = [System.Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $QemuPath
    $start.Arguments = "-machine none -accel $Accelerator -nodefaults -display none -qmp stdio"
    $start.UseShellExecute = $false
    $start.RedirectStandardInput = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.CreateNoWindow = $true
    $process = [System.Diagnostics.Process]::new()
    $process.StartInfo = $start
    try {
        if (-not $process.Start()) {
            return [pscustomobject]@{ Passed = $false; Reason = "accelerator-probe-start-failed" }
        }
        $process.StandardInput.WriteLine('{"execute":"qmp_capabilities"}')
        $process.StandardInput.WriteLine('{"execute":"quit"}')
        $process.StandardInput.Close()
        if (-not $process.WaitForExit(5000)) {
            $process.Kill()
            $process.WaitForExit()
            return [pscustomobject]@{ Passed = $false; Reason = "accelerator-probe-timeout" }
        }
        $probeOutput = $process.StandardOutput.ReadToEnd()
        $probeError = $process.StandardError.ReadToEnd()
        if ($process.ExitCode -ne 0 -or $probeOutput -notmatch '"return"') {
            return [pscustomobject]@{ Passed = $false; Reason = "accelerator-runtime-rejected:$($process.ExitCode)"; Detail = $probeError.Trim() }
        }
        return [pscustomobject]@{ Passed = $true; Reason = "accelerator-executed" }
    } catch {
        return [pscustomobject]@{ Passed = $false; Reason = "accelerator-probe-exception:$($_.Exception.GetType().Name)" }
    } finally {
        $process.Dispose()
    }
}

function Get-QemuPath([string]$Name) {
    $fileName = "$Name.exe"
    if (-not [string]::IsNullOrWhiteSpace($env:SIMPLE_QEMU_BIN_DIR)) {
        $binDir = $env:SIMPLE_QEMU_BIN_DIR
        if (-not [System.IO.Path]::IsPathRooted($binDir)) {
            $binDir = Join-Path $script:RepoRoot $binDir
        }
        return Join-Path $binDir $fileName
    }
    return $fileName
}

function Get-SimplePath {
    if (-not [string]::IsNullOrWhiteSpace($env:SIMPLE_BIN)) {
        return $env:SIMPLE_BIN
    }
    $workspaceBinary = Join-Path $script:RepoRoot "bin\simple.exe"
    if (Test-Path -LiteralPath $workspaceBinary -PathType Leaf) {
        return $workspaceBinary
    }
    return "simple.exe"
}

. (Join-Path $PSScriptRoot "lib\sosix-qemu-compiler-designation.ps1") -Consumer matrix

$compilerDesignationPolicy=Read-SosixQemuCompilerDesignationPolicy (Join-Path $PSScriptRoot "lib\sosix-qemu-compiler-designation-v1.tsv")
$rows = @(
    [pscustomobject]@{ Guest = "x86_32"; Qemu = (Get-QemuPath "qemu-system-x86_64"); Kernel = "build\os\simpleos_x86_32_initrd_fs_exec_probe.elf"; Image = "build\os\fat32-x86_32.img"; Spec = "test\03_system\os\qemu\sys_qemu_x86_32_fs_exec_spec.spl" },
    [pscustomobject]@{ Guest = "x86_64"; Qemu = (Get-QemuPath "qemu-system-x86_64"); Kernel = "build\os\simpleos_x86_64_fs_exec.elf"; Image = "build\os\fat32-x86_64.img"; Spec = "test\03_system\os\qemu\sys_qemu_x86_64_fs_exec_spec.spl" },
    [pscustomobject]@{ Guest = "arm32"; Qemu = (Get-QemuPath "qemu-system-arm"); Kernel = "build\os\simpleos_arm32_fs_exec.elf"; Image = "build\os\fat32-arm32.img"; Spec = "test\03_system\os\qemu\sys_qemu_arm32_fs_exec_spec.spl" },
    [pscustomobject]@{ Guest = "arm64"; Qemu = (Get-QemuPath "qemu-system-aarch64"); Kernel = "build\os\simpleos_arm64_fs_exec.elf"; Image = "build\os\fat32-arm64.img"; Spec = "test\03_system\os\qemu\sys_qemu_arm64_fs_exec_spec.spl" },
    [pscustomobject]@{ Guest = "riscv32"; Qemu = (Get-QemuPath "qemu-system-riscv32"); Kernel = "build\os\simpleos_riscv32_smf_fs.elf"; Image = "build\os\fat32-riscv32.img"; Spec = "test\03_system\os\qemu\sys_qemu_riscv32_fs_exec_spec.spl" },
    [pscustomobject]@{ Guest = "riscv64"; Qemu = (Get-QemuPath "qemu-system-riscv64"); Kernel = "build\os\simpleos_riscv64_smf_fs.elf"; Image = "build\os\fat32-riscv64.img"; Spec = "test\03_system\os\qemu\sys_qemu_riscv64_fs_exec_spec.spl" }
)
foreach ($row in $rows) {
    $designated=$compilerDesignationPolicy["windows|$($row.Guest)"] -eq "true"
    Add-Member -InputObject $row -NotePropertyName CompilerInFilesystem -NotePropertyValue $designated
    Add-Member -InputObject $row -NotePropertyName CompilerVersionEvidencePath -NotePropertyValue ""
    Add-Member -InputObject $row -NotePropertyName CompilerHelloEvidencePath -NotePropertyValue ""
    Add-Member -InputObject $row -NotePropertyName CompilerAliasEvidencePath -NotePropertyValue ""
    Add-Member -InputObject $row -NotePropertyName CompilerManifestEvidencePath -NotePropertyValue ""
}
if (-not $AllGuests) {
    $rows = @($rows | Where-Object { $_.Guest -eq $Guest })
}

$storageRoot = Resolve-BigStorageRoot
$artifactRoot = Join-Path $storageRoot "qemu\artifacts"
$runId = [DateTime]::UtcNow.ToString("yyyyMMddTHHmmssZ")
$runRoot = Join-Path $artifactRoot "sosix-qemu\windows\matrix\$runId"
[System.IO.Directory]::CreateDirectory($runRoot) | Out-Null
foreach ($row in $rows) {
    if ($row.CompilerInFilesystem) {
        $row.CompilerVersionEvidencePath=Join-Path $runRoot "$($row.Guest).compiler-version.txt"
        $row.CompilerHelloEvidencePath=Join-Path $runRoot "$($row.Guest).compiler-hello.txt"
        $row.CompilerAliasEvidencePath=Join-Path $runRoot "$($row.Guest).compiler-aliases.txt"
        $row.CompilerManifestEvidencePath=Join-Path $runRoot "$($row.Guest).compiler-manifest.env"
    }
}
$report = Join-Path $runRoot "matrix.env"
[System.IO.File]::WriteAllText($report, "", [System.Text.UTF8Encoding]::new($false))

function Write-Receipt([string]$Line) {
    Write-Output $Line
    [System.IO.File]::AppendAllText($report, "$Line`n", [System.Text.UTF8Encoding]::new($false))
}

function Write-HostAdmission([object]$Row, [string]$QemuPath, [string]$RowAccelerator) {
    $version = ((& $QemuPath --version 2>&1 | Select-Object -First 1) -as [string])
    if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($version)) { throw "qemu-version-failed:$($Row.Guest)" }
    $path = Join-Path $runRoot "$($Row.Guest).host-admission.env"
    $lines = @(
        "detected_host=windows", "requested_host=windows", "host_identity_status=pass",
        "host_identity_reason=matched", "qemu_binary=$QemuPath", "qemu_binary_resolved=$QemuPath",
        "qemu_sha256=$((Get-FileHash -LiteralPath $QemuPath -Algorithm SHA256).Hash.ToLowerInvariant())",
        "qemu_version=$version", "requested_accelerator=$RowAccelerator",
        "accelerator_advertised_status=pass", "accelerator_advertised_reason=advertised",
        "accelerator_probe_status=pass", "accelerator_probe_reason=accelerator-executed",
        "native_timing_applicable=$(if ($RowAccelerator -eq 'tcg') { 'false' } else { 'true' })",
        "simple_qemu_storage_root=$storageRoot"
    )
    [System.IO.File]::WriteAllLines($path,$lines,[System.Text.UTF8Encoding]::new($false))
    return $path
}

function Read-NativePassDescriptor([string]$Path) {
    $required = @("schema_version","nonce","qemu_argv_file","firmware_path","firmware_id","firmware_mode","firmware_version","firmware_stages","boot_correlation_marker","program_path","transcript_path","required_markers_file","owner","reviewer","compiler_identity","kernel_identity","image_identity")
    $optional = @("compiler_version_evidence_path","compiler_hello_evidence_path","compiler_alias_evidence_path","compiler_manifest_evidence_path")
    $allowed = @($required + $optional)
    $values=@{}
    foreach ($line in [System.IO.File]::ReadAllLines($Path)) {
        $at=$line.IndexOf('='); if ($at -le 0) { throw "native-pass-descriptor-malformed:$Path" }
        $key=$line.Substring(0,$at); if ($key -notin $allowed -or $values.ContainsKey($key)) { throw "native-pass-descriptor-open-or-duplicate:$key" }
        $values[$key]=$line.Substring($at+1)
    }
    foreach ($key in $required) { if (-not $values.ContainsKey($key) -or [string]::IsNullOrWhiteSpace($values[$key])) { throw "native-pass-descriptor-missing:$key" } }
    if ($values.schema_version -ne "1") { throw "native-pass-descriptor-version" }
    return $values
}

function Assert-CurrentGuestReceipt(
    [object]$Row,
    [hashtable]$Descriptor,
    [string]$KernelPath,
    [string]$ImagePath,
    [string]$RunIdentifier
) {
    $expectedNonce = "$RunIdentifier-windows-$($Row.Guest)"
    if ($Descriptor.nonce -cne $expectedNonce) { throw "native-pass-receipt-stale:$($Row.Guest)" }
    $serialPath = Join-Path $script:RepoRoot "build\os\systest\$($Row.Guest).serial.log"
    if (-not (Test-Path -LiteralPath $serialPath -PathType Leaf)) { throw "native-pass-receipt-missing-serial:$serialPath" }
    $lines = @([System.IO.File]::ReadAllLines($serialPath))
    $stages = switch ($Descriptor.firmware_mode) {
        "uefi-pflash" { "firmware-entry>firmware-handoff>guest-entry" }
        "opensbi-bios" { "opensbi-entry>opensbi-handoff>guest-entry" }
        "board-rom" { "rom-entry>rom-handoff>guest-entry" }
        default { throw "native-pass-receipt-invalid-firmware-mode:$($Row.Guest)" }
    }
    if ($Descriptor.firmware_stages -cne $stages) { throw "native-pass-receipt-firmware-stages:$($Row.Guest)" }
    $positions = @()
    foreach ($stage in ($stages -split '>')) {
        $matches = @(for ($i=0; $i -lt $lines.Count; $i++) { if ($lines[$i] -ceq $stage) { $i } })
        if ($matches.Count -ne 1 -or ($positions.Count -gt 0 -and $matches[0] -le $positions[-1])) { throw "native-pass-receipt-stage-order:$($Row.Guest)" }
        $positions += $matches[0]
    }
    $markerMatches = @(for ($i=0; $i -lt $lines.Count; $i++) { if ($lines[$i] -ceq $Descriptor.boot_correlation_marker) { $i } })
    if ($markerMatches.Count -ne 1 -or $markerMatches[0] -le $positions[1] -or $markerMatches[0] -ge $positions[2]) { throw "native-pass-receipt-boot-marker:$($Row.Guest)" }
    $nonceMatches = @(for ($i=0; $i -lt $lines.Count; $i++) { if ($lines[$i].Contains($Descriptor.nonce,[StringComparison]::Ordinal)) { $i } })
    if ($nonceMatches.Count -eq 0 -or @($nonceMatches | Where-Object { $_ -le $positions[2] }).Count -ne 0) { throw "native-pass-receipt-nonce:$($Row.Guest)" }
    if ($Descriptor.kernel_identity -cne "sha256:$(Hash $KernelPath)" -or $Descriptor.image_identity -cne "sha256:$(Hash $ImagePath)") {
        throw "native-pass-receipt-media-identity:$($Row.Guest)"
    }
}

function Resolve-RepoInput([string]$Path) {
    if ([System.IO.Path]::IsPathRooted($Path)) { return [System.IO.Path]::GetFullPath($Path) }
    return [System.IO.Path]::GetFullPath((Join-Path $script:RepoRoot $Path))
}

function Publish-NativePass([object]$Row) {
    $descriptorPath=Join-Path $script:RepoRoot "build\os\systest\$($Row.Guest).native-pass.env"
    if (-not (Test-Path -LiteralPath $descriptorPath -PathType Leaf)) { throw "native-pass-descriptor-missing:$descriptorPath" }
    $d=Read-NativePassDescriptor $descriptorPath
    $compilerVersionPath=''; $compilerHelloPath=''; $compilerAliasPath=''; $compilerManifestPath=''
    if ($Row.CompilerInFilesystem) {
        foreach ($key in @('compiler_version_evidence_path','compiler_hello_evidence_path','compiler_alias_evidence_path','compiler_manifest_evidence_path')) {
            if (-not $d.ContainsKey($key) -or [string]::IsNullOrWhiteSpace($d[$key])) { throw "native-pass-descriptor-missing:$key" }
        }
        $compilerVersionPath=Resolve-RepoInput $d.compiler_version_evidence_path
        $compilerHelloPath=Resolve-RepoInput $d.compiler_hello_evidence_path
        $compilerAliasPath=Resolve-RepoInput $d.compiler_alias_evidence_path
        $compilerManifestPath=Resolve-RepoInput $d.compiler_manifest_evidence_path
    }
    $qemuPath=Resolve-Executable $Row.Qemu; if ($null -eq $qemuPath) { throw "native-pass-qemu-missing" }
    $rowAccelerator=Get-RowAccelerator $Row.Guest $accelerator
    $admissionPath=Join-Path $runRoot "$($Row.Guest).host-admission.env"
    $versionPath=Join-Path $runRoot "$($Row.Guest).qemu.version"
    $version=((Get-Content -LiteralPath $admissionPath | Where-Object { $_ -like 'qemu_version=*' } | Select-Object -First 1) -replace '^qemu_version=','')
    [System.IO.File]::WriteAllText($versionPath,"$version`n",[System.Text.UTF8Encoding]::new($false))
    $producer=Join-Path $PSScriptRoot "produce-sosix-qemu-native-pass-bundle.ps1"
    $arguments=@{
        HostName="windows"; Guest=$Row.Guest; Output=(Join-Path $artifactRoot "sosix-qemu\native")
        Admission=$admissionPath; QemuBinary=$qemuPath; QemuArgvFile=(Resolve-RepoInput $d.qemu_argv_file)
        QemuVersionFile=$versionPath; Accelerator=$rowAccelerator; Firmware=(Resolve-RepoInput $d.firmware_path)
        FirmwareId=$d.firmware_id; FirmwareMode=$d.firmware_mode; FirmwareVersion=$d.firmware_version
        FirmwareStages=$d.firmware_stages; BootCorrelationMarker=$d.boot_correlation_marker
        Kernel=(Resolve-RepoInput $Row.Kernel); Image=(Resolve-RepoInput $Row.Image)
        Program=(Resolve-RepoInput $d.program_path); Transcript=(Resolve-RepoInput $d.transcript_path)
        RequiredMarkersFile=(Resolve-RepoInput $d.required_markers_file); Nonce=$d.nonce; Owner=$d.owner
        Reviewer=$d.reviewer; CompilerIdentity=$d.compiler_identity
        CompilerInFilesystem=$([string]$Row.CompilerInFilesystem).ToLowerInvariant()
        CompilerVersionEvidence=$compilerVersionPath
        CompilerHelloEvidence=$compilerHelloPath
        CompilerAliasEvidence=$compilerAliasPath
        CompilerManifestEvidence=$compilerManifestPath
        Source=$script:RepoRoot
    }
    Assert-CurrentGuestReceipt $Row $d (Resolve-RepoInput $Row.Kernel) (Resolve-RepoInput $Row.Image) $runId
    & $producer @arguments
}

$mode = if ($Run) { "run" } else { "preflight" }
$accelerator = if ([string]::IsNullOrWhiteSpace($env:SIMPLE_QEMU_ACCELERATOR)) { "whpx" } else { $env:SIMPLE_QEMU_ACCELERATOR }
if ($accelerator -notin @("whpx", "tcg")) {
    Write-Receipt "sosix_qemu_matrix_status=blocked"
    Write-Receipt "sosix_qemu_matrix_reason=invalid-windows-accelerator:$accelerator"
    exit 1
}
Write-Receipt "sosix_qemu_matrix_host=windows"
Write-Receipt "sosix_qemu_matrix_mode=$mode"
Write-Receipt "sosix_qemu_matrix_guest_selection=$(if ($AllGuests) { 'all' } else { $Guest })"
Write-Receipt "sosix_qemu_matrix_execution=$(if ($Parallel) { 'parallel' } else { 'serial' })"
Write-Receipt "sosix_qemu_matrix_accelerator=$accelerator"
Write-Receipt "sosix_qemu_matrix_accelerator_availability=verified-per-row"
Write-Receipt "sosix_qemu_matrix_native_timing_applicable=verified-per-row"
Write-Receipt "sosix_qemu_matrix_artifact_root=$runRoot"

$ready = 0
$blocked = 0
foreach ($row in $rows) {
    $prefix = "sosix_qemu_matrix_windows_$($row.Guest)"
    $kernel = Join-Path $script:RepoRoot $row.Kernel
    $image = Join-Path $script:RepoRoot $row.Image
    $spec = Join-Path $script:RepoRoot $row.Spec
    Write-Receipt "${prefix}_kernel=$kernel"
    Write-Receipt "${prefix}_image=$image"
    Write-Receipt "${prefix}_spec=$spec"
    Write-Receipt "${prefix}_compiler_in_filesystem=$($row.CompilerInFilesystem.ToString().ToLowerInvariant())"
    Write-Receipt "${prefix}_compiler_version_evidence_path=$($row.CompilerVersionEvidencePath)"
    Write-Receipt "${prefix}_compiler_hello_evidence_path=$($row.CompilerHelloEvidencePath)"
    Write-Receipt "${prefix}_compiler_alias_evidence_path=$($row.CompilerAliasEvidencePath)"
    Write-Receipt "${prefix}_compiler_manifest_evidence_path=$($row.CompilerManifestEvidencePath)"
    $qemuPath = Resolve-Executable $row.Qemu
    $rowAccelerator = Get-RowAccelerator $row.Guest $accelerator
    $probe = if ($null -ne $qemuPath) { Invoke-QemuAcceleratorProbe $qemuPath $rowAccelerator } else { $null }
    Write-Receipt "${prefix}_accelerator=$rowAccelerator"
    if ($null -eq $qemuPath) {
        Write-Receipt "${prefix}_status=blocked"
        Write-Receipt "${prefix}_reason=missing-qemu:$($row.Qemu)"
        $blocked++
    } elseif (-not $probe.Passed) {
        Write-Receipt "${prefix}_accelerator_probe_status=failed"
        Write-Receipt "${prefix}_accelerator_probe_reason=$($probe.Reason)"
        Write-Receipt "${prefix}_status=blocked"
        Write-Receipt "${prefix}_reason=host-or-accelerator-admission-failed"
        $blocked++
    } elseif (-not (Test-Path -LiteralPath $kernel -PathType Leaf)) {
        Write-Receipt "${prefix}_status=blocked"
        Write-Receipt "${prefix}_reason=missing-kernel:$kernel"
        $blocked++
    } elseif (-not (Test-Path -LiteralPath $image -PathType Leaf)) {
        Write-Receipt "${prefix}_status=blocked"
        Write-Receipt "${prefix}_reason=missing-image:$image"
        $blocked++
    } elseif (-not (Test-Path -LiteralPath $spec -PathType Leaf)) {
        Write-Receipt "${prefix}_status=blocked"
        Write-Receipt "${prefix}_reason=missing-spec:$spec"
        $blocked++
    } else {
        Write-Receipt "${prefix}_accelerator_probe_status=pass"
        Write-Receipt "${prefix}_accelerator_probe_reason=accelerator-executed"
        Write-Receipt "${prefix}_native_timing_applicable=$(if ($rowAccelerator -eq 'tcg') { 'false' } else { 'true' })"
        Write-Receipt "${prefix}_status=ready"
        Write-Receipt "${prefix}_reason=media-emulator-and-spec-present"
        $admissionPath=Write-HostAdmission $row $qemuPath $rowAccelerator
        Write-Receipt "${prefix}_host_admission=$admissionPath"
        $ready++
    }
}
Write-Receipt "sosix_qemu_matrix_ready_count=$ready"
Write-Receipt "sosix_qemu_matrix_blocked_count=$blocked"

if ($mode -eq "preflight") {
    if ($blocked -gt 0) {
        Write-Receipt "sosix_qemu_matrix_status=blocked"
        exit 1
    }
    Write-Receipt "sosix_qemu_matrix_status=ready"
    exit 0
}

$simpleCandidate = Get-SimplePath
$simpleBinary = Resolve-Executable $simpleCandidate
if ($null -eq $simpleBinary) {
    Write-Receipt "sosix_qemu_matrix_status=blocked"
    Write-Receipt "sosix_qemu_matrix_reason=missing-simple:$simpleCandidate"
    exit 1
}
$versionOutput = (& $simpleBinary --version 2>&1 | Out-String)
$versionExit = $LASTEXITCODE
if ($versionExit -ne 0) {
    Write-Receipt "sosix_qemu_matrix_status=blocked"
    Write-Receipt "sosix_qemu_matrix_reason=simple-version-failed:$versionExit"
    exit 1
}
if ($versionOutput -match "(?i)bootstrap seed only|Rust-built Simple binary") {
    Write-Receipt "sosix_qemu_matrix_status=blocked"
    Write-Receipt "sosix_qemu_matrix_reason=deployed-cli-is-bootstrap-seed"
    exit 1
}
if ($blocked -gt 0) {
    Write-Receipt "sosix_qemu_matrix_status=blocked"
    Write-Receipt "sosix_qemu_matrix_reason=required-row-not-ready"
    exit 1
}

$worker = {
    param($GuestName, $SpecPath, $LogPath, $SimplePath, $RowAccelerator, $RunIdentifier)
    $env:SIMPLE_TIMEOUT_SECONDS = "900"
    $env:SIMPLE_QEMU_ACCELERATOR = $RowAccelerator
    $env:SOSIX_QEMU_NONCE = "$RunIdentifier-windows-$GuestName"
    try {
        & $SimplePath test $SpecPath --no-session-daemon --timeout 180 *> $LogPath
        $processExit = $LASTEXITCODE
        $text = [System.IO.File]::ReadAllText($LogPath)
        if ($processExit -ne 0) {
            return [pscustomobject]@{ Guest = $GuestName; Passed = $false; Reason = "spec-failed:$SpecPath" }
        }
        if ($text -notmatch "SPEC FILE VERDICT:.*failed=0 dropped=0") {
            return [pscustomobject]@{ Guest = $GuestName; Passed = $false; Reason = "missing-authoritative-verdict:$SpecPath" }
        }
        return [pscustomobject]@{ Guest = $GuestName; Passed = $true; Reason = "" }
    } catch {
        return [pscustomobject]@{ Guest = $GuestName; Passed = $false; Reason = "runner-exception:$($_.Exception.GetType().Name)" }
    }
}

$results = @()
if ($Parallel) {
    $jobs = foreach ($row in $rows) {
        $spec = Join-Path $script:RepoRoot $row.Spec
        $log = Join-Path $runRoot "$($row.Guest).log"
        $rowAccelerator = Get-RowAccelerator $row.Guest $accelerator
            Start-Job -Name "sosix-qemu-$($row.Guest)" -ScriptBlock $worker -ArgumentList $row.Guest, $spec, $log, $simpleBinary, $rowAccelerator, $runId
    }
    $null = Wait-Job -Job $jobs -Timeout 900
    foreach ($job in $jobs) {
        if ($job.State -eq "Completed") {
            $received = @(Receive-Job -Job $job)
            $result = $received | Where-Object { $_.PSObject.Properties.Name -contains "Guest" } | Select-Object -Last 1
            if ($null -eq $result) {
                $result = [pscustomobject]@{ Guest = $job.Name.Substring(11); Passed = $false; Reason = "worker-emitted-no-result" }
            }
        } else {
            Stop-Job -Job $job -ErrorAction SilentlyContinue
            $result = [pscustomobject]@{ Guest = $job.Name.Substring(11); Passed = $false; Reason = "worker-timeout-or-state:$($job.State)" }
        }
        $results += $result
    }
    Remove-Job -Job $jobs -Force -ErrorAction SilentlyContinue
} else {
    foreach ($row in $rows) {
        $spec = Join-Path $script:RepoRoot $row.Spec
        $log = Join-Path $runRoot "$($row.Guest).log"
        $rowAccelerator = Get-RowAccelerator $row.Guest $accelerator
        $results += & $worker $row.Guest $spec $log $simpleBinary $rowAccelerator $runId
    }
}

$aggregate = Get-AggregatedResults $results @($rows.Guest)
$publicationFailed=0
foreach ($result in $aggregate.Results) {
    if ($result.Passed) {
        $row=@($rows | Where-Object { $_.Guest -eq $result.Guest })[0]
        try {
            Publish-NativePass $row | ForEach-Object { Write-Receipt "sosix_qemu_matrix_windows_$($result.Guest)_bundle_$_" }
            Write-Receipt "sosix_qemu_matrix_windows_$($result.Guest)_run_status=pass"
        } catch {
            $result.Passed=$false
            $result.Reason="native-pass-publication-failed:$($_.Exception.Message)"
            $publicationFailed++
            Write-Receipt "sosix_qemu_matrix_windows_$($result.Guest)_run_status=failed"
            Write-Receipt "sosix_qemu_matrix_windows_$($result.Guest)_run_reason=$($result.Reason)"
        }
    } else {
        Write-Receipt "sosix_qemu_matrix_windows_$($result.Guest)_run_status=failed"
        Write-Receipt "sosix_qemu_matrix_windows_$($result.Guest)_run_reason=$($result.Reason)"
    }
}
if (($aggregate.FailedCount + $publicationFailed) -gt 0) {
    Write-Receipt "sosix_qemu_matrix_status=failed"
    Write-Receipt "sosix_qemu_matrix_reason=$(if ($Parallel) { 'parallel' } else { 'serial' })-spec-or-publication-failures:$($aggregate.FailedCount + $publicationFailed)"
    exit 1
}
Write-Receipt "sosix_qemu_matrix_status=pass"
