# Native PowerShell parity producer for one collector-ready SOSIX QEMU PASS row.
[CmdletBinding()]
param(
    [Parameter(Mandatory)][ValidateSet("linux","windows","macos","freebsd")][string]$HostName,
    [Parameter(Mandatory)][ValidateSet("x86_32","x86_64","arm32","arm64","riscv32","riscv64")][string]$Guest,
    [Parameter(Mandatory)][string]$Output,
    [Parameter(Mandatory)][string]$Admission,
    [Parameter(Mandatory)][string]$QemuBinary,
    [Parameter(Mandatory)][string]$QemuArgvFile,
    [Parameter(Mandatory)][string]$QemuVersionFile,
    [Parameter(Mandatory)][string]$Accelerator,
    [Parameter(Mandatory)][string]$Firmware,
    [Parameter(Mandatory)][string]$FirmwareId,
    [Parameter(Mandatory)][ValidateSet("uefi-pflash","opensbi-bios","board-rom")][string]$FirmwareMode,
    [Parameter(Mandatory)][string]$FirmwareVersion,
    [Parameter(Mandatory)][string]$FirmwareStages,
    [Parameter(Mandatory)][string]$BootCorrelationMarker,
    [Parameter(Mandatory)][string]$Kernel,
    [Parameter(Mandatory)][string]$Image,
    [Parameter(Mandatory)][string]$Program,
    [Parameter(Mandatory)][string]$Transcript,
    [Parameter(Mandatory)][string]$RequiredMarkersFile,
    [Parameter(Mandatory)][string]$Nonce,
    [Parameter(Mandatory)][string]$Owner,
    [Parameter(Mandatory)][string]$Reviewer,
    [Parameter(Mandatory)][string]$CompilerIdentity,
    [ValidateSet("true","false")][string]$CompilerInFilesystem = "false",
    [string]$CompilerVersionEvidence = "",
    [string]$CompilerHelloEvidence = "",
    [string]$CompilerAliasEvidence = "",
    [string]$CompilerManifestEvidence = "",
    [string]$CompilerDesignationFixture = "",
    [string]$Source = (Join-Path $PSScriptRoot "..\..")
)
$ErrorActionPreference = "Stop"

function Stop-Pass([string]$Reason) { throw "sosix-native-pass: $Reason" }
function Hash([string]$Path) { (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant() }
function One-Line([string]$Path, [string]$Label) {
    $lines = @([System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $Path).Path))
    if ($lines.Count -ne 1 -or [string]::IsNullOrWhiteSpace($lines[0])) { Stop-Pass "$Label must be exactly one nonempty line" }
    $lines[0]
}
function Read-ClosedEnv([string]$Path, [string[]]$Allowed, [string[]]$Required) {
    $values = @{}
    foreach ($line in [System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $Path).Path)) {
        $at = $line.IndexOf('=')
        if ($at -le 0) { Stop-Pass "$Path contains malformed field" }
        $key = $line.Substring(0,$at); $value = $line.Substring($at + 1)
        if ($key -notin $Allowed) { Stop-Pass "$Path contains unknown field $key" }
        if ($values.ContainsKey($key)) { Stop-Pass "$Path duplicates field $key" }
        $values[$key] = $value
    }
    foreach ($key in $Required) { if (-not $values.ContainsKey($key)) { Stop-Pass "$Path misses field $key" } }
    $values
}
function Require-File([string]$Path) { if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { Stop-Pass "missing input $Path" } }
. (Join-Path $PSScriptRoot "lib\sosix-qemu-compiler-designation.ps1") -Consumer producer
function Assert-NoHardlinkAlias([string]$Path) {
    if ($IsWindows -and (Get-Command fsutil.exe -ErrorAction SilentlyContinue)) {
        $links = @(& fsutil.exe hardlink list $Path 2>$null)
        if ($LASTEXITCODE -eq 0 -and $links.Count -gt 1) { Stop-Pass "hard-link evidence alias is not allowed: $Path" }
    }
}
function Assert-FirmwareTranscript([string[]]$Lines, [string]$Mode, [string]$Stages, [string]$BootMarker, [string]$ExecutionNonce) {
    $expected = @{
        "uefi-pflash" = "firmware-entry>firmware-handoff>guest-entry"
        "opensbi-bios" = "opensbi-entry>opensbi-handoff>guest-entry"
        "board-rom" = "rom-entry>rom-handoff>guest-entry"
    }
    if ($Stages -ne $expected[$Mode]) { Stop-Pass "firmware stages do not match mode" }
    $previous = -1; $guestEntry = -1; $lastPreEntry = -1
    foreach ($marker in ($Stages -split '>')) {
        $matches = @(for ($i=0; $i -lt $Lines.Count; $i++) {
            if ([string]::Equals($Lines[$i],$marker,[StringComparison]::Ordinal)) { $i }
        })
        if ($matches.Count -ne 1) { Stop-Pass "firmware stage must occur as exactly one complete line: $marker" }
        if ($matches[0] -le $previous) { Stop-Pass "firmware stage out of order: $marker" }
        $previous=$matches[0]
        if ($marker -eq "guest-entry") { $guestEntry=$matches[0] } else { $lastPreEntry=$matches[0] }
    }
    $bootMatches = @(for ($i=0; $i -lt $Lines.Count; $i++) {
        if ([string]::Equals($Lines[$i],$BootMarker,[StringComparison]::Ordinal)) { $i }
    })
    if ($bootMatches.Count -ne 1) { Stop-Pass "boot-correlation marker must occur as exactly one complete line" }
    if ($bootMatches[0] -le $lastPreEntry -or $bootMatches[0] -ge $guestEntry) { Stop-Pass "boot-correlation marker must be between firmware handoff and guest-entry" }
    $nonceSeen=$false
    for ($i=0; $i -lt $Lines.Count; $i++) {
        if ($Lines[$i].Contains($ExecutionNonce,[StringComparison]::Ordinal)) {
            $nonceSeen=$true; if ($i -le $guestEntry) { Stop-Pass "execution nonce must occur only after guest-entry" }
        }
    }
    if (-not $nonceSeen) { Stop-Pass "execution nonce is absent" }
}
function Assert-CompilerPlacement([string]$PlacementPath, [string]$ManifestPath, [string[]]$TranscriptLines,
    [string]$RowHost, [string]$RowGuest, [string]$ExecutionNonce, [string]$ImageIdentity, [string]$SourceIdentity) {
    $placementLines=@([System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $PlacementPath).Path))
    $manifestLines=@([System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $ManifestPath).Path))
    if ($placementLines.Count -ne 8 -or $manifestLines.Count -ne 1) { Stop-Pass "compiler placement/manifest line count is not closed" }
    $header="SIMPLEOS_COMPILER_PLACEMENT schema=1 host=$RowHost guest=$RowGuest nonce=$ExecutionNonce image_identity=$ImageIdentity"
    if ($placementLines[0] -cne $header) { Stop-Pass "noncanonical compiler placement header" }
    $specs=@(
        @('/usr/bin/simple','compiler',$true), @('/bin/simple','compiler-alias',$true),
        @('/sys/apps/simple','compiler-alias',$true), @('/sys/apps/simple_compiler','compiler-alias',$true),
        @('/sys/apps/simple_interpreter','interpreter',$false), @('/sys/apps/simple_loader','loader',$false),
        @('/SYS/SIMPLETOOL.SDN','toolchain-manifest',$false)
    )
    $payloadIdentity=''
    for ($i=0; $i -lt $specs.Count; $i++) {
        $path=$specs[$i][0]; $role=$specs[$i][1]
        $prefix="SIMPLEOS_COMPILER_READBACK host=$RowHost guest=$RowGuest nonce=$ExecutionNonce path=$path role=$role sha256="
        $suffix=' target_native=true'; $line=$placementLines[$i+1]
        if (-not $line.StartsWith($prefix,[StringComparison]::Ordinal) -or -not $line.EndsWith($suffix,[StringComparison]::Ordinal)) { Stop-Pass "noncanonical compiler readback for $path" }
        $digest=$line.Substring($prefix.Length,$line.Length-$prefix.Length-$suffix.Length)
        if ($digest -notmatch '^[0-9a-f]{64}$') { Stop-Pass "invalid compiler readback digest for $path" }
        if ($i -eq 0) { $payloadIdentity="sha256:$digest" }
        elseif ($specs[$i][2] -and "sha256:$digest" -ne $payloadIdentity) { Stop-Pass "compiler alias digest differs at $path" }
        if (@($TranscriptLines | Where-Object { $_ -ceq $line }).Count -ne 1) { Stop-Pass "compiler readback is not uniquely retained for $path" }
    }
    $placementIdentity="sha256:$(Hash $PlacementPath)"
    $expectedManifest="SIMPLEOS_COMPILER_MANIFEST schema=1 host=$RowHost guest=$RowGuest nonce=$ExecutionNonce source_identity=$SourceIdentity payload_path=/usr/bin/simple payload_identity=$payloadIdentity image_path=guest.img image_identity=$ImageIdentity placement_identity=$placementIdentity"
    if ($manifestLines[0] -cne $expectedManifest -or @($TranscriptLines | Where-Object { $_ -ceq $expectedManifest }).Count -ne 1) { Stop-Pass "compiler manifest does not bind unique target readback lineage" }
    [pscustomobject]@{ Payload=$payloadIdentity; Placement=$placementIdentity; Manifest="sha256:$(Hash $ManifestPath)" }
}

$designationPolicy=Read-SosixQemuCompilerDesignationPolicy (Join-Path $PSScriptRoot "lib\sosix-qemu-compiler-designation-v1.tsv")
$liveCompilerDesignation = $designationPolicy["$HostName|$Guest"]
$fixtureCompilerDesignation = ($env:SOSIX_QEMU_TEST_MODE -eq "1" -and
    $CompilerDesignationFixture -eq "$HostName`:$Guest")
$expectedCompilerDesignation = if ($fixtureCompilerDesignation) { "true" } else { $liveCompilerDesignation }
if ($CompilerInFilesystem -ne $expectedCompilerDesignation) {
    Stop-Pass "compiler designation is not canonical for $HostName/$Guest"
}
if ($CompilerInFilesystem -eq "true") {
    if ([string]::IsNullOrWhiteSpace($CompilerVersionEvidence) -or
        [string]::IsNullOrWhiteSpace($CompilerHelloEvidence) -or
        [string]::IsNullOrWhiteSpace($CompilerAliasEvidence) -or
        [string]::IsNullOrWhiteSpace($CompilerManifestEvidence)) { Stop-Pass "designated compiler row requires version, hello, placement, and manifest evidence files" }
    foreach ($evidence in @($CompilerVersionEvidence,$CompilerHelloEvidence,$CompilerAliasEvidence,$CompilerManifestEvidence)) {
        Require-File $evidence
        $item = Get-Item -LiteralPath $evidence
        if ($item.Attributes -band [IO.FileAttributes]::ReparsePoint) { Stop-Pass "symlink evidence is not allowed: $evidence" }
        if ($item.Length -eq 0) { Stop-Pass "compiler evidence must be non-empty" }
        Assert-NoHardlinkAlias $evidence
    }
    if ([IO.Path]::GetFullPath($CompilerVersionEvidence) -eq [IO.Path]::GetFullPath($CompilerHelloEvidence)) {
        Stop-Pass "compiler evidence inputs must be distinct"
    }
}

foreach ($path in @($Admission,$QemuBinary,$QemuArgvFile,$QemuVersionFile,$Firmware,$Kernel,$Image,$Program,$Transcript,$RequiredMarkersFile)) { Require-File $path }
if ($Nonce -notmatch '^[A-Za-z0-9][A-Za-z0-9._-]{15,127}$') { Stop-Pass "unsafe nonce" }
if ($BootCorrelationMarker -notmatch '^[A-Za-z0-9][A-Za-z0-9._:-]{7,127}$' -or $BootCorrelationMarker -ceq $Nonce) { Stop-Pass "unsafe or non-distinct boot-correlation marker" }
if ($FirmwareId -notmatch '^[A-Za-z0-9][A-Za-z0-9._+-]*$' -or $FirmwareVersion -notmatch '^[A-Za-z0-9][A-Za-z0-9._+-]*$') { Stop-Pass "invalid firmware identity/version" }
$transcriptLines=@([System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $Transcript).Path))
Assert-FirmwareTranscript $transcriptLines $FirmwareMode $FirmwareStages $BootCorrelationMarker $Nonce

$admissionKeys = @("detected_host","requested_host","host_identity_status","host_identity_reason","qemu_binary","qemu_binary_resolved","qemu_sha256","qemu_version","requested_accelerator","accelerator_advertised_status","accelerator_advertised_reason","accelerator_probe_status","accelerator_probe_reason","native_timing_applicable","simple_qemu_storage_root")
$requiredAdmission = @($admissionKeys | Where-Object { $_ -ne "simple_qemu_storage_root" })
$admit = Read-ClosedEnv $Admission $admissionKeys $requiredAdmission
$qemuResolved = (Resolve-Path -LiteralPath $QemuBinary).Path
if ($admit.detected_host -ne $HostName -or $admit.requested_host -ne $HostName -or $admit.host_identity_status -ne "pass") { Stop-Pass "host admission mismatch" }
if ($admit.accelerator_advertised_status -ne "pass" -or $admit.accelerator_probe_status -ne "pass" -or $admit.requested_accelerator -ne $Accelerator) { Stop-Pass "accelerator was not admitted" }
if ([System.IO.Path]::GetFullPath($admit.qemu_binary_resolved) -ne [System.IO.Path]::GetFullPath($qemuResolved)) { Stop-Pass "QEMU resolved path changed" }
if ($admit.qemu_sha256 -ne (Hash $qemuResolved)) { Stop-Pass "QEMU binary changed after admission" }
$qemuVersion = One-Line $QemuVersionFile "QEMU version"
if ($admit.qemu_version -ne $qemuVersion) { Stop-Pass "QEMU version changed after admission" }
$qemuArgv = One-Line $QemuArgvFile "QEMU argv"

$sourceResolved = (Resolve-Path -LiteralPath $Source).Path
$status = @(& git -C $sourceResolved status --porcelain=v1 --untracked-files=all)
if ($LASTEXITCODE -ne 0 -or $status.Count -ne 0) { Stop-Pass "source worktree is not clean" }
$commit = (& git -C $sourceResolved rev-parse HEAD).Trim()
$tree = (& git -C $sourceResolved rev-parse 'HEAD^{tree}').Trim()
if ($LASTEXITCODE -ne 0 -or $commit -notmatch '^[0-9a-f]{40,64}$' -or $tree -notmatch '^[0-9a-f]{40,64}$') { Stop-Pass "invalid Git lineage" }

$transcriptText = [System.IO.File]::ReadAllText((Resolve-Path -LiteralPath $Transcript).Path)
$markerLines = @([System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $RequiredMarkersFile).Path))
if ($markerLines.Count -eq 0) { Stop-Pass "empty required marker contract" }
$position = -1
foreach ($marker in $markerLines) {
    if ([string]::IsNullOrEmpty($marker)) { Stop-Pass "empty required marker" }
    $next = $transcriptText.IndexOf($marker,$position + 1,[StringComparison]::Ordinal)
    if ($next -lt 0) { Stop-Pass "missing or out-of-order required marker: $marker" }; $position = $next
}

$runDir = Join-Path (Join-Path (Join-Path ([System.IO.Path]::GetFullPath($Output)) $HostName) $Guest) "run-$Nonce"
if (Test-Path -LiteralPath $runDir) { Stop-Pass "destination exists: $runDir" }
$stage = Join-Path ([System.IO.Path]::GetTempPath()) ("sosix-native-pass." + [Guid]::NewGuid().ToString("N"))
[System.IO.Directory]::CreateDirectory($stage) | Out-Null
try {
    $artifacts = [ordered]@{
        "host-admission.env"=$Admission; "qemu.argv"=$QemuArgvFile; "qemu.version"=$QemuVersionFile
        "transcript.log"=$Transcript; "kernel.elf"=$Kernel; "guest.img"=$Image
        "program.elf"=$Program; "firmware.bin"=$Firmware; "required-markers.txt"=$RequiredMarkersFile
    }
    if ($CompilerInFilesystem -eq "true") {
        $compilerVersionHash = Hash $CompilerVersionEvidence
        $compilerHelloHash = Hash $CompilerHelloEvidence
        $compilerAliasHash = Hash $CompilerAliasEvidence
        $compilerManifestHash = Hash $CompilerManifestEvidence
        if ($env:SOSIX_QEMU_TEST_MODE -eq "1" -and $env:SOSIX_QEMU_TEST_MUTATE_COMPILER_BEFORE_COPY -eq "true") {
            Add-Content -LiteralPath $CompilerVersionEvidence -Value "deterministic-mid-copy-mutation"
        }
        $artifacts["compiler-version.txt"]=$CompilerVersionEvidence
        $artifacts["compiler-hello.txt"]=$CompilerHelloEvidence
        $artifacts["compiler-aliases.txt"]=$CompilerAliasEvidence
        $artifacts["compiler-manifest.env"]=$CompilerManifestEvidence
    }
    foreach ($entry in $artifacts.GetEnumerator()) { Copy-Item -LiteralPath $entry.Value -Destination (Join-Path $stage $entry.Key) }
    if ($CompilerInFilesystem -eq "true" -and
        ((Hash $CompilerVersionEvidence) -ne $compilerVersionHash -or
         (Hash $CompilerHelloEvidence) -ne $compilerHelloHash -or
         (Hash $CompilerAliasEvidence) -ne $compilerAliasHash -or
         (Hash $CompilerManifestEvidence) -ne $compilerManifestHash -or
         (Hash (Join-Path $stage "compiler-version.txt")) -ne $compilerVersionHash -or
         (Hash (Join-Path $stage "compiler-hello.txt")) -ne $compilerHelloHash -or
         (Hash (Join-Path $stage "compiler-aliases.txt")) -ne $compilerAliasHash -or
         (Hash (Join-Path $stage "compiler-manifest.env")) -ne $compilerManifestHash)) {
        Stop-Pass "compiler evidence changed during snapshot"
    }
    $kernelHash=Hash (Join-Path $stage "kernel.elf"); $imageHash=Hash (Join-Path $stage "guest.img")
    $programHash=Hash (Join-Path $stage "program.elf"); $transcriptHash=Hash (Join-Path $stage "transcript.log")
    $firmwareHash=Hash (Join-Path $stage "firmware.bin"); $qemuHash=Hash $qemuResolved
    $sourceIdentity="git:${commit}:tree:${tree}:clean"
    $compilerPayloadIdentity=''; $compilerImageIdentity=''; $compilerAliasIdentity=''; $compilerManifestIdentity=''
    if ($CompilerInFilesystem -eq "true") {
        $compilerLineage=Assert-CompilerPlacement (Join-Path $stage 'compiler-aliases.txt') (Join-Path $stage 'compiler-manifest.env') $transcriptLines $HostName $Guest $Nonce "sha256:$imageHash" $sourceIdentity
        $compilerPayloadIdentity=$compilerLineage.Payload; $compilerImageIdentity="sha256:$imageHash"
        $compilerAliasIdentity=$compilerLineage.Placement; $compilerManifestIdentity=$compilerLineage.Manifest
        $expectedCompilerIdentity="target-native-simple:payload=${compilerPayloadIdentity}:image=${compilerImageIdentity}:alias=${compilerAliasIdentity}:manifest=${compilerManifestIdentity}"
        if ($CompilerIdentity -cne $expectedCompilerIdentity) { Stop-Pass "compiler identity is not bound to target readback lineage" }
    }
    $lines = [System.Collections.Generic.List[string]]::new()
    $versionPath = if ($CompilerInFilesystem -eq "true") { "compiler-version.txt" } else { "" }
    $helloPath = if ($CompilerInFilesystem -eq "true") { "compiler-hello.txt" } else { "" }
    $aliasPath = if ($CompilerInFilesystem -eq "true") { "compiler-aliases.txt" } else { "" }
    $manifestPath = if ($CompilerInFilesystem -eq "true") { "compiler-manifest.env" } else { "" }
    $designationScope = if ($fixtureCompilerDesignation) { "contract-fixture" } else { "live-policy" }
    $compilerIdentityScope = if ($CompilerInFilesystem -eq "true") { "target-filesystem" } else { "source-toolchain" }
    $compilerPolicyPath = Join-Path $PSScriptRoot "lib\sosix-qemu-compiler-designation-v1.tsv"
    foreach ($line in @("schema_version=1","host=$HostName","guest=$Guest","status=pass","reason=","owner=$Owner","reviewer=$Reviewer","resume_command=","source_identity=$sourceIdentity","compiler_identity=$CompilerIdentity","compiler_identity_scope=$compilerIdentityScope","compiler_policy_sha256=$(Hash $compilerPolicyPath)","compiler_policy_value=$liveCompilerDesignation","compiler_payload_identity=$compilerPayloadIdentity","compiler_image_identity=$compilerImageIdentity","compiler_alias_identity=$compilerAliasIdentity","compiler_manifest_identity=$compilerManifestIdentity","kernel_identity=sha256:$kernelHash","image_identity=sha256:$imageHash","qemu_identity=sha256:$qemuHash`:version:$qemuVersion","qemu_argv=$qemuArgv","accelerator_identity=$Accelerator","firmware_identity=firmware:$FirmwareId","firmware_mode=$FirmwareMode","firmware_path=$((Resolve-Path -LiteralPath $Firmware).Path)","firmware_version=version:$FirmwareVersion","firmware_sha256=sha256:$firmwareHash","firmware_stage_markers=$FirmwareStages","boot_correlation_marker=$BootCorrelationMarker","run_nonce=$Nonce","transcript_identity=sha256:$transcriptHash","program_identity=sha256:$programHash","compiler_in_filesystem=$CompilerInFilesystem","compiler_designation_scope=$designationScope","compiler_version_evidence_path=$versionPath","compiler_hello_evidence_path=$helloPath","compiler_alias_evidence_path=$aliasPath","compiler_manifest_evidence_path=$manifestPath","artifact_count=$($artifacts.Count)")) { $lines.Add($line) }
    $i=1; foreach ($name in $artifacts.Keys) { $lines.Add("artifact_${i}_path=$name"); $lines.Add("artifact_${i}_sha256=$(Hash (Join-Path $stage $name))"); $i++ }
    [System.IO.File]::WriteAllLines((Join-Path $stage "evidence.env"),$lines,[System.Text.UTF8Encoding]::new($false))
    [System.IO.Directory]::CreateDirectory((Split-Path -Parent $runDir)) | Out-Null
    [System.IO.Directory]::Move($stage,$runDir); $stage=$null
    Write-Output "sosix_qemu_native_pass_bundle_status=pass"
    Write-Output "sosix_qemu_native_pass_bundle=$(Join-Path $runDir 'evidence.env')"
} finally { if ($null -ne $stage -and (Test-Path -LiteralPath $stage)) { Remove-Item -LiteralPath $stage -Recurse -Force } }
