# setup-cef-dynlib.ps1 — Windows twin of scripts/setup/setup-cef-dynlib.shs.
#
# Same flags, same receipt keys, same fail-closed rules. The pinned VERSION LINE comes from
# the SAME data file, config/cef/cef_pin.sdn; archive names and digests are resolved at
# install time from the publisher index, exactly as the POSIX twin does. This script
# carries no second copy of either.
#
#   -Check        (default) report what is staged; never touches the network
#   -Install      resolve the archive from the index, admit it against the index's SHA1,
#                 extract under build\cef\, then record the measured SHA256 at
#                 build\cef\<version>\<platform>\admitted.sha256
#   -Env          print the SIMPLE_CEF_ROOT / SIMPLE_CEF_LIB assignments
#   -AllowUnpinned  install a version that is NOT in the index, e.g. a locally built drop
#                 (announced loudly; never admitted evidence)
#   -IndexFile    use a local copy of index.json instead of fetching it
#
# CEF publishes .tar.bz2 for every platform, Windows included, so extraction uses `tar`,
# which ships with Windows 10+. Expand-Archive cannot read .tar.bz2 and is deliberately not
# used. Destructive operations are confined to build\cef.
[CmdletBinding()]
param(
    [switch]$Check,
    [switch]$Install,
    [switch]$Env,
    [switch]$AllowUnpinned,
    [string]$Platform = "",
    [string]$PinFile = "",
    [string]$IndexFile = ""
)

$ErrorActionPreference = "Stop"
$RootDir = (Resolve-Path (Join-Path $PSScriptRoot "..\..")).Path
if ([string]::IsNullOrEmpty($PinFile)) {
    $PinFile = Join-Path $RootDir "config\cef\cef_pin.sdn"
}

$script:MacosHelperStatus = ""

function Write-Receipt {
    param($Plat, $Version, $Lib, $ShaStatus, $Reason, $Status)
    Write-Output "cef_platform=$Plat"
    Write-Output "cef_version=$Version"
    Write-Output "cef_lib=$Lib"
    Write-Output "cef_sha256_status=$ShaStatus"
    if ($script:MacosHelperStatus -ne "") {
        Write-Output "macos_helper_status=$($script:MacosHelperStatus)"
    }
    Write-Output "cef_reason=$Reason"
    Write-Output "cef_status=$Status"
}

function Get-PinScalar {
    param($Key)
    foreach ($line in Get-Content -LiteralPath $PinFile) {
        $t = $line.Trim()
        if ($t.StartsWith("$Key" + ":")) {
            return $t.Substring($Key.Length + 1).Trim().Trim('"')
        }
    }
    return ""
}

function Get-PinRowField {
    param($Want, $Field)
    $current = ""
    foreach ($line in Get-Content -LiteralPath $PinFile) {
        $t = $line.Trim()
        if ($t.StartsWith("- platform:")) {
            $current = $t.Substring("- platform:".Length).Trim().Trim('"')
            continue
        }
        if ($current -eq $Want -and $t.StartsWith("$Field" + ":")) {
            return $t.Substring($Field.Length + 1).Trim().Trim('"')
        }
    }
    return ""
}

function Get-DetectedPlatform {
    # PROCESSOR_ARCHITECTURE is the process view; ...W6432 is the machine view under WOW64.
    $arch = $env:PROCESSOR_ARCHITEW6432
    if ([string]::IsNullOrEmpty($arch)) { $arch = $env:PROCESSOR_ARCHITECTURE }
    switch ($arch) {
        "AMD64" { return "windows64" }
        "ARM64" { return "windowsarm64" }
        default { return "unsupported" }
    }
}

function Test-DropRoot {
    param($DropRoot, $RelLib)
    if (-not (Test-Path -LiteralPath $DropRoot)) { return @("missing", "no-cef-drop", "") }
    $header = Join-Path $DropRoot "include\capi\cef_app_capi.h"
    if (-not (Test-Path -LiteralPath $header)) { return @("missing", "headers-absent", "") }
    if ([string]::IsNullOrEmpty($RelLib)) { return @("missing", "libcef-absent", "") }
    $lib = Join-Path $DropRoot ($RelLib -replace "/", "\")
    if (-not (Test-Path -LiteralPath $lib)) { return @("missing", "libcef-absent", "") }
    return @("present", "", $lib)
}

if (-not (Test-Path -LiteralPath $PinFile)) {
    Write-Receipt "unknown" "unknown" "" "unknown" "pin-file-absent:$PinFile" "missing"
    exit 2
}

$Plat = if ($Platform -ne "") { $Platform } else { Get-DetectedPlatform }
$Version = Get-PinScalar "version"
$InstallRoot = Join-Path $RootDir ((Get-PinScalar "install_root") -replace "/", "\")

if ($Plat -eq "unsupported") {
    Write-Receipt "unsupported" $Version "" "unknown" "no-cef-distribution-for-this-arch" "missing"
    exit 2
}

$RelLib = Get-PinRowField $Plat "lib"
# Archive name and digest are NOT in the pin file — they are resolved from the publisher
# index at install time, exactly as the POSIX twin does. See config/cef/cef_pin.sdn.
$Archive = ""
$IndexSha1 = ""
if ([string]::IsNullOrEmpty($RelLib)) {
    Write-Receipt $Plat $Version "" "unknown" "no-pin-row-for-platform" "missing"
    exit 2
}

$DropRoot = $env:SIMPLE_CEF_ROOT
if ([string]::IsNullOrEmpty($DropRoot)) {
    $DropRoot = Join-Path (Join-Path $InstallRoot $Version) $Plat
}

$ShaStatus = "unadmitted"

if ($Install) {
    $Distribution = Get-PinScalar "distribution"
    $StageDir = Join-Path $InstallRoot ".download"
    New-Item -ItemType Directory -Force -Path $StageDir | Out-Null

    # 1. Publisher index (or a local copy via -IndexFile).
    $IndexPath = $IndexFile
    if ([string]::IsNullOrEmpty($IndexPath)) {
        $IndexPath = Join-Path $StageDir "index.json"
        try {
            Invoke-WebRequest -Uri (Get-PinScalar "index_url") -OutFile $IndexPath -UseBasicParsing
        } catch { }
    }
    if (-not (Test-Path -LiteralPath $IndexPath)) {
        Write-Receipt $Plat $Version "" "unknown" "publisher-index-unavailable" "missing"
        exit 2
    }

    # 2. Resolve THIS platform's archive for the pinned version line, plus its sha1.
    $Index = Get-Content -LiteralPath $IndexPath -Raw | ConvertFrom-Json
    $PlatNode = $Index.$Plat
    if ($null -ne $PlatNode) {
        foreach ($v in $PlatNode.versions) {
            if ($v.cef_version -like "$Version*") {
                foreach ($f in $v.files) {
                    if ($f.type -eq $Distribution) { $Archive = $f.name; $IndexSha1 = $f.sha1; break }
                }
            }
            if ($Archive -ne "") { break }
        }
    }
    if ([string]::IsNullOrEmpty($Archive) -and -not $AllowUnpinned) {
        Write-Warning "REFUSED: no $Distribution archive for $Plat starts with version $Version in the index."
        Write-Warning "Correct config/cef/cef_pin.sdn, or re-run with -AllowUnpinned for a locally built drop."
        Write-Receipt $Plat $Version "" "unset" "version-not-in-index" "missing"
        exit 2
    }
    $ShaStatus = if ([string]::IsNullOrEmpty($IndexSha1)) { "unpinned" } else { "pinned" }
    if ($ShaStatus -eq "unpinned") {
        Write-Warning "*** -AllowUnpinned: installing a CEF archive with NO publisher digest. ***"
        Write-Warning "*** The resulting drop is NOT admitted evidence for any gate.          ***"
    }
    Write-Output "cef_index_sha1=$(if ($IndexSha1) { $IndexSha1 } else { 'none' })"
    Write-Output "cef_archive=$(if ($Archive) { $Archive } else { 'none' })"
    if ([string]::IsNullOrEmpty($Archive)) {
        Write-Receipt $Plat $Version "" $ShaStatus "archive-name-unresolved" "missing"
        exit 2
    }

    $Url = (Get-PinScalar "url_template") -replace "\{archive\}", $Archive
    $ArchivePath = Join-Path $StageDir $Archive

    if (-not (Test-Path -LiteralPath $ArchivePath)) {
        try {
            Invoke-WebRequest -Uri $Url -OutFile "$ArchivePath.part" -UseBasicParsing
        } catch {
            Remove-Item -LiteralPath "$ArchivePath.part" -ErrorAction SilentlyContinue
            Write-Receipt $Plat $Version "" $ShaStatus "download-failed" "missing"
            exit 2
        }
        Move-Item -LiteralPath "$ArchivePath.part" -Destination $ArchivePath
    }

    # 3. Admit the downloaded archive against the INDEX's own sha1 for that exact file.
    if ($ShaStatus -eq "pinned") {
        $Actual = (Get-FileHash -LiteralPath $ArchivePath -Algorithm SHA1).Hash.ToLower()
        if ($Actual -ne $IndexSha1.ToLower()) {
            # Keep the offending file for inspection; never silently re-download over it.
            Write-Receipt $Plat $Version "" "mismatch" "archive-sha1-does-not-match-index" "hash-mismatch"
            exit 3
        }
    }

    $Target = Join-Path (Join-Path $InstallRoot $Version) $Plat
    if (-not $Target.StartsWith($InstallRoot)) {
        Write-Receipt $Plat $Version "" $ShaStatus "refusing-to-write-outside-install-root" "missing"
        exit 2
    }
    if (Test-Path -LiteralPath $Target) { Remove-Item -LiteralPath $Target -Recurse -Force }
    New-Item -ItemType Directory -Force -Path $Target | Out-Null

    # `tar` (bsdtar) ships with Windows 10+ and reads .tar.bz2; Expand-Archive cannot.
    & tar -xjf $ArchivePath -C $Target --strip-components=1
    if ($LASTEXITCODE -ne 0) {
        Write-Receipt $Plat $Version "" $ShaStatus "extract-failed-rc-$LASTEXITCODE" "missing"
        exit 2
    }
    # 4. Record the MEASURED sha256 of the admitted archive; every later -Check reads it.
    $AdmittedSha256 = (Get-FileHash -LiteralPath $ArchivePath -Algorithm SHA256).Hash.ToLower()
    @(
        "archive=$Archive"
        "index_sha1=$(if ($IndexSha1) { $IndexSha1 } else { 'none' })"
        "gate=$ShaStatus"
        "sha256=$AdmittedSha256"
    ) | Set-Content -LiteralPath (Join-Path $Target "admitted.sha256")
    $DropRoot = $Target
}

$Result = Test-DropRoot $DropRoot $RelLib
$Status = $Result[0]
$Reason = $Result[1]
$LibPath = $Result[2]

# -Check never touches the network: it reads the record the install wrote. A drop with no
# admitted.sha256 is `unadmitted` and is NOT present, because nothing ever verified it.
$AdmitFile = Join-Path $DropRoot "admitted.sha256"
if (Test-Path -LiteralPath $AdmitFile) {
    $AdmitLines = Get-Content -LiteralPath $AdmitFile
    $ShaStatus = ($AdmitLines | Where-Object { $_ -like "gate=*" }) -replace "^gate=", ""
    if ([string]::IsNullOrEmpty($ShaStatus)) { $ShaStatus = "unknown" }
    Write-Output "cef_admitted_sha256=$(($AdmitLines | Where-Object { $_ -like 'sha256=*' }) -replace '^sha256=', '')"
    Write-Output "cef_index_sha1=$(($AdmitLines | Where-Object { $_ -like 'index_sha1=*' }) -replace '^index_sha1=', '')"
} else {
    $ShaStatus = "unadmitted"
    if ($Status -eq "present") {
        $Status = "missing"
        $Reason = "no-admitted-sha256-record-run--Install"
    }
}

if ($Env) {
    if ($Status -ne "present") {
        Write-Receipt $Plat $Version "" $ShaStatus $Reason "missing"
        exit 1
    }
    Write-Output "`$env:SIMPLE_CEF_ROOT = `"$DropRoot`""
    Write-Output "`$env:SIMPLE_CEF_LIB = `"$LibPath`""
    Write-Output "`$env:SIMPLE_CEF_PLATFORM = `"$Plat`""
}

if ($Status -eq "present") {
    Write-Receipt $Plat $Version $LibPath $ShaStatus "ok" "present"
    exit 0
}

Write-Receipt $Plat $Version "" $ShaStatus $Reason "missing"
exit 1
