# setup-cef-dynlib.ps1 — Windows twin of scripts/setup/setup-cef-dynlib.shs.
#
# Same flags, same receipt keys, same fail-closed rules. The version and per-platform
# archive digests come from the SAME data file, config/cef/cef_pin.sdn; this script carries
# no second copy of them.
#
#   -Check        (default) report what is staged; never touches the network
#   -Install      download the pinned archive, verify SHA256, extract under build\cef\
#   -Env          print the SIMPLE_CEF_ROOT / SIMPLE_CEF_LIB assignments
#   -AllowUnpinned  install despite an UNSET pin (announced loudly; never admitted evidence)
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
    [string]$PinFile = ""
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
$Archive = Get-PinRowField $Plat "archive"
$PinnedSha = Get-PinRowField $Plat "sha256"
if ([string]::IsNullOrEmpty($RelLib)) {
    Write-Receipt $Plat $Version "" "unknown" "no-pin-row-for-platform" "missing"
    exit 2
}

$DropRoot = $env:SIMPLE_CEF_ROOT
if ([string]::IsNullOrEmpty($DropRoot)) {
    $DropRoot = Join-Path (Join-Path $InstallRoot $Version) $Plat
}

$ShaStatus = if ([string]::IsNullOrEmpty($PinnedSha) -or $PinnedSha -eq "UNSET") { "unpinned" } else { "pinned" }

if ($Install) {
    if ($ShaStatus -eq "unpinned" -and -not $AllowUnpinned) {
        Write-Warning "REFUSED: the sha256 for platform $Plat is UNSET in $PinFile."
        Write-Warning "Fill the pin from the publisher index, or re-run with -AllowUnpinned."
        Write-Receipt $Plat $Version "" "unset" "pin-unset-refused" "missing"
        exit 2
    }
    if ($ShaStatus -eq "unpinned") {
        Write-Warning "*** -AllowUnpinned: installing an UNVERIFIED CEF archive.        ***"
        Write-Warning "*** The resulting drop is NOT admitted evidence for any gate.    ***"
    }
    if ([string]::IsNullOrEmpty($Archive) -or $Archive -eq "UNSET-verify-before-use") {
        Write-Receipt $Plat $Version "" $ShaStatus "archive-name-unset" "missing"
        exit 2
    }

    $Url = (Get-PinScalar "url_template") -replace "\{archive\}", $Archive
    $StageDir = Join-Path $InstallRoot ".download"
    New-Item -ItemType Directory -Force -Path $StageDir | Out-Null
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

    if ($ShaStatus -eq "pinned") {
        $Actual = (Get-FileHash -LiteralPath $ArchivePath -Algorithm SHA256).Hash.ToLower()
        if ($Actual -ne $PinnedSha.ToLower()) {
            # Keep the offending file for inspection; never silently re-download over it.
            Write-Receipt $Plat $Version "" "mismatch" "archive-sha256-does-not-match-pin" "hash-mismatch"
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
    $DropRoot = $Target
}

$Result = Test-DropRoot $DropRoot $RelLib
$Status = $Result[0]
$Reason = $Result[1]
$LibPath = $Result[2]

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
