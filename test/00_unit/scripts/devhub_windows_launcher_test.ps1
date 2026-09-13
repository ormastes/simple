$ErrorActionPreference = 'Stop'

$Root = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$Launcher = Join-Path $Root 'bin\devhub.cmd'
if (-not (Test-Path -LiteralPath $Launcher -PathType Leaf)) {
    throw "missing Windows DevHub launcher: $Launcher"
}

$Temp = Join-Path ([IO.Path]::GetTempPath()) ('devhub-launcher-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Temp | Out-Null
$OldDevHubSh = $env:DEVHUB_SH
$OldPath = $env:Path
$OldMarker = $env:DEVHUB_TEST_MARKER
$OldSimpleBinary = $env:SIMPLE_BINARY
$OldFixtureMode = $env:SIMPLE_HOST_RESOLVER_FIXTURE_MODE
$Utf8NoBom = New-Object System.Text.UTF8Encoding($false)
function Write-LfFile([string] $Path, [string] $Content) {
    $normalized = $Content -replace "`r`n", "`n"
    [IO.File]::WriteAllText($Path, $normalized, $Utf8NoBom)
}
try {
    $FakeSh = Join-Path $Temp 'fake-sh.cmd'
    $Marker = Join-Path $Temp 'dispatch.args'
    Write-LfFile $FakeSh @'
@echo off
setlocal
> "%DEVHUB_TEST_MARKER%" echo script=%~1
>>"%DEVHUB_TEST_MARKER%" echo arg1=%~2
>>"%DEVHUB_TEST_MARKER%" echo arg2=%~3
exit /b 0
'@

    function Invoke-DevHub([string[]] $Arguments) {
        $argText = ($Arguments | ForEach-Object {
            if ($_ -match '[\s"]') { '"' + ($_ -replace '"', '\"') + '"' } else { $_ }
        }) -join ' '
        $psi = [Diagnostics.ProcessStartInfo]::new()
        $psi.FileName = $env:ComSpec
        $prefix = if ($env:DEVHUB_SH) { 'set "DEVHUB_SH=' + $env:DEVHUB_SH + '"&& ' } else { '' }
        $psi.Arguments = '/d /c ' + $prefix + 'call "' + $Launcher + '" ' + $argText
        $psi.WorkingDirectory = $Root
        $psi.UseShellExecute = $false
        $psi.RedirectStandardOutput = $true
        $psi.RedirectStandardError = $true
        $p = [Diagnostics.Process]::Start($psi)
        $stdout = $p.StandardOutput.ReadToEnd()
        $stderr = $p.StandardError.ReadToEnd()
        $p.WaitForExit()
        [pscustomobject]@{ ExitCode = $p.ExitCode; Stdout = $stdout; Stderr = $stderr }
    }

    # Explicit DEVHUB_SH override and argument forwarding, including spaces.
    $env:DEVHUB_SH = $FakeSh
    $env:DEVHUB_TEST_MARKER = $Marker
    & $FakeSh 'fixture-script' '--name' 'value with spaces'
    if (-not (Test-Path -LiteralPath $Marker)) { throw 'fake shell fixture did not execute directly' }
    Remove-Item -LiteralPath $Marker -Force
    $r = Invoke-DevHub @('--name', 'value with spaces')
    if ($r.ExitCode -ne 0) { throw "override dispatch failed: exit=$($r.ExitCode) out=$($r.Stdout) err=$($r.Stderr) marker=$([bool](Test-Path $Marker)) devhub_sh=$env:DEVHUB_SH" }
    $lines = Get-Content -LiteralPath $Marker
    if ($lines[1] -ne 'arg1=--name' -or $lines[2] -ne 'arg2=value with spaces') {
        throw "argument forwarding failed: $($lines -join '; ')"
    }

    # With no shell on PATH, the launcher must fail closed with status 127.
    Remove-Item Env:DEVHUB_SH -ErrorAction SilentlyContinue
    $env:Path = $Temp
    $r = Invoke-DevHub @('--help')
    if ($r.ExitCode -ne 127 -or $r.Stderr -notmatch 'requires sh\.exe') {
        throw "missing-shell contract failed: exit=$($r.ExitCode) stderr=$($r.Stderr)"
    }

    # Exercise real sh.exe discovery and the existing provenance-enforced
    # wrapper when a POSIX shell is installed (Git for Windows/ MSYS).
    $env:Path = $OldPath
    $savedErrorAction = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $sh = (& $env:ComSpec /d /c where sh.exe 2>$null | Select-Object -First 1)
    $ErrorActionPreference = $savedErrorAction
    if ([string]::IsNullOrWhiteSpace($sh)) {
        Write-Output 'SKIP devhub-windows-launcher actual-sh=unavailable'
    } else {
        $Runtime = Join-Path $Temp 'admitted\x86_64-pc-windows-msvc\simple.exe'
        New-Item -ItemType Directory -Force -Path (Split-Path $Runtime) | Out-Null
        Write-LfFile $Runtime @'
#!/bin/sh
case "${1:-}" in
  --version) printf '%s\n' 'Simple v9.9.9-test' ;;
  --help) printf '%s\n' 'simple test' ;;
  run) printf '%s\n' 'provenance-safe-dispatch' ;;
  *) exit 2 ;;
esac
'@
        & bash.exe -lc ('chmod +x "' + ($Runtime -replace '\\','/') + '"') 2>$null
        $hash = (Get-FileHash -LiteralPath $Runtime -Algorithm SHA256).Hash.ToLowerInvariant()
        Write-LfFile ($Runtime + '.provenance.env') @"
schema=simple-runtime-provenance-v1
status=admitted
implementation=pure-simple
artifact_sha256=$hash
target_triple=x86_64-pc-windows-msvc
version_output=Simple v9.9.9-test
producer=windows-launcher-test
evidence=windows-launcher-test
"@
        $env:SIMPLE_BINARY = $Runtime
        $env:SIMPLE_HOST_RESOLVER_FIXTURE_MODE = '1'
        Remove-Item Env:DEVHUB_SH -ErrorAction SilentlyContinue
        $r = Invoke-DevHub @('--help')
        if ($r.ExitCode -ne 0 -or $r.Stdout -notmatch 'provenance-safe-dispatch') {
            throw "actual sh dispatch failed: exit=$($r.ExitCode) out=$($r.Stdout) err=$($r.Stderr)"
        }
        Write-Output 'PASS devhub-windows-launcher actual-sh=discovered provenance=exercised'
    }
} finally {
    if ($null -eq $OldDevHubSh) { Remove-Item Env:DEVHUB_SH -ErrorAction SilentlyContinue } else { $env:DEVHUB_SH = $OldDevHubSh }
    if ($null -eq $OldPath) { Remove-Item Env:Path -ErrorAction SilentlyContinue } else { $env:Path = $OldPath }
    if ($null -eq $OldMarker) { Remove-Item Env:DEVHUB_TEST_MARKER -ErrorAction SilentlyContinue } else { $env:DEVHUB_TEST_MARKER = $OldMarker }
    if ($null -eq $OldSimpleBinary) { Remove-Item Env:SIMPLE_BINARY -ErrorAction SilentlyContinue } else { $env:SIMPLE_BINARY = $OldSimpleBinary }
    if ($null -eq $OldFixtureMode) { Remove-Item Env:SIMPLE_HOST_RESOLVER_FIXTURE_MODE -ErrorAction SilentlyContinue } else { $env:SIMPLE_HOST_RESOLVER_FIXTURE_MODE = $OldFixtureMode }
    Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue
}

Write-Output 'PASS devhub-windows-launcher override=args missing-shell=127'
