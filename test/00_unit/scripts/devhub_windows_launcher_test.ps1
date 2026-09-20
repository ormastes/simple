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
$OldWindowsAbi = $env:SIMPLE_WINDOWS_ABI
$OldTestExit = $env:DEVHUB_TEST_EXIT
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
            '"' + ($_ -replace '"', '\"') + '"'
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
    Remove-Item -LiteralPath $Marker -Force
    $r = Invoke-DevHub @('--mode', 'loading')
    if ($r.ExitCode -ne 78 -or (Test-Path -LiteralPath $Marker)) {
        throw "loading mode executed the shell override: exit=$($r.ExitCode) err=$($r.Stderr)"
    }

    # Native Windows dispatch does not need sh.exe.  Use a fixture runtime so
    # this also verifies argument boundaries and child exit propagation.
    $FakeRuntime = Join-Path $Temp 'fake-simple.cmd'
    Write-LfFile $FakeRuntime @'
@echo off
if "%~1"=="--version" (
    echo Simple v9.9.9-test
    exit /b 0
)
if "%~1"=="--help" (
    echo simple test
    exit /b 0
)
if "%~1"=="run" goto capture_run
exit /b 2

:capture_run
    set "marker=%DEVHUB_TEST_MARKER%"
    set "arg3=%~3"
    set "arg4=%~4"
    set "arg5=%~5"
    set "arg6=%~6"
    set "arg7=%~7"
    set "arg8=%~8"
    set "arg9=%~9"
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    shift
    set "arg10=%~1"
    set "arg11=%~2"
    set "arg12=%~3"
    set "arg13=%~4"
    setlocal EnableDelayedExpansion
    >"!marker!" echo invocation=1
    >>"!marker!" echo arg3=!arg3!
    >>"!marker!" echo arg4=!arg4!
    >>"!marker!" echo arg5=!arg5!
    >>"!marker!" echo arg6=!arg6!
    >>"!marker!" echo arg7=!arg7!
    >>"!marker!" echo arg8=!arg8!
    >>"!marker!" echo arg9=!arg9!
    >>"!marker!" echo arg10=!arg10!
    >>"!marker!" echo arg11=!arg11!
    >>"!marker!" echo arg12=!arg12!
    >>"!marker!" echo arg13=!arg13!
    exit /b %DEVHUB_TEST_EXIT%
'@
    $hash = (Get-FileHash -LiteralPath $FakeRuntime -Algorithm SHA256).Hash.ToLowerInvariant()
    $env:SIMPLE_WINDOWS_ABI = 'msvc'
    $hostArch = if ($env:PROCESSOR_ARCHITEW6432) { $env:PROCESSOR_ARCHITEW6432 } else { $env:PROCESSOR_ARCHITECTURE }
    if ($hostArch -eq 'AMD64') { $hostArch = 'x86_64' }
    if ($hostArch -eq 'ARM64') { $hostArch = 'aarch64' }
    $env:DEVHUB_TEST_EXIT = '0'
    Write-LfFile ($FakeRuntime + '.provenance.env') @"
schema=simple-runtime-provenance-v1
status=admitted
implementation=pure-simple
artifact_sha256=$hash
target_triple=$hostArch-pc-windows-msvc
version_output=Simple v9.9.9-test
"@
    $env:SIMPLE_BINARY = $FakeRuntime
    $env:SIMPLE_HOST_RESOLVER_FIXTURE_MODE = '1'
    Remove-Item Env:DEVHUB_SH -ErrorAction SilentlyContinue
    # Keep certutil available while intentionally excluding Git's sh.exe.
    $env:Path = $Temp + ';' + (Join-Path $env:SystemRoot 'System32')
    $r = Invoke-DevHub @('--mode', 'ordinary', '--alpha', 'two words', 'a&b', 'bang!value', 'arg7', 'arg8', 'arg9', 'arg10', 'arg11', 'arg12', 'arg13')
    if ($r.ExitCode -ne 0) {
        throw "native dispatch failed: exit=$($r.ExitCode) out=$($r.Stdout) err=$($r.Stderr)"
    }
    $lines = Get-Content -LiteralPath $Marker
    if (($lines | Where-Object { $_ -eq 'invocation=1' }).Count -ne 1) { throw "native invocation count failed: $($lines -join '; ')" }
    if ($lines[1] -ne 'arg3=--mode' -or $lines[2] -ne 'arg4=ordinary' -or $lines[3] -ne 'arg5=--alpha' -or $lines[4] -ne 'arg6=two words' -or $lines[5] -ne 'arg7=a&b' -or $lines[6] -ne 'arg8=bang!value' -or $lines[8] -ne 'arg10=arg13') {
        throw "native argument forwarding failed: $($lines -join '; ')"
    }
    $env:DEVHUB_TEST_EXIT = '41'
    $r = Invoke-DevHub @('check', 'value with spaces')
    if ($r.ExitCode -ne 41) { throw "native exit propagation failed: exit=$($r.ExitCode) err=$($r.Stderr)" }
    Remove-Item Env:DEVHUB_TEST_EXIT -ErrorAction SilentlyContinue

    # An absent or unadmitted artifact must fail closed without attempting to
    # open it through a file association or another fallback.
    $env:SIMPLE_BINARY = Join-Path $Temp 'missing-simple.exe'
    Remove-Item -LiteralPath $Marker -Force -ErrorAction SilentlyContinue
    $r = Invoke-DevHub @('--help')
    if ($r.ExitCode -ne 127 -or $r.Stderr -notmatch 'no Simple runtime found') {
        throw "missing-artifact contract failed: exit=$($r.ExitCode) stderr=$($r.Stderr)"
    }
    if (Test-Path -LiteralPath $Marker) {
        throw 'missing artifact was accidentally executed'
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
        # Discovery is intentionally not implicit; exercise the POSIX wrapper
        # through its explicit compatibility override.
        $env:DEVHUB_SH = $sh
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
    if ($null -eq $OldWindowsAbi) { Remove-Item Env:SIMPLE_WINDOWS_ABI -ErrorAction SilentlyContinue } else { $env:SIMPLE_WINDOWS_ABI = $OldWindowsAbi }
    if ($null -eq $OldTestExit) { Remove-Item Env:DEVHUB_TEST_EXIT -ErrorAction SilentlyContinue } else { $env:DEVHUB_TEST_EXIT = $OldTestExit }
    Remove-Item -LiteralPath $Temp -Recurse -Force -ErrorAction SilentlyContinue
}

Write-Output 'PASS devhub-windows-launcher override=args native=args+exit missing-artifact=127'
