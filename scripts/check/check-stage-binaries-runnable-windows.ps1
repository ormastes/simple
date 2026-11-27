param(
    [Parameter(Mandatory=$true)][string]$Evidence,
    [string]$Bash = 'C:/dev/tool/Git/bin/bash.exe',
    [string]$Compiler = 'C:/dev/tool/msys2/mingw64/bin/gcc.exe',
    [string]$Nm = 'C:/dev/tool/msys2/mingw64/bin/nm.exe'
)
$ErrorActionPreference = 'Stop'
# These native C programs are host guard fixtures, never Simple producers.
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
foreach ($required in @($Bash, $Compiler, $Nm)) {
    if (-not (Test-Path -LiteralPath $required -PathType Leaf)) { throw "Missing fixture prerequisite: $required" }
}
if (-not [IO.Path]::IsPathRooted($Evidence)) { $Evidence = Join-Path (Get-Location).Path $Evidence }
$Evidence = [IO.Path]::GetFullPath($Evidence)
if (Test-Path -LiteralPath $Evidence) { throw 'Fresh private evidence directory required' }
New-Item -ItemType Directory -Path $Evidence | Out-Null
$utf8 = New-Object Text.UTF8Encoding($false)

function Invoke-FixtureProcess([string]$Program, [string[]]$Arguments, [string]$Label) {
    $quoted = foreach ($argument in $Arguments) {
        if ($argument.Contains('"') -or $argument.EndsWith('\')) { throw 'Unsupported fixture argument quoting' }
        '"' + $argument + '"'
    }
    $stdout = Join-Path $Evidence ($Label + '.stdout')
    $stderr = Join-Path $Evidence ($Label + '.stderr')
    $child = Start-Process -FilePath $Program -ArgumentList ($quoted -join ' ') -WindowStyle Hidden -PassThru -RedirectStandardOutput $stdout -RedirectStandardError $stderr
    $null = $child.Handle
    if (-not $child.WaitForExit(120000)) { $child.Kill(); throw "Private fixture timed out: $Label" }
    return @{ Code = $child.ExitCode; Out = [IO.File]::ReadAllText($stdout); Err = [IO.File]::ReadAllText($stderr) }
}

function Require-Text([string]$Text, [string]$Expected) {
    if (-not $Text.Contains($Expected)) { throw "Missing guard evidence: $Expected" }
}

$source = Join-Path $Evidence 'host-fixture.c'
[IO.File]::WriteAllText($source, @'
#include <string.h>
int main(int argc, char **argv) {
#ifdef NEGATIVE
    if (argc > 1 && strcmp(argv[1], "--version") == 0) return 0;
    return 7;
#else
    (void)argc; (void)argv;
    return 0;
#endif
}
'@, $utf8)
$fixtureRepo = Join-Path $Evidence 'repo'
$nativeDir = Join-Path $fixtureRepo 'bootstrap/stage8/x86_64-pc-windows-msvc'
$negativeDir = Join-Path $fixtureRepo 'bootstrap/stage9/x86_64-pc-windows-msvc'
$foreignDir = Join-Path $fixtureRepo 'bootstrap/stage7/aarch64-pc-windows-msvc'
$invalidDir = Join-Path $fixtureRepo 'bootstrap/stage6/x86_64-pc-windows-msvc'
$bareDir = Join-Path $fixtureRepo 'bootstrap/stage5'
New-Item -ItemType Directory -Path $nativeDir, $negativeDir, $foreignDir, $invalidDir, $bareDir | Out-Null
$positive = Join-Path $nativeDir 'simple.exe'
$negative = Join-Path $negativeDir 'simple.exe'
$built = Invoke-FixtureProcess $Compiler @('-O0', '-s', $source, '-o', $positive) 'build-positive'
if ($built.Code -ne 0) { throw 'Native positive PE fixture failed to link' }
$builtNegative = Invoke-FixtureProcess $Compiler @('-O0', '-s', '-DNEGATIVE', $source, '-o', $negative) 'build-negative'
if ($builtNegative.Code -ne 0) { throw 'Native negative PE fixture failed to link' }
$symbols = Invoke-FixtureProcess $Nm @('-a', '--defined-only', $positive) 'stripped-symbol-table'
if ($symbols.Code -ne 0) { throw 'Symbol reader failed; an empty failed query is not stripped-PE evidence' }
if ($symbols.Out.Trim() -ne '') { throw 'Expected a genuinely stripped native PE fixture' }
$image = [IO.File]::ReadAllBytes($positive)
$header = [BitConverter]::ToInt32($image, 60)
if ($header -lt 64 -or $header + 24 -gt $image.Length -or $image[$header + 4] -ne 0x64 -or $image[$header + 5] -ne 0x86) {
    throw 'This fixture requires a native x86-64 Windows PE compiler'
}
# An architecture-header mutation is a skip/classification control, not an
# assertion that x86-64 machine code became an executable ARM64 program.
$foreign = [byte[]]$image.Clone()
$foreign[$header + 4] = 0x64; $foreign[$header + 5] = 0xaa
[IO.File]::WriteAllBytes((Join-Path $foreignDir 'simple.exe'), $foreign)
$invalid = [byte[]]$image.Clone()
$invalid[$header] = 0
[IO.File]::WriteAllBytes((Join-Path $invalidDir 'simple.exe'), $invalid)
Copy-Item -LiteralPath $positive -Destination (Join-Path $bareDir 'simple.exe')
$git = (Get-Command git -CommandType Application | Select-Object -First 1).Source
$initialized = Invoke-FixtureProcess $git @('init', '-q', $fixtureRepo) 'git-init'
if ($initialized.Code -ne 0) { throw 'Private fixture repository failed to initialize' }
$indexed = Invoke-FixtureProcess $git @('-C', $fixtureRepo, 'add', '-f', '--', 'bootstrap') 'git-index'
if ($indexed.Code -ne 0) { throw 'Private fixture binaries failed to enter the index' }
$runner = Join-Path $Evidence 'run.shs'
[IO.File]::WriteAllText($runner, "PATH=/usr/bin:/bin:`$PATH; export PATH`nsh ""`$1"" --root ""`$2"" --verbose --timeout 5`n", $utf8)
$guard = (Join-Path $repo 'scripts/check/check-stage-binaries-runnable.shs').Replace('\', '/')
$observed = Invoke-FixtureProcess $Bash @('--noprofile', '--norc', $runner.Replace('\', '/'), $guard, $fixtureRepo.Replace('\', '/')) 'guard'
if ($observed.Code -ne 1) { throw "Expected a named negative verdict, got exit $($observed.Code)" }
Require-Text $observed.Out 'selftest 11/11 fixtures correct'
Require-Text $observed.Out '6 invocation(s) executed across 2 binary(ies), 4 crashed/failed/wrong-arch'
Require-Text $observed.Out 'stage5/simple.exe:unscoped-stage-path'
Require-Text $observed.Out 'stage6/x86_64-pc-windows-msvc/simple.exe:invalid-pe-header'
Require-Text $observed.Out '1 foreign-triple scoped artifact(s) skipped, not counted as passing'
Require-Text $observed.Out 'stage7/aarch64-pc-windows-msvc/simple.exe:foreign-triple(pe-aarch64)'
foreach ($command in @('--version', 'compile', 'native-build')) {
    Require-Text $observed.Out ("stage8/x86_64-pc-windows-msvc/simple.exe {0} -> rc=0 (ok)" -f $command)
}
Require-Text $observed.Out 'stage9/x86_64-pc-windows-msvc/simple.exe:compile(fail,rc=7)'
Require-Text $observed.Out 'stage9/x86_64-pc-windows-msvc/simple.exe:native-build(fail,rc=7)'
$receipt = "classification: windows_host_guard_fixture`nlegacy_selftest_cases_passed: 11`nactual_native_pe_invocations: 6`nstripped_symbol_table: empty`nnegative_offenders: 4`nforeign_skips: 1`nsimple_compiler_or_bootstrap_admission: not_claimed`n"
[IO.File]::WriteAllText((Join-Path $Evidence 'receipt.sdn'), $receipt, $utf8)
Write-Output 'PASS: Windows stripped-PE fixture exercised 6 native invocations, 4 named offenders and 1 explicit foreign skip; host guard only'
