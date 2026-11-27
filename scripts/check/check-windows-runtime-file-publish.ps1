param(
    [string]$Clang = 'C:\dev\tool\clang+llvm-23.1.1-x86_64-pc-windows-msvc\bin\clang-cl.exe',
    [string]$OutputDir = '',
    [ValidateSet('runtime', 'runtime_native')]
    [string[]]$Owners = @('runtime', 'runtime_native')
)
$ErrorActionPreference = 'Stop'
if ($Owners.Count -eq 0) { throw 'at least one runtime owner is required' }
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
if ([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT) { throw 'native Windows is required' }
$out = if ($OutputDir) { [IO.Path]::GetFullPath($OutputDir) } else { Join-Path $root "build/native_probe/windows-file-publish-$PID" }
if (Test-Path -LiteralPath $out) { throw "fresh output directory required: $out" }
[IO.Directory]::CreateDirectory($out) | Out-Null
$vswhere = Join-Path ${env:ProgramFiles(x86)} 'Microsoft Visual Studio/Installer/vswhere.exe'
$vs = & $vswhere -latest -products '*' -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath
if (!$vs -or !(Test-Path -LiteralPath $Clang)) { throw 'clang-cl and the Windows C SDK are required' }
$vcvars = Join-Path $vs 'VC/Auxiliary/Build/vcvars64.bat'
$clangHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $Clang).Hash
$harnessHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $PSCommandPath).Hash
$sourceRevision = (& git -C $root rev-parse HEAD)
if ($LASTEXITCODE -ne 0) { throw 'source revision query failed' }
$clangVersion = (& $Clang --version 2>&1 | Select-Object -First 1)
if ($LASTEXITCODE -ne 0) { throw 'clang-cl version query failed' }
function Invoke-RecordedProcess([string]$program, [string]$arguments, [string]$prefix) {
    # Windows PowerShell turns native stderr into terminating errors under
    # ErrorActionPreference=Stop. Capture raw streams and judge the exit code.
    $start = [Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $program
    $start.Arguments = $arguments
    $start.WorkingDirectory = $root
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.WindowStyle = [Diagnostics.ProcessWindowStyle]::Hidden
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $start
    if (!$process.Start()) { throw "native process did not start: $program" }
    $stdout = $process.StandardOutput.ReadToEndAsync()
    $stderr = $process.StandardError.ReadToEndAsync()
    if (!$process.WaitForExit(120000)) {
        & "$env:SystemRoot/System32/taskkill.exe" /PID $process.Id /T /F *> "$prefix.timeout.log"
        throw "native process timed out: $prefix"
    }
    $process.WaitForExit()
    [IO.File]::WriteAllText("$prefix.stdout.log", $stdout.GetAwaiter().GetResult())
    [IO.File]::WriteAllText("$prefix.stderr.log", $stderr.GetAwaiter().GetResult())
    $code = $process.ExitCode
    $process.Dispose()
    return $code
}
function Sdn-Quoted([string]$value) {
    '"' + $value.Replace('\', '\\').Replace('"', '\"').Replace("`r", '\r').Replace("`n", '\n') + '"'
}
function Get-CFunction([string]$source, [string]$name) {
    $pattern = '(?ms)^(?:static\s+)?[a-zA-Z_][^\r\n]*\b' + [regex]::Escape($name) + '\([^\{]*\{.*?^\}'
    $match = [regex]::Matches($source, $pattern)
    if ($match.Count -ne 1) { throw "expected one production definition of $name" }
    return $match[0].Value
}
$failed = $false
# rt_widen_long_path_rc (macro alias for rt_win_long_path_widen) used to be a
# byte-identical copy pasted separately into runtime.c and runtime_native.c;
# it now lives once in platform/runtime_win_long_path.h (host-OS-services
# routing: rt_* long-path/rename helpers belong next to the other Windows
# platform shims such as windows_raw_mapping.h) and both owners #include it,
# so it is read from the shared header instead of regex-extracted per owner.
$sharedHeader = [IO.File]::ReadAllText((Join-Path $root 'src/runtime/platform/runtime_win_long_path.h'))
$allocationHeaderPath = Join-Path $root 'src/runtime/runtime_alloc_observer.h'
$allocationHeader = [IO.File]::ReadAllText($allocationHeaderPath)
$allocationHeaderHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $allocationHeaderPath).Hash
$fixturePath = Join-Path $root 'src/runtime/test/rt_windows_file_publish_selfcheck.c'
$headerHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $root 'src/runtime/platform/runtime_win_long_path.h')).Hash
$fixtureHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $fixturePath).Hash
foreach ($owner in $Owners) {
    $sourcePath = Join-Path $root "src/runtime/$owner.c"
    $source = [IO.File]::ReadAllText($sourcePath)
    $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
    # Compile the production function bodies verbatim, without unrelated runtime
    # exports that prevent a standalone COFF link. No mocked filesystem calls.
    $unit = "#include <windows.h>`n#include <stdint.h>`n#include <stdio.h>`n#include <stdlib.h>`n#include <string.h>`n#include <wchar.h>`n#define RT_TEXT_PATH_MAX 4096`n"
    $unit += $sharedHeader + "`n"
    # Keep the native owner's real helper and its real disabled-observer
    # allocation macros; no path or filesystem implementation is substituted.
    $unit += $allocationHeader + "`n"
    $names = @('rt_text_arg_to_path', 'rt_secure_temp_dir_diag')
    if ($owner -eq 'runtime_native') { $names += 'spl_widen_long_path' }
    $names += 'rt_file_publish_noreplace'
    foreach ($name in $names) {
        $unit += (Get-CFunction $source $name) + "`n"
    }
    $unit += [IO.File]::ReadAllText($fixturePath)
    $c = Join-Path $out "$owner.c"
    $exe = Join-Path $out "$owner.exe"
    [IO.File]::WriteAllText($c, $unit, [Text.UTF8Encoding]::new($false))
    $unitHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $c).Hash
    $batch = Join-Path $out "$owner-build.cmd"
    $commands = "@echo off`r`ncall `"$vcvars`" >nul`r`nif errorlevel 1 exit /b 2`r`n`"$Clang`" /nologo /TC /std:c11 /utf-8 /W4 /D_CRT_SECURE_NO_WARNINGS `"$c`" /Fo`"$out/$owner.obj`" /Fe`"$exe`"`r`nexit /b %errorlevel%`r`n"
    [IO.File]::WriteAllText($batch, $commands)
    $buildExit = Invoke-RecordedProcess $env:ComSpec ('/d /c ""' + $batch + '""') (Join-Path $out "$owner.build")
    $runExit = -1
    $exeHash = ''
    if ($buildExit -eq 0 -and (Test-Path -LiteralPath $exe)) {
        $exeHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $exe).Hash
        $runExit = Invoke-RecordedProcess $exe ('"' + $out + '"') (Join-Path $out "$owner.run")
    }
    $summary = if ($runExit -ne -1) { [IO.File]::ReadAllText((Join-Path $out "$owner.run.stdout.log")).Trim() } else { 'fixture not executed' }
    if ($buildExit -ne 0 -or $runExit -ne 0 -or $summary -notmatch '^Windows publication: cases=5 checks=[1-9][0-9]* failures=0$') { $failed = $true }
    $receipt = @(
        'native_file_publish:'
        "  owner: $owner"
        ('  base_revision: ' + (Sdn-Quoted "$sourceRevision"))
        ('  source_sha256: ' + (Sdn-Quoted $sourceHash))
        ('  shared_header_sha256: ' + (Sdn-Quoted $headerHash))
        ('  allocation_header_sha256: ' + (Sdn-Quoted $allocationHeaderHash))
        ('  fixture_sha256: ' + (Sdn-Quoted $fixtureHash))
        ('  harness_sha256: ' + (Sdn-Quoted $harnessHash))
        ('  extracted_unit_sha256: ' + (Sdn-Quoted $unitHash))
        ('  clang_sha256: ' + (Sdn-Quoted $clangHash))
        ('  clang_version: ' + (Sdn-Quoted "$clangVersion"))
        ('  build_command_file: ' + (Sdn-Quoted $batch))
        "  build_exit: $buildExit"
        "  run_exit: $runExit"
        ('  executable_sha256: ' + (Sdn-Quoted $exeHash))
        ('  summary: ' + (Sdn-Quoted $summary))
        '  evidence_scope: native-production-function-extraction'
        '  simple_runtime_admission: not-established'
    ) -join "`n"
    [IO.File]::WriteAllText((Join-Path $out "$owner.receipt.sdn"), $receipt + "`n", [Text.UTF8Encoding]::new($false))
    Write-Output "$owner build_exit=$buildExit run_exit=$runExit $summary"
}
if ($failed) { exit 1 }
