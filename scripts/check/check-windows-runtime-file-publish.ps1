param(
    [string]$Clang = 'C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang-cl.exe'
)
$ErrorActionPreference = 'Stop'
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$out = Join-Path $root 'build/native_probe/windows-file-publish'
[IO.Directory]::CreateDirectory($out) | Out-Null
$vswhere = Join-Path ${env:ProgramFiles(x86)} 'Microsoft Visual Studio/Installer/vswhere.exe'
$vs = & $vswhere -latest -products '*' -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath
if (!$vs -or !(Test-Path -LiteralPath $Clang)) { throw 'clang-cl and the Windows C SDK are required' }
$vcvars = Join-Path $vs 'VC/Auxiliary/Build/vcvars64.bat'
function Get-CFunction([string]$source, [string]$name) {
    $pattern = '(?ms)^(?:static\s+)?[a-zA-Z_][^\r\n]*\b' + [regex]::Escape($name) + '\([^\{]*\{.*?^\}'
    $match = [regex]::Matches($source, $pattern)
    if ($match.Count -ne 1) { throw "expected one production definition of $name" }
    return $match[0].Value
}
$failed = $false
foreach ($owner in @('runtime', 'runtime_native')) {
    $source = [IO.File]::ReadAllText((Join-Path $root "src/runtime/$owner.c"))
    $widen = if ($owner -eq 'runtime') { 'rt_widen_long_path_rc' } else { 'spl_widen_long_path' }
    # Compile the production function bodies verbatim, without unrelated runtime
    # exports that prevent a standalone COFF link. No mocked filesystem calls.
    $unit = "#include <windows.h>`n#include <stdint.h>`n#include <stdio.h>`n#include <stdlib.h>`n#include <string.h>`n#include <wchar.h>`n#define RT_TEXT_PATH_MAX 4096`n"
    foreach ($name in @('rt_text_arg_to_path', $widen, 'rt_secure_temp_dir_diag', 'rt_file_publish_noreplace')) {
        $unit += (Get-CFunction $source $name) + "`n"
    }
    $unit += [IO.File]::ReadAllText((Join-Path $root 'src/runtime/test/rt_windows_file_publish_selfcheck.c'))
    $c = Join-Path $out "$owner.c"
    $exe = Join-Path $out "$owner.exe"
    [IO.File]::WriteAllText($c, $unit, [Text.UTF8Encoding]::new($false))
    $batch = Join-Path $out "$owner-build.cmd"
    $commands = "@echo off`r`ncall `"$vcvars`" >nul`r`nif errorlevel 1 exit /b 2`r`n`"$Clang`" /nologo /TC /std:c11 /W4 /D_CRT_SECURE_NO_WARNINGS `"$c`" /Fo`"$out/$owner.obj`" /Fe`"$exe`"`r`nexit /b %errorlevel%`r`n"
    [IO.File]::WriteAllText($batch, $commands)
    & $env:ComSpec /d /c $batch *> (Join-Path $out "$owner.build.log")
    if ($LASTEXITCODE -ne 0) { throw "C compilation failed: $out/$owner.build.log" }
    & $exe $out *> (Join-Path $out "$owner.run.log")
    if ($LASTEXITCODE -ne 0) { $failed = $true }
    Get-Content -LiteralPath (Join-Path $out "$owner.run.log")
}
if ($failed) { exit 1 }
