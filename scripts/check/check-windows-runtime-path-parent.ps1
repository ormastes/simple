param(
    [string]$ClangCl = "C:\dev\tool\clang+llvm-23.1.1-x86_64-pc-windows-msvc\bin\clang-cl.exe"
)

$ErrorActionPreference = "Stop"
if (-not (Test-Path -LiteralPath $ClangCl)) {
    throw "LLVM 23.1.1 clang-cl authority not found: $ClangCl"
}
$compiler = (Resolve-Path -LiteralPath $ClangCl).Path
$version = (& $compiler --version 2>&1)
if ($LASTEXITCODE -ne 0 -or $version[0] -notmatch '^clang version 23\.1\.1 ') {
    throw "LLVM 23.1.1 clang-cl authority required: $compiler"
}
$compilerHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $compiler).Hash
Write-Host "clang_cl=$compiler"
Write-Host "clang_cl_version=$($version[0])"
Write-Host "clang_cl_sha256=$compilerHash"

$repo = (Resolve-Path (Join-Path $PSScriptRoot "..\..")).Path
$outDir = Join-Path $repo "build\check\windows-runtime-path-parent"
$exe = Join-Path $outDir "windows_path_parent_separator_test.exe"
New-Item -ItemType Directory -Force $outDir | Out-Null
Remove-Item -LiteralPath $exe -Force -ErrorAction SilentlyContinue

$sources = @(
    (Join-Path $repo "test\01_unit\runtime\windows_path_parent_separator_test.c"),
    (Join-Path $repo "test\01_unit\runtime\windows_path_parent_separator_stubs.c"),
    (Join-Path $repo "src\runtime\runtime_native.c")
)

& $compiler /nologo /std:c11 /utf-8 /DSIMPLE_RUNTIME_TESTING /D_CRT_SECURE_NO_WARNINGS /D_CRT_NONSTDC_NO_WARNINGS /Gy /Gw `
    "/I$(Join-Path $repo 'src\runtime')" `
    "/I$(Join-Path $repo 'src\runtime\platform')" `
    $sources /link /opt:ref "/out:$exe"
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

& $exe
exit $LASTEXITCODE
