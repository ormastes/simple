param([Parameter(Mandatory=$true)][string]$Compiler,
      [Parameter(Mandatory=$true)][string]$OutputDirectory)

$ErrorActionPreference = 'Stop'
if (-not (Test-Path -LiteralPath $Compiler) -or -not $env:INCLUDE -or -not $env:LIB) {
    throw 'pinned clang-cl and initialized MSVC SDK environment required'
}
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$output = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $output) { throw 'qualification output must be new' }
New-Item -ItemType Directory -Path $output | Out-Null
$source = Join-Path $repo 'test/01_unit/runtime/windows_private_atomic_write_test.c'
$object = Join-Path $output 'windows-private-atomic.obj'
$binary = Join-Path $output 'windows-private-atomic.exe'
$log = Join-Path $output 'build.log'
$previousPreference = $ErrorActionPreference
try {
    $ErrorActionPreference = 'Continue'
    & $Compiler '/nologo' '/O1' '/std:c11' '/D_CRT_SECURE_NO_WARNINGS' "/I$repo" $source "/Fo$object" "/Fe$binary" '/link' 'advapi32.lib' *> $log
    $compileExit = $LASTEXITCODE
} finally {
    $ErrorActionPreference = $previousPreference
}
if ($compileExit -ne 0) { throw "native provider build failed; inspect $log" }
& $binary
if ($LASTEXITCODE -ne 0) { throw 'actual Windows private atomic provider regression failed' }
Get-FileHash -LiteralPath $binary -Algorithm SHA256
