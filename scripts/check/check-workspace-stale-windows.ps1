param(
    [string]$Compiler = "C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe",
    [string]$Msvc = "C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207",
    [string]$Sdk = "C:/Program Files (x86)/Windows Kits/10",
    [string]$Output = "build/workspace-stale-windows"
)
$ErrorActionPreference = "Stop"
$repo = (Resolve-Path "$PSScriptRoot/../..").Path
Push-Location $repo
$savedInclude = $env:INCLUDE
$savedLib = $env:LIB
try {
    if (-not (Test-Path -LiteralPath $Compiler)) { throw "Pinned clang-cl missing: $Compiler" }
    New-Item -ItemType Directory -Force $Output | Out-Null
    $env:INCLUDE = "$Msvc/include;$Sdk/Include/10.0.26100.0/ucrt;$Sdk/Include/10.0.26100.0/shared;$Sdk/Include/10.0.26100.0/um"
    $env:LIB = "$Msvc/lib/x64;$Sdk/Lib/10.0.26100.0/ucrt/x64;$Sdk/Lib/10.0.26100.0/um/x64"
    & $Compiler /nologo /MD /std:c11 /O2 /Gy /I src/runtime "/Fo$Output/stale.obj" "/Fe$Output/stale.exe" scripts/check/fixtures/runtime-workspace-stale-windows.c /link advapi32.lib
    if ($LASTEXITCODE -ne 0) { throw "Workspace stale fixture compile failed ($LASTEXITCODE)" }
    & "$repo/$Output/stale.exe"
    if ($LASTEXITCODE -ne 0) { throw "Workspace stale fixture failed ($LASTEXITCODE)" }
    Write-Output "PASS: Windows stale capability refusal, retained loans, and released-token invalidation"
} finally {
    $env:INCLUDE = $savedInclude
    $env:LIB = $savedLib
    Pop-Location
}
