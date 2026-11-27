param(
    [string]$ClangCl = 'C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe',
    [string]$Msvc = 'C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207',
    [string]$Sdk = 'C:/Program Files (x86)/Windows Kits/10',
    [string]$SdkVersion = '10.0.26100.0'
)
$ErrorActionPreference = 'Stop'
$root = Split-Path (Split-Path $PSScriptRoot)
$out = Join-Path $root ('build/sosix-crt-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory $out | Out-Null
$oldInclude = $env:INCLUDE; $oldLib = $env:LIB
try {
    $env:INCLUDE = "$Msvc/include;$Sdk/Include/$SdkVersion/ucrt;$Sdk/Include/$SdkVersion/shared;$Sdk/Include/$SdkVersion/um"
    $env:LIB = "$Msvc/lib/x64;$Sdk/Lib/$SdkVersion/ucrt/x64;$Sdk/Lib/$SdkVersion/um/x64"
    & $ClangCl /nologo /W3 /WX "/I$root/src/runtime" "$PSScriptRoot/sosix-directory-crt-regression.c" "/Fo$out/regression.obj" "/Fe$out/regression.exe" /link /stack:8388608
    if ($LASTEXITCODE) { throw 'compile failed' }
    $fixture = Join-Path $out 'fixture'; New-Item -ItemType Directory $fixture | Out-Null
    & "$out/regression.exe" $fixture
    if ($LASTEXITCODE) { throw 'regression failed' }
    # Prove the warning gate rejects the original deprecated API.
    '#include <string.h>', 'int main(void) { char out[8]; strcpy(out, "probe"); return out[0]; }' | Set-Content "$out/negative.c"
    $ErrorActionPreference = 'Continue'
    & $ClangCl /nologo /W3 /WX /c "$out/negative.c" "/Fo$out/negative.obj" *> "$out/negative.log"
    $negativeExit = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
    if ($negativeExit -eq 0 -or !(Select-String -Quiet 'deprecated' "$out/negative.log")) { throw 'negative warning control failed' }
    Write-Output "PASS deprecated-CRT negative control; evidence: $out"
} finally { $env:INCLUDE = $oldInclude; $env:LIB = $oldLib }
