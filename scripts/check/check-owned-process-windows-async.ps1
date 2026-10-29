param([string]$Compiler = "")
$ErrorActionPreference = "Stop"
if ($env:OS -ne "Windows_NT") { throw "MissingEvidence: Windows-native compilation and execution required" }
$root = (Resolve-Path (Join-Path $PSScriptRoot "../..")).Path
Push-Location $root
try {
    if (-not $Compiler) {
        foreach ($candidate in @("clang-cl", "clang")) {
            $found = Get-Command $candidate -ErrorAction SilentlyContinue
            if ($found) { $Compiler = $found.Source; break }
        }
    }
    if (-not $Compiler) { throw "MissingEvidence: clang-cl or clang is required to compile the native C selfcheck" }
    $output = Join-Path $root "build/runtime-process-owned-windows-async"
    New-Item -ItemType Directory -Force -Path $output | Out-Null
    $binary = Join-Path $output "runtime_process_owned_windows_async_selfcheck.exe"
    $sources = @("src/runtime/test/runtime_process_owned_windows_async_selfcheck.c", "src/runtime/runtime_process_owned.c")
    if ([System.IO.Path]::GetFileNameWithoutExtension($Compiler) -eq "clang-cl") {
        & $Compiler /nologo /std:c11 /O2 /W4 /DRT_PROCESS_OWNED_CORE_ONLY /Isrc/runtime /Isrc/runtime/include "/Fe:$binary" @sources
    } else {
        & $Compiler -std=c11 -O2 -Wall -Wextra -DRT_PROCESS_OWNED_CORE_ONLY -I src/runtime -I src/runtime/include -o $binary @sources
    }
    if ($LASTEXITCODE -ne 0) { throw "Windows owner selfcheck compilation failed: $LASTEXITCODE" }
    & $binary
    if ($LASTEXITCODE -ne 0) { throw "Windows owner selfcheck failed: $LASTEXITCODE" }
} finally { Pop-Location }
