param([Parameter(Mandatory=$true)][string]$OutputDirectory)
$ErrorActionPreference = 'Continue'
$repo = (Resolve-Path "$PSScriptRoot/../..").Path
if (Test-Path -LiteralPath $OutputDirectory) { throw 'Use a fresh output directory to preserve evidence' }
New-Item -ItemType Directory -Path $OutputDirectory | Out-Null
$out = (Resolve-Path -LiteralPath $OutputDirectory).Path
$llvm = 'C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin'
$vc = 'C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207'
$sdk = 'C:/Program Files (x86)/Windows Kits/10'
$savedInclude = $env:INCLUDE
$savedLib = $env:LIB
try {
    $env:INCLUDE = "$vc/include;$sdk/Include/10.0.26100.0/ucrt;$sdk/Include/10.0.26100.0/um;$sdk/Include/10.0.26100.0/shared"
    $env:LIB = "$vc/lib/x64;$sdk/Lib/10.0.26100.0/ucrt/x64;$sdk/Lib/10.0.26100.0/um/x64"
    $flags = @('-c','-O1','-Gy','-Gw','-GS-','-std:c11','-DSIMPLE_CORE_C_STANDALONE=1','-DSIMPLE_RUNTIME_MEMORY_OWNER=1',"-I$repo/src/runtime","-I$repo/src/runtime/platform",'/WX')
    & "$llvm/clang-cl.exe" @flags "$repo/src/runtime/runtime_thread.c" "-Fo$out/runtime_thread.obj" *> "$out/compile.log"
    if ($LASTEXITCODE -ne 0) { throw "Production TU /WX failed: $out/compile.log" }
    # This unchanged dependency retains its existing CRT deprecation warning.
    # /WX admission above applies to the owned production TU.
    & "$llvm/clang-cl.exe" @($flags | Where-Object { $_ -ne "/WX" }) "$repo/src/runtime/runtime_memtrack.c" "-Fo$out/runtime_memtrack.obj" *> "$out/memtrack-compile.log"
    if ($LASTEXITCODE -ne 0) { throw "Memory tracking dependency compile failed" }
    & "$llvm/clang-cl.exe" @flags "$PSScriptRoot/fixtures/runtime-thread-unused-pool-abi.c" "-Fo$out/unused-pool-abi.obj" *> "$out/unused-pool-abi-compile.log"
    if ($LASTEXITCODE -ne 0) { throw "Fixture dependency compile failed" }
    foreach ($mode in @('absent','present','empty')) {
        $defines = @()
        if ($mode -eq 'present') { $defines = @('-DTEST_WORKER_PROVIDER=1') }
        if ($mode -eq 'empty') { $defines = @('-DTEST_EMPTY_WORKER_PROVIDER=1') }
        & "$llvm/clang-cl.exe" @flags @defines "$PSScriptRoot/fixtures/runtime-thread-optional-worker.c" "-Fo$out/$mode.obj" *> "$out/$mode-compile.log"
        if ($LASTEXITCODE -ne 0) { throw "Fixture compile failed: $mode" }
        & "$llvm/lld-link.exe" "$out/$mode.obj" "$out/runtime_thread.obj" "$out/runtime_memtrack.obj" "$out/unused-pool-abi.obj" "/out:$out/$mode.exe" /subsystem:console /opt:ref /opt:icf kernel32.lib *> "$out/$mode-link.log"
        if ($LASTEXITCODE -ne 0) { throw "Fixture link failed: $out/$mode-link.log" }
        & "$out/$mode.exe" *> "$out/$mode-run.log"
        if ($LASTEXITCODE -ne 0) { throw "Production worker behavior failed: $mode" }
    }
    'PASS: production runtime_thread.c /WX; absent provider returns zero; present provider executes pool ID; empty linked provider spawns and joins' | Tee-Object -FilePath "$out/result.sdn"
} finally {
    $env:INCLUDE = $savedInclude
    $env:LIB = $savedLib
}
