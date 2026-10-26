param(
    [Parameter(Mandatory=$true)][string]$OutputDirectory,
    [string]$Compiler = 'cc',
    [string]$Python = 'python',
    [string]$Bash = 'C:/msys64/usr/bin/bash.exe'
)
# Windows C-provider/production-value regression recipe. Each compiler/test
# process tree gets 120s, 1GiB RSS and a 16MiB combined log. Never uses runtime.c.
# No compiler seed, Simple suite, POSIX or performance admission is implied.
$ErrorActionPreference = 'Stop'
if ($env:OS -ne 'Windows_NT') { throw 'This recipe requires native Windows' }
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$out = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $out) { throw 'OutputDirectory must be fresh; existing evidence is never replaced' }
$cc = (Get-Command $Compiler -ErrorAction Stop).Source
$py = (Get-Command $Python -ErrorAction Stop).Source
if (-not (Test-Path -LiteralPath $Bash -PathType Leaf)) { throw 'MSYS bash not found' }
New-Item -ItemType Directory $out | Out-Null
$runtime = Join-Path $out 'runtime'
New-Item -ItemType Directory $runtime | Out-Null
$owners = @('runtime_native.c','runtime_process.c','runtime_legacy_core.c',
    'runtime_memory.c','runtime_thread.c','runtime_memtrack.c',
    'runtime_simd_dispatch.c','runtime_simd_utf8.c','runtime_process_owned.c')
foreach ($name in $owners) { Copy-Item -LiteralPath "$repo/src/runtime/$name" -Destination "$runtime/$name" }
Get-ChildItem -LiteralPath "$repo/src/runtime" -Filter '*.h' -File | ForEach-Object {
    Copy-Item -LiteralPath $_.FullName -Destination $runtime
}
Get-ChildItem -LiteralPath "$repo/src/runtime/platform" -Filter '*.h' -File -Recurse | ForEach-Object {
    $relative = [IO.Path]::GetRelativePath("$repo/src/runtime", $_.FullName)
    $target = Join-Path $runtime $relative
    New-Item -ItemType Directory -Force (Split-Path $target) | Out-Null
    Copy-Item -LiteralPath $_.FullName -Destination $target
}
foreach ($name in @('rt_process_capture_bytes_selfcheck.c','rt_process_capture_value_selfcheck.c')) {
    Copy-Item -LiteralPath "$repo/src/runtime/test/$name" -Destination "$out/$name"
}
$control = Join-Path $out 'control'
$helpers = @('scripts/bootstrap/run-process-group-timeout.shs',
    'scripts/resource/process-tree-rss-watchdog.pl',
    'scripts/bootstrap/bootstrap-session-exec.c',
    'scripts/bootstrap/run-process-group-bounded-log-windows.py')
foreach ($name in $helpers) {
    $target = Join-Path $control $name
    New-Item -ItemType Directory -Force (Split-Path $target) | Out-Null
    Copy-Item -LiteralPath "$repo/$name" -Destination $target
}
$wrapper = @'
#!/bin/bash
set -euo pipefail
export PATH=/usr/bin:/bin:$PATH
control=$(cygpath -au "$1")
packet=$(cygpath -au "$2")
shift 2
mkdir -p "$packet/tmp"
export TMPDIR="$packet/tmp" TMP="$(cygpath -aw "$packet/tmp")"
export TEMP="$TMP"
export SIMPLE_BOOTSTRAP_RSS_CAP_MODE=enforce
export SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=1048576
export SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=1048576
export SIMPLE_PROCESS_TREE_RSS_RECEIPT="$packet/rss.env"
unset SIMPLE_BOOTSTRAP_SESSION_ID SIMPLE_BOOTSTRAP_SESSION_EXEC
sh "$control/scripts/bootstrap/run-process-group-timeout.shs" 120 5 "$@"
'@
[IO.File]::WriteAllText("$out/run-contained.shs", $wrapper.Replace("`r`n","`n")+"`n", (New-Object Text.UTF8Encoding($false)))
$pins = @(Get-ChildItem -LiteralPath $out -File -Recurse | ForEach-Object {
    @{path=$_.FullName;sha256=(Get-FileHash -LiteralPath $_.FullName).Hash.ToLower()}
})
$pins += @{path=$cc;sha256=(Get-FileHash -LiteralPath $cc).Hash.ToLower()}
$pins | ConvertTo-Json | Set-Content "$out/input-pins.json"
$logger = "$control/scripts/bootstrap/run-process-group-bounded-log-windows.py"
$loggerHash = (Get-FileHash -LiteralPath $logger).Hash.ToLower()
function Confirm-Pins {
    foreach ($pin in $pins) {
        if ((Get-FileHash -LiteralPath $pin.path).Hash.ToLower() -ne $pin.sha256) { throw "Input changed: $($pin.path)" }
    }
}
function Invoke-Bounded([string]$Name, [string[]]$Command, [string]$Expected) {
    Confirm-Pins
    $packet = "$out/$Name"
    New-Item -ItemType Directory $packet | Out-Null
    $Command | ConvertTo-Json | Set-Content "$packet/command.json"
    $stagePins = @($Command | Where-Object { Test-Path -LiteralPath $_ -PathType Leaf } | ForEach-Object {
        @{path=$_;sha256=(Get-FileHash -LiteralPath $_).Hash.ToLower()}
    })
    $stagePins | ConvertTo-Json | Set-Content "$packet/execution-pins.json"
    & $py $logger --output-parent $packet --log-leaf output.log --receipt-leaf log.env --helper-sha256 $loggerHash --max-bytes 16777216 --timeout-seconds 150 --term-grace-seconds 5 -- $Bash --noprofile --norc "$out/run-contained.shs" $control $packet @Command
    $code = $LASTEXITCODE
    Confirm-Pins
    foreach ($pin in $stagePins) {
        if ((Get-FileHash -LiteralPath $pin.path).Hash.ToLower() -ne $pin.sha256) { throw "Executed input changed: $($pin.path)" }
    }
    $receipt = @{}
    foreach ($line in Get-Content "$packet/rss.env") { if ($line -match '^([^=]+)=(.*)$') { $receipt[$matches[1]]=$matches[2] } }
    if ($code -ne 0 -or $receipt.exit_status -ne '0' -or $receipt.status -ne 'complete' -or
        $receipt.quiescent -ne '1' -or $receipt.rss_cap_enforced -ne '1' -or
        $receipt.rss_limit_kib -ne '1048576' -or $receipt.session_helper_integrity -ne 'verified' -or
        $receipt.containment_scope -ne 'win32-job-object-no-breakaway') { throw "Stage failed: $Name (exit $code); retained $packet" }
    if ($Expected -and -not (Get-Content "$packet/output.log" -Raw).Contains($Expected)) { throw "Missing verdict: $Name" }
    Write-Output "$Name PASS (receipt and source pins verified)"
}
$common = @('-O2','-ffunction-sections','-fdata-sections','-I',$runtime)
$fixture = "$out/fixture.exe"
Invoke-Bounded 'build-provider' (@($cc)+$common+@("$out/rt_process_capture_bytes_selfcheck.c","$runtime/runtime_process.c",'-Wl,--gc-sections','-o',$fixture)) ''
Invoke-Bounded 'provider' @($fixture) 'RESULT cases=11 failures=0'
Invoke-Bounded 'reset' @($fixture,'--reset-only') 'CASE empty-then-text-reset PASS'
$abi = "$out/abi.exe"
$ownerPaths = @($owners | ForEach-Object { "$runtime/$_" })
Invoke-Bounded 'build-abi' (@($cc)+$common+@('-DSIMPLE_CORE_C_STANDALONE=1','-DSIMPLE_RUNTIME_MEMORY_OWNER=1',"$out/rt_process_capture_value_selfcheck.c")+$ownerPaths+@('-Wl,--gc-sections','-lws2_32','-luser32','-lshell32','-o',$abi)) ''
Invoke-Bounded 'abi' @($abi,$fixture) 'ABI_RESULT cases=5 failures=0'
Get-FileHash -LiteralPath $fixture,$abi | Select-Object Path,Hash | ConvertTo-Json | Set-Content "$out/binary-pins.json"
Write-Output 'PASS: Windows provider 11 cases, reset 2 cases, production value/tuple 5 cases; no Simple or performance admission'
