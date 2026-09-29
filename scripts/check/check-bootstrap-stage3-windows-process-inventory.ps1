param(
    [string]$EvidenceRoot = 'build/stage3-windows-process-inventory',
    [string]$BashPath = 'C:/msys64/usr/bin/bash.exe',
    [switch]$BindingOnly,
    [string]$WorkerLabel
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
if ($WorkerLabel) {
    # Real owned OS process with an admission-classification control in argv.
    # It sleeps; this control does not claim to execute a bootstrap/compiler.
    Start-Sleep -Seconds 120
    exit 0
}

$repoRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
if (-not [System.IO.Path]::IsPathRooted($EvidenceRoot)) { $EvidenceRoot = Join-Path $repoRoot $EvidenceRoot }
$EvidenceRoot = [System.IO.Path]::GetFullPath($EvidenceRoot)
New-Item -ItemType Directory -Force -Path $EvidenceRoot | Out-Null
$nativePowerShell = Join-Path $env:SystemRoot 'System32/WindowsPowerShell/v1.0/powershell.exe'
$utf8 = [System.Text.UTF8Encoding]::new($false)
$children = [System.Collections.Generic.List[System.Diagnostics.Process]]::new()

function Write-Utf8([string]$path, [string]$content) {
    [System.IO.File]::WriteAllText($path, $content, $utf8)
}

function Run-Shell([string]$body, [string]$name) {
    $script = Join-Path $EvidenceRoot ($name + '.sh')
    $stdout = Join-Path $EvidenceRoot ($name + '.stdout')
    $stderr = Join-Path $EvidenceRoot ($name + '.stderr')
    $source = $repoRoot.Replace('\', '/')
    $evidence = $EvidenceRoot.Replace('\', '/')
    $preamble = @"
set -eu
PATH=/usr/bin:/bin:`$PATH
export PATH
cd '$source'
TMPDIR='$evidence'
export TMPDIR
BOOTSTRAP_STAGE3_FACADE_PATH=`$(pwd -P)/scripts/check/lib/bootstrap-stage3-provenance.shs
export BOOTSTRAP_STAGE3_FACADE_PATH
. "`$BOOTSTRAP_STAGE3_FACADE_PATH"
. scripts/check/lib/bootstrap-stage3/memory-admission.shs
unset SIMPLE_BOOTSTRAP_STAGE3_PROCESS_SNAPSHOT
"@
    Write-Utf8 $script (($preamble + "`n" + $body + "`n").Replace("`r`n", "`n"))
    $process = Start-Process -FilePath $BashPath -ArgumentList @('--noprofile', '--norc', ('"' + $script.Replace('\', '/') + '"')) -PassThru -WindowStyle Hidden -RedirectStandardOutput $stdout -RedirectStandardError $stderr
    try {
        $null = $process.Handle
        if (-not $process.WaitForExit(30000)) { $process.Kill(); $null = $process.WaitForExit(5000); throw "$name exceeded 30 seconds" }
        $process.Refresh()
        if ($null -eq $process.ExitCode -or $process.ExitCode -ne 0) { throw "$name failed; see $stderr" }
    } finally { $process.Dispose() }
}

function Start-Control([string]$label) {
    $options = @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass',
        '-File', ('"' + $PSCommandPath + '"'), '-WorkerLabel', ('"' + $label + '"'))
    $process = Start-Process -FilePath $nativePowerShell -ArgumentList $options -PassThru -WindowStyle Hidden
    $null = $process.Handle
    $children.Add($process)
    return $process
}

if ($BindingOnly) {
    Run-Shell @'
original_root=$(pwd -P)
original_facade=$BOOTSTRAP_STAGE3_FACADE_PATH
provider_rel=scripts/check/lib/bootstrap-stage3/windows-process-inventory.ps1
capture="$TMPDIR/authority-capture.ps1"
bootstrap_stage3_memory_capture_windows_provider "$capture"
[ "$bootstrap_stage3_memory_windows_root" = "$original_root" ]
[ "$bootstrap_stage3_memory_windows_commit" = "$(git rev-parse HEAD)" ]
git cat-file blob "$bootstrap_stage3_memory_windows_blob" >"$TMPDIR/expected-provider.ps1"
cmp "$capture" "$TMPDIR/expected-provider.ps1"
out="$TMPDIR/committed-provider.env"
: >"$out"
bootstrap_stage3_memory_append_processes "$out"
[ "$(bootstrap_stage3_manifest_value process_scan_source "$out")" = windows-cim ]
[ "$(bootstrap_stage3_manifest_value process_scan_status "$out")" = available ]
[ "$(bootstrap_stage3_manifest_value process_scan_git_head "$out")" = "$(git rev-parse HEAD)" ]
[ "$(bootstrap_stage3_manifest_value process_scan_provider_blob "$out")" = "$(git rev-parse "HEAD:$provider_rel")" ]

# A private real Git repository exercises failed source authority without
# editing the production checkout or claiming a bootstrap admission receipt.
fixture="$TMPDIR/authority-fixture"
mkdir -p "$fixture/scripts/check/lib/bootstrap-stage3"
cp "$original_facade" "$fixture/scripts/check/lib/bootstrap-stage3-provenance.shs"
for helper in authority command-snapshot sanity manifest-write manifest-verify self-test; do
    cp "$original_root/scripts/check/lib/bootstrap-stage3/$helper.shs" \
        "$fixture/scripts/check/lib/bootstrap-stage3/$helper.shs"
done
git -C "$fixture" init -q
git -C "$fixture" config user.name 'Inventory authority regression'
git -C "$fixture" config user.email 'inventory-regression@example.invalid'
git -C "$fixture" config core.autocrlf false
git -C "$fixture" add scripts
git -C "$fixture" -c core.hooksPath=/dev/null commit -qm 'Fixture without provider'
BOOTSTRAP_STAGE3_FACADE_PATH=$fixture/scripts/check/lib/bootstrap-stage3-provenance.shs
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
if bootstrap_stage3_memory_capture_windows_provider "$capture"; then
    echo 'missing committed provider was accepted' >&2; exit 1
fi
cp "$original_root/$provider_rel" "$fixture/$provider_rel"
git -C "$fixture" add "$provider_rel"
git -C "$fixture" -c core.hooksPath=/dev/null commit -qm 'Fixture committed provider'
bootstrap_stage3_memory_capture_windows_provider "$capture"
printf '\n# changed working bytes\n' >>"$fixture/$provider_rel"
if bootstrap_stage3_memory_capture_windows_provider "$capture"; then
    echo 'changed working provider was accepted' >&2; exit 1
fi
git -C "$fixture" show "HEAD:$provider_rel" >"$fixture/$provider_rel"
bootstrap_stage3_memory_capture_windows_provider "$capture"
printf '\n# changed captured bytes\n' >>"$capture"
if bootstrap_stage3_memory_validate_windows_provider; then
    echo 'changed captured provider was accepted' >&2; exit 1
fi
bootstrap_stage3_memory_capture_windows_provider "$capture"
git -C "$fixture" -c core.hooksPath=/dev/null commit --allow-empty -qm 'Fixture authority advanced'
if bootstrap_stage3_memory_validate_windows_provider; then
    echo 'changed pinned HEAD was accepted' >&2; exit 1
fi
BOOTSTRAP_STAGE3_FACADE_PATH=$original_facade
if bootstrap_stage3_memory_capture_windows_provider "$capture"; then
    echo 'facade root mismatch was accepted' >&2; exit 1
fi
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
printf 'status=PASS\nprovider=windows-cim\nauthority=committed-git-blob\nfailure_controls=5\n' >"$TMPDIR/result.env"
echo 'PASS committed provider execution and five authority refusal controls'
'@ 'binding-only'
    Write-Output 'STATUS: PASS Windows provider committed-source binding'
    exit 0
}

try {
    $provider = Join-Path $PSScriptRoot 'lib/bootstrap-stage3/windows-process-inventory.ps1'
    $snapshot = Join-Path $EvidenceRoot 'native.snapshot'
    & $nativePowerShell -NoLogo -NoProfile -NonInteractive -ExecutionPolicy Bypass -File $provider -OutputPath $snapshot
    if ($LASTEXITCODE -ne 0) { throw 'Real CIM provider failed' }
    $rows = @(Get-Content -LiteralPath $snapshot -Encoding UTF8)
    if ($rows.Count -eq 0) { throw 'Real CIM snapshot was empty' }
    $mine = @($rows | Where-Object { $_ -match ('^' + $PID + '\|') })
    if ($mine.Count -ne 1) { throw 'Real inventory did not contain the test owner PID exactly once' }
    $fields = $mine[0].Split('|', 4)
    $actual = Get-CimInstance Win32_Process -Filter "ProcessId=$PID" -OperationTimeoutSec 10
    if ([uint32]$fields[1] -ne [uint32]$actual.ParentProcessId -or [uint64]$fields[2] -eq 0) {
        throw 'Real provider returned incorrect PPID or zero RSS for live test owner'
    }
    foreach ($row in $rows) {
        if ($row -notmatch '^\d+\|\d+\|\d+\|[^\r\n|]+$') { throw 'Malformed real inventory row' }
    }

    $native = Start-Control '/simple native-build --inventory-control'
    $qemu = Start-Control 'qemu-system-inventory-control'
    $bootstrap1 = Start-Control 'scripts/bootstrap/bootstrap-from-scratch.sh --inventory-control-one'
    $bootstrap2 = Start-Control 'scripts/bootstrap/bootstrap-from-scratch.sh --inventory-control-two'
    $controlScript = @'
out="$TMPDIR/busy.env"
: >"$out"
bootstrap_stage3_memory_append_processes "$out"
[ "$(bootstrap_stage3_manifest_value process_scan_source "$out")" = windows-cim ]
[ "$(bootstrap_stage3_manifest_value process_scan_status "$out")" = available ]
for expected in CONTROL_NATIVE CONTROL_QEMU CONTROL_BOOTSTRAP1 CONTROL_BOOTSTRAP2; do
    grep -Eq "^process_[0-9]+_pid=$expected$" "$out"
done
[ "$(bootstrap_stage3_manifest_value concurrent_native_build_count "$out")" -ge 1 ]
[ "$(bootstrap_stage3_manifest_value concurrent_bootstrap_count "$out")" -ge 2 ]
[ "$(bootstrap_stage3_manifest_value concurrent_qemu_count "$out")" -ge 1 ]
set +e
bootstrap_stage3_memory_require_exclusive_heavy "$out"
status=$?
set -e
[ "$status" -eq 75 ]
printf 'process_scan_status=unavailable\n' >"$TMPDIR/unavailable.env"
set +e
bootstrap_stage3_memory_require_exclusive_heavy "$TMPDIR/unavailable.env"
status=$?
set -e
[ "$status" -eq 75 ]
echo 'PASS real Windows inventory and heavy/unavailable refusal'
'@
    $controlScript = $controlScript.Replace('CONTROL_NATIVE', [string]$native.Id).Replace('CONTROL_QEMU', [string]$qemu.Id).Replace('CONTROL_BOOTSTRAP1', [string]$bootstrap1.Id).Replace('CONTROL_BOOTSTRAP2', [string]$bootstrap2.Id)
    Run-Shell $controlScript 'busy-gate'
    Write-Utf8 (Join-Path $EvidenceRoot 'result.env') "status=PASS`nprovider=windows-cim`nowner_pid=$PID`nrows=$($rows.Count)`nheavy_gate_exit=75`nunavailable_gate_exit=75`n"
    Write-Output 'STATUS: PASS Windows Stage3 process inventory (real CIM + actual gate refusal)'
} finally {
    foreach ($child in $children) {
        try { if (-not $child.HasExited) { $child.Kill(); $null = $child.WaitForExit(5000) } } finally { $child.Dispose() }
    }
}
