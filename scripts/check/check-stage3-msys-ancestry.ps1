param(
    [string]$EvidenceRoot = 'build/stage3-msys-ancestry',
    [string]$Provider = '',
    [string]$BashPath = 'C:/Program Files/Git/bin/bash.exe',
    [string]$WorkerLabel
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
if ($WorkerLabel) { Start-Sleep -Seconds 90; exit 0 }
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
if (-not [IO.Path]::IsPathRooted($EvidenceRoot)) { $EvidenceRoot = Join-Path $root $EvidenceRoot }
$EvidenceRoot = [IO.Path]::GetFullPath($EvidenceRoot)
if (-not $Provider) { $Provider = Join-Path $PSScriptRoot 'lib/bootstrap-stage3/windows-process-inventory.ps1' }
$Provider = [IO.Path]::GetFullPath($Provider)
$utf8 = [Text.UTF8Encoding]::new($false)
$powershell = Join-Path $env:SystemRoot 'System32/WindowsPowerShell/v1.0/powershell.exe'
$fixture = Join-Path $EvidenceRoot 'owner/scripts/bootstrap/bootstrap-from-scratch.sh'
$null = New-Item -ItemType Directory -Force (Split-Path $fixture)
$snapshot = Join-Path $EvidenceRoot 'snapshot.txt'
$fixtureBody = @'
set -eu
PATH=/usr/bin:/bin:$PATH
export PATH
powershell.exe -NoLogo -NoProfile -NonInteractive -ExecutionPolicy Bypass -File 'PROVIDER' -OutputPath 'SNAPSHOT'
'@
$fixtureBody = $fixtureBody.Replace('PROVIDER', $Provider.Replace('\', '/')).Replace('SNAPSHOT', $snapshot.Replace('\', '/'))
[IO.File]::WriteAllText($fixture, $fixtureBody.Replace("`r`n", "`n"), $utf8)
$launch = Join-Path $EvidenceRoot 'launch.sh'
$launchBody = "set -eu`nunset SIMPLE_BOOTSTRAP_SESSION_ID SIMPLE_BOOTSTRAP_SESSION_EXEC`nexec /usr/bin/perl '" + $root.Replace('\', '/') + "/scripts/check/lib/portable-session-exec.pl' /bin/sh '" + $fixture.Replace('\', '/') + "'`n"
[IO.File]::WriteAllText($launch, $launchBody, $utf8)
$control = $null
$owner = $null
try {
    $control = Start-Process -FilePath $powershell -ArgumentList @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', ('"' + $PSCommandPath + '"'), '-WorkerLabel', 'scripts/bootstrap/bootstrap-from-scratch.sh-unrelated') -PassThru -WindowStyle Hidden
    $null = $control.Handle
    $owner = Start-Process -FilePath $BashPath -ArgumentList @('--noprofile', '--norc', ('"' + $launch.Replace('\', '/') + '"')) -PassThru -WindowStyle Hidden -RedirectStandardOutput (Join-Path $EvidenceRoot 'stdout.log') -RedirectStandardError (Join-Path $EvidenceRoot 'stderr.log')
    $null = $owner.Handle
    if (-not $owner.WaitForExit(55000)) { throw 'real MSYS launch exceeded 55 seconds' }
    $owner.Refresh()
    if ($owner.ExitCode -ne 0) { throw 'inventory failed through real MSYS launch; see stderr.log' }
    if ($control.HasExited) { throw 'unrelated control exited before inventory validation' }
    $rows = @(Get-Content -LiteralPath $snapshot)
    $selfRows = @($rows | Where-Object { $_.Contains($fixture.Replace('\', '/')) })
    if ($selfRows.Count -ne 0) { throw 'own MSYS portable-session launcher was classified as concurrent work' }
    $controlRows = @($rows | Where-Object { $_ -match ('^' + $control.Id + '\|') })
    if ($controlRows.Count -ne 1 -or -not $controlRows[0].Contains('scripts/bootstrap/bootstrap-from-scratch.sh-unrelated')) { throw 'unrelated heavy control disappeared' }
    # Exercise the unchanged production rejection using this real inventory's
    # bootstrap count. This is test evidence, not an admission receipt.
    $count = @($rows | Where-Object { $_.Contains('scripts/bootstrap/bootstrap-from-scratch.sh') }).Count
    $gate = Join-Path $EvidenceRoot 'busy.env'
    [IO.File]::WriteAllText($gate, "process_scan_status=available`nprocess_scan_source=windows-cim`nconcurrent_native_build_count=0`nconcurrent_bootstrap_count=$count`nconcurrent_qemu_count=0`n", $utf8)
    $gateScript = Join-Path $EvidenceRoot 'gate.sh'
    $body = @'
set -eu
cd 'ROOT'
. scripts/check/lib/bootstrap-stage3/memory-admission.shs
bootstrap_stage3_manifest_value() { sed -n "s/^$1=//p" "$2"; }
set +e
bootstrap_stage3_memory_require_exclusive_heavy 'GATE' 33554432
status=$?
set -e
[ "$status" -eq 75 ]
'@
    $body = $body.Replace('ROOT', $root.Replace('\', '/')).Replace('GATE', $gate.Replace('\', '/'))
    [IO.File]::WriteAllText($gateScript, $body.Replace("`r`n", "`n"), $utf8)
    & $BashPath --noprofile --norc $gateScript
    if ($LASTEXITCODE -ne 0) { throw 'unrelated heavy work was not refused' }
    [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'result.sdn'), "status = `"PASS`"`nself_wrapper_rows = 0`nunrelated_control_pid = $($control.Id)`nheavy_gate_exit = 75`n", $utf8)
    Write-Output 'PASS real MSYS self ancestry and unrelated-heavy rejection'
} finally {
    foreach ($process in @($owner, $control)) {
        if ($null -ne $process) {
            try { if (-not $process.HasExited) { $process.Kill(); $null = $process.WaitForExit(5000) } } finally { $process.Dispose() }
        }
    }
}
