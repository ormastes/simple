param([string]$EvidenceRoot = 'build/stage3-inventory-diagnostic-test')

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$repoRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
if (-not [System.IO.Path]::IsPathRooted($EvidenceRoot)) { $EvidenceRoot = Join-Path $repoRoot $EvidenceRoot }
$evidence = [System.IO.Path]::GetFullPath($EvidenceRoot)
New-Item -ItemType Directory -Path $evidence -Force | Out-Null
$source = Join-Path $PSScriptRoot 'lib/bootstrap-stage3/windows-process-inventory.ps1'
$fixture = Join-Path $evidence 'failing-provider.ps1'
$snapshot = Join-Path $evidence 'snapshot.txt'
$stdout = Join-Path $evidence 'stdout.txt'
$stderr = Join-Path $evidence 'stderr.txt'
$text = [System.IO.File]::ReadAllText($source)
$needle = '$processes = @(Get-CimInstance -ClassName Win32_Process -OperationTimeoutSec 30)'
if (-not $text.Contains($needle)) { throw 'provider fixture could not locate the inventory query' }
$fixtureText = $text.Replace($needle, "throw 'controlled-inventory-failure'")
[System.IO.File]::WriteAllText($fixture, $fixtureText, [System.Text.UTF8Encoding]::new($false))
$nativePowerShell = Join-Path $env:SystemRoot 'System32/WindowsPowerShell/v1.0/powershell.exe'
$args = @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass',
    '-File', ('"' + $fixture + '"'), '-OutputPath', ('"' + $snapshot + '"'))
$process = Start-Process -FilePath $nativePowerShell -ArgumentList $args -PassThru -WindowStyle Hidden -RedirectStandardOutput $stdout -RedirectStandardError $stderr
try {
    $null = $process.Handle
    if (-not $process.WaitForExit(45000)) { $process.Kill(); throw 'fixture exceeded 45 seconds' }
    $process.Refresh()
    if ($process.ExitCode -eq 0) { throw 'failing worker was accepted' }
    $message = [System.IO.File]::ReadAllText($stderr)
    if (-not $message.Contains('Windows process inventory query failed: controlled-inventory-failure')) {
        throw 'worker error was not preserved by its owner'
    }
    if (Test-Path -LiteralPath $snapshot) { throw 'failed worker published an inventory' }
    Write-Output 'PASS — worker failure was rejected with its bounded diagnostic'
} finally { $process.Dispose() }

# The mock lives only in this private provider copy. It models a command-less
# gate-sensitive snapshot row whose PID either disappeared or is still live.
$mock = @'
function Get-CimInstance {
    param($ClassName, $OperationTimeoutSec, $Filter)
    if ($Filter) {
        if ($env:SIMPLE_INVENTORY_FIXTURE_LIVE -eq '1') {
            return [pscustomobject]@{ ProcessId = 500 }
        }
        return
    }
    return @(
        [pscustomobject]@{ ProcessId = 500; ParentProcessId = 1; WorkingSetSize = 1024; Name = 'cmd.exe'; CommandLine = $null },
        [pscustomobject]@{ ProcessId = 501; ParentProcessId = 1; WorkingSetSize = 2048; Name = 'system.exe'; CommandLine = 'system.exe' }
    )
}
'@
$raceFixture = Join-Path $evidence 'race-provider.ps1'
$raceText = $text.Replace('Set-StrictMode -Version Latest', "Set-StrictMode -Version Latest`n$mock")
[System.IO.File]::WriteAllText($raceFixture, $raceText, [System.Text.UTF8Encoding]::new($false))
foreach ($live in @('0', '1')) {
    $env:SIMPLE_INVENTORY_FIXTURE_LIVE = $live
    $raceSnapshot = Join-Path $evidence "race-$live.snapshot"
    $raceStdout = Join-Path $evidence "race-$live.stdout"
    $raceStderr = Join-Path $evidence "race-$live.stderr"
    $raceArgs = @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass',
        '-File', ('"' + $raceFixture + '"'), '-OutputPath', ('"' + $raceSnapshot + '"'))
    $race = Start-Process -FilePath $nativePowerShell -ArgumentList $raceArgs -PassThru -WindowStyle Hidden -RedirectStandardOutput $raceStdout -RedirectStandardError $raceStderr
    try {
        $null = $race.Handle
        if (-not $race.WaitForExit(45000)) { $race.Kill(); throw 'race fixture exceeded 45 seconds' }
        $race.Refresh()
        if ($live -eq '0') {
            if ($race.ExitCode -ne 0) { throw 'confirmed exited process was not omitted' }
            $rows = [System.IO.File]::ReadAllText($raceSnapshot)
            if ($rows -match '(?m)^500\|' -or $rows -notmatch '(?m)^501\|') { throw 'stale-process snapshot was incorrect' }
        } else {
            if ($race.ExitCode -eq 0) { throw 'live process without a command line was accepted' }
            if (-not ([System.IO.File]::ReadAllText($raceStderr)).Contains('command line unavailable for gate-sensitive PID 500')) {
                throw 'live-process refusal lost its diagnostic'
            }
        }
    } finally { $race.Dispose() }
}
Remove-Item Env:SIMPLE_INVENTORY_FIXTURE_LIVE -ErrorAction SilentlyContinue
Write-Output 'PASS — exited process omitted and live unknown process refused'
