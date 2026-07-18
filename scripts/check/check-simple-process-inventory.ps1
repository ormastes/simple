param(
    [string]$EvidencePath = "build/simpleos_multiconfig_live_evidence/simple-process-inventory.env",
    [int]$ProcessLimit = 128,
    [int]$MaxSample = 20,
    [int]$MinAgeMinutes = 0,
    [switch]$Kill,
    [string]$ConfirmText = ""
)

$ErrorActionPreference = "Stop"

$scriptDir = Split-Path -Parent $PSCommandPath
$repoRoot = Resolve-Path -LiteralPath (Join-Path $scriptDir "..\..")

function Resolve-RepoPath([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path)) {
        return $path
    }
    if ([System.IO.Path]::IsPathRooted($path)) {
        return $path
    }
    return Join-Path $repoRoot $path
}

$EvidencePath = Resolve-RepoPath $EvidencePath

function Write-Rows([string[]]$rows) {
    $dir = Split-Path -Parent $EvidencePath
    if (-not [string]::IsNullOrWhiteSpace($dir)) {
        New-Item -ItemType Directory -Force -Path $dir | Out-Null
    }
    $rows | Set-Content -Encoding ASCII -Path $EvidencePath
    $rows | ForEach-Object { Write-Output $_ }
}

function Process-Age-Minutes($process) {
    try {
        $age = (Get-Date) - $process.StartTime
        return [int][Math]::Floor($age.TotalMinutes)
    } catch {
        return -1
    }
}

$processes = @(Get-Process -Name simple -ErrorAction SilentlyContinue)
$count = $processes.Count
$overLimit = $count -gt $ProcessLimit
$sample = @($processes | Sort-Object Id | Select-Object -First $MaxSample)
$samplePids = ($sample | ForEach-Object { $_.Id }) -join ";"
$sampleAges = ($sample | ForEach-Object { Process-Age-Minutes $_ }) -join ";"
$eligible = @()
foreach ($process in $processes) {
    $ageMinutes = Process-Age-Minutes $process
    if ($MinAgeMinutes -le 0 -or ($ageMinutes -ge $MinAgeMinutes)) {
        $eligible += $process
    }
}

$killed = 0
$killStatus = "not-requested"
if ($Kill) {
    if ($ConfirmText -ne "KILL_SIMPLE_PROCESSES") {
        $killStatus = "blocked:missing-confirmation"
    } else {
        foreach ($process in $eligible) {
            try {
                Stop-Process -Id $process.Id -Force -ErrorAction Stop
                $killed = $killed + 1
            } catch {
                $killStatus = "blocked:stop-process-failed"
                break
            }
        }
        if ($killStatus -eq "not-requested") {
            $killStatus = "pass"
        }
    }
}

$status = if ($overLimit) { "blocked:process-count-over-limit" } else { "pass" }
if ($Kill -and $killStatus -eq "pass") {
    $status = "killed-requested-processes"
}

$rows = @(
    "simple_process_inventory_status=$status",
    "simple_process_inventory_count=$count",
    "simple_process_inventory_limit=$ProcessLimit",
    "simple_process_inventory_over_limit=$($overLimit.ToString().ToLower())",
    "simple_process_inventory_sample_limit=$MaxSample",
    "simple_process_inventory_sample_pids=$samplePids",
    "simple_process_inventory_sample_age_minutes=$sampleAges",
    "simple_process_inventory_min_age_minutes=$MinAgeMinutes",
    "simple_process_inventory_kill_requested=$($Kill.IsPresent.ToString().ToLower())",
    "simple_process_inventory_kill_status=$killStatus",
    "simple_process_inventory_killed_count=$killed",
    "simple_process_inventory_evidence_path=$EvidencePath"
)
Write-Rows $rows
if ($status -eq "pass" -or $status -eq "killed-requested-processes") {
    exit 0
}
exit 1
