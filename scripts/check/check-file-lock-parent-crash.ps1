param([Parameter(Mandatory=$true)][string]$Probe, [Parameter(Mandatory=$true)][string]$Evidence)
$ErrorActionPreference = 'Stop'
if (Test-Path -LiteralPath $Evidence) { throw 'Fresh evidence directory required' }
New-Item -ItemType Directory -Path $Evidence | Out-Null
$lock = Join-Path $Evidence 'stable-parent.lock'
$stdout = Join-Path $Evidence 'parent.stdout'
$stderr = Join-Path $Evidence 'parent.stderr'
$parent = Start-Process -FilePath $Probe -ArgumentList @('parent', ('"' + $lock + '"')) -WindowStyle Hidden -PassThru -RedirectStandardOutput $stdout -RedirectStandardError $stderr
$childId = $null
try {
    $deadline = [DateTime]::UtcNow.AddSeconds(10)
    do {
        if ($parent.HasExited) { throw 'Parent exited before lock publication' }
        $line = Get-Content -LiteralPath $stdout -ErrorAction SilentlyContinue | Select-Object -First 1
        if ($line -match '^LOCKED CHILD=([0-9]+)$') { $childId = [int]$Matches[1]; break }
        Start-Sleep -Milliseconds 50
    } while ([DateTime]::UtcNow -lt $deadline)
    if (!$childId) { throw 'No authenticated child PID observation' }
    $child = Get-Process -Id $childId -ErrorAction Stop
    $childStart = $child.StartTime
    & $Probe acquire $lock > (Join-Path $Evidence 'while-parent.stdout')
    if ($LASTEXITCODE -ne 3) { throw 'Concurrent writer was not excluded' }
    Stop-Process -Id $parent.Id
    if (!$parent.WaitForExit(5000)) { throw 'Parent did not terminate' }
    $stillLive = Get-Process -Id $childId -ErrorAction Stop
    if ($stillLive.StartTime -ne $childStart) { throw 'Child generation changed' }
    & $Probe acquire $lock > (Join-Path $Evidence 'after-crash.stdout')
    if ($LASTEXITCODE -ne 0 -or (Get-Content (Join-Path $Evidence 'after-crash.stdout') -Raw).Trim() -ne 'ACQUIRED') { throw 'Live child retained parent lock after crash' }
    'PASS: parent excluded concurrent writer; parent crash released lock while child remained alive'
} finally {
    if (!$parent.HasExited) { Stop-Process -Id $parent.Id -ErrorAction SilentlyContinue }
    if ($childId) {
        $owned = Get-Process -Id $childId -ErrorAction SilentlyContinue
        if ($owned -and $childStart -and $owned.StartTime -eq $childStart) { Stop-Process -Id $childId }
    }
}
