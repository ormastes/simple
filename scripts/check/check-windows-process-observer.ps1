$ErrorActionPreference = 'Stop'
. "$PSScriptRoot/../resource/windows-process-observer.ps1"

function Require([bool]$Condition, [string]$Message) {
    if (-not $Condition) { throw $Message }
}
function Entry([int]$Id, [int]$Parent, [string]$Name, [long]$Cpu, [long]$Rss) {
    [pscustomobject]@{
        ProcessId=$Id; ParentProcessId=$Parent; Name=$Name
        CreationDate=[datetime]'2026-10-09T01:02:03.1234567Z'
        KernelModeTime=0L; UserModeTime=$Cpu; WorkingSetSize=$Rss
    }
}
$fixture = @(
    (Entry 100 1 'python.exe' 10000000 1024),
    (Entry 200 100 'cargo.exe' 25000000 2048),
    (Entry 300 200 'rustc.exe' 1237500000 2097152),
    (Entry 400 100 'watcher.exe' 900000000 8192),
    (Entry 500 400 'observer.exe' 900000000 8192),
    (Entry 999 1 'unrelated.exe' 9000000000 900000000)
)
$rows = @(ConvertTo-BootstrapProgressRows $fixture 100 400)
Require ($rows.Count -eq 3) 'native child/grandchild count or watcher exclusion'
Require ($rows[2] -match '^300 200 300 2048 .* 123\.7500000 rustc\.exe$') 'native CPU units/RSS/ancestry'
Require (-not ($rows -match 'watcher|observer|unrelated')) 'unrelated/watcher process leaked'
Require ($rows[0] -match '01:02:03\.1234567') 'subsecond creation identity lost'
# MSYS exec: perl's native parent 650 is the exited fork intermediate.
$execFixture = $fixture + @((Entry 600 650 'perl.exe' 50000000 4096))
$unbridged = @(ConvertTo-BootstrapProgressRows $execFixture 100 400)
Require ($unbridged.Count -eq 3) 'exec child reachable without bridge (fixture invalid)'
$bridgedRows = @(ConvertTo-BootstrapProgressRows $execFixture 100 400 '600:100,500:400')
Require ($bridgedRows.Count -eq 4) 'MSYS exec child not bridged into tree'
Require (@($bridgedRows -match '^600 100 600 4 .* perl\.exe$').Count -eq 1) 'bridged child must report its MSYS parent'
Require (-not ($bridgedRows -match 'observer|watcher')) 'bridge leaked excluded watcher subtree'
$failed = $false
try { ConvertTo-BootstrapProgressRows $execFixture 100 400 '600-100' | Out-Null } catch { $failed = $true }
Require $failed 'malformed bridge edge accepted'
$pageFixture = @(Entry 101 1 'page-units.exe' 0 (180 * 1024 * 1024))
$pageRows = @(ConvertTo-BootstrapProgressRows $pageFixture 101 0)
Require (($pageRows[0] -split ' ')[3] -eq '184320') '180 MiB bytes must remain 184320 KiB, not MSYS 16x page inflation'

$oldCulture = [Globalization.CultureInfo]::CurrentCulture
try {
    [Globalization.CultureInfo]::CurrentCulture = [Globalization.CultureInfo]'de-DE'
    $localized = @(ConvertTo-BootstrapProgressRows $fixture 100 400)
    Require (($localized -join "`n") -ceq ($rows -join "`n")) 'locale changed numeric/birth identity wire format'
} finally { [Globalization.CultureInfo]::CurrentCulture = $oldCulture }

$fixture[2].CreationDate = ([datetime]$fixture[2].CreationDate).AddTicks(1)
$reused = @(ConvertTo-BootstrapProgressRows $fixture 100 400)
Require ($reused[2] -cne $rows[2]) 'reused PID inherited old birth identity'

$partial = @()
$failed = $false
$fixture[2].UserModeTime = $null
try { $partial = @(ConvertTo-BootstrapProgressRows $fixture 100 400) } catch { $failed = $true }
Require ($failed -and $partial.Count -eq 0) 'partial native snapshot escaped as healthy'
$failed = $false
try { ConvertTo-BootstrapProgressRows $fixture 777 400 | Out-Null } catch { $failed = $true }
Require $failed 'missing root accepted as empty healthy tree'
$nativeIdentity = Get-BootstrapNativeProcessIdentity $PID
Require ($nativeIdentity -match ('^windows:' + $PID + ':\d+$')) 'native birth token malformed'
Require ((Get-BootstrapNativeProcessIdentity $PID) -ceq $nativeIdentity) 'live native birth identity changed'
$failed = $false
try { Get-BootstrapNativeProcessIdentity 0 | Out-Null } catch { $failed = $true }
Require $failed 'invalid native PID accepted'
$supervisor = Entry 601 100 'bootstrap-session-exec.exe' 0 1024
$supervisor | Add-Member CommandLine 'bootstrap-session-exec.exe --supervise --spec fixture'
$jobFixture = @((Entry 100 1 'sh.exe' 0 1024), $supervisor,
    (Entry 602 777 'sh.exe' 0 1024), (Entry 603 602 'simple.exe' 3500000000 1153433600),
    (Entry 604 602 'watcher.exe' 0 1024), (Entry 605 604 'observer.exe' 0 1024),
    (Entry 606 1 'unrelated.exe' 0 1024))
$jobRows = @(ConvertTo-BootstrapProgressRows $jobFixture 100 604 '' { param($OwnerId)
    if ($OwnerId -ne 601) { throw 'queried unrelated supervisor' }; @(602,603,604,605)
})
Require ($jobRows.Count -eq 4) 'orphaned job workload missing or exclusion leaked'
Require (@($jobRows -match '^602 601 602 ').Count -eq 1) 'job root not bridged to supervisor'
Require (@($jobRows -match '^603 602 603 1126400 .* 350\.0000000 simple\.exe$').Count -eq 1) 'job compiler CPU/RSS missing'
$partial = @(); $failed = $false
try { $partial = @(ConvertTo-BootstrapProgressRows $jobFixture 100 604 '' { @(602,9999) }) } catch { $failed = $true }
Require ($failed -and $partial.Count -eq 0) 'missing job member escaped as healthy partial snapshot'
$partial = @(); $failed = $false
try { $partial = @(ConvertTo-BootstrapProgressRows $jobFixture 100 604 '' { throw 'job query unavailable' }) } catch { $failed = $true }
Require ($failed -and $partial.Count -eq 0) 'job query failure escaped as healthy partial snapshot'
$excludedRows = @(ConvertTo-BootstrapProgressRows $jobFixture 100 601 '' { throw 'excluded supervisor queried' })
Require ($excludedRows.Count -eq 1) 'excluded supervisor job was queried'
$supervisor.CommandLine = 'bootstrap-session-exec.exe --exec'
$plainRows = @(ConvertTo-BootstrapProgressRows $jobFixture 100 604 '' { throw 'non-supervisor queried' })
Require ($plainRows.Count -eq 2) 'non-supervisor helper job was queried'

$supervisor.CommandLine = 'bootstrap-session-exec.exe --supervise --spec fixture'
$state = [pscustomobject]@{Initialized=$false; Snapshots=0; Jobs=0}
$raceRows = @(Get-BootstrapProgressRows 100 604 '' {
    Require $state.Initialized 'interop initialization must precede process snapshot'
    $state.Snapshots++
    if ($state.Snapshots -eq 1) { @($jobFixture | Where-Object ProcessId -ne 603) }
    else { $jobFixture }
} { param($OwnerId)
    $state.Jobs++; @(602,603,604,605)
} { $state.Initialized = $true })
Require ($state.Snapshots -eq 2 -and $state.Jobs -eq 2) 'new member race did not refresh both authoritative inputs'
Require ($raceRows.Count -eq 4 -and @($raceRows -match '^603 602 603 ').Count -eq 1) 'new live member was dropped instead of observed'

$state = [pscustomobject]@{Snapshots=0; Jobs=0}
$retiredRows = @(Get-BootstrapProgressRows 100 604 '' {
    $state.Snapshots++; $jobFixture
} { param($OwnerId)
    $state.Jobs++
    if ($state.Jobs -eq 1) { @(602,603,604,605,9999) }
    else { @(602,603,604,605) }
} {})
Require ($state.Snapshots -eq 2 -and $state.Jobs -eq 2) 'retired member race did not refresh native snapshot and job ownership'
Require ($retiredRows.Count -eq 4) 'retired member race lost active owned processes'

$state = [pscustomobject]@{Snapshots=0; Jobs=0}
$partial = @(); $failed = $false
try {
    $partial = @(Get-BootstrapProgressRows 100 604 '' {
        $state.Snapshots++; $jobFixture
    } { param($OwnerId) $state.Jobs++; @(602,9999) } {})
} catch { $failed = $true }
Require ($failed -and $partial.Count -eq 0) 'persistent missing owned member escaped as a healthy partial tree'
Require ($state.Snapshots -eq 3 -and $state.Jobs -eq 3) 'missing-member resnapshot budget was not bounded to three attempts'

$state = [pscustomobject]@{Snapshots=0; Jobs=0}
$partial = @(); $failed = $false
try {
    $partial = @(Get-BootstrapProgressRows 100 604 '' {
        $state.Snapshots++; $jobFixture
    } { param($OwnerId) $state.Jobs++; throw 'job query unavailable' } {})
} catch { $failed = $true }
Require ($failed -and $partial.Count -eq 0 -and $state.Snapshots -eq 1 -and $state.Jobs -eq 1) 'non-race ownership failure was retried or published'

$metricFixture = @((Entry 100 1 'sh.exe' 0 1024), $supervisor,
    (Entry 602 777 'sh.exe' 0 1024))
$metricFixture[2].WorkingSetSize = $null
$state = [pscustomobject]@{Snapshots=0}
$partial = @(); $failed = $false
try {
    $partial = @(Get-BootstrapProgressRows 100 0 '' {
        $state.Snapshots++; $metricFixture
    } { @(602) } {})
} catch { $failed = $true }
Require ($failed -and $partial.Count -eq 0 -and $state.Snapshots -eq 1) 'missing metrics were downgraded to a retryable membership race'
Write-Output 'PASS windows process observer: 34 checks'
