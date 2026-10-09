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
Write-Output 'PASS windows process observer: 9 checks'
