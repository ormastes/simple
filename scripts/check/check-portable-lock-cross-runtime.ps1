param(
    [Parameter(Mandatory=$true)][string]$Evidence,
    [string]$GitBash = 'C:/dev/tool/Git/bin/bash.exe',
    [string]$MsysBash = 'C:/dev/tool/msys2/usr/bin/bash.exe',
    [string]$HelperPath = '',
    [string]$LibraryPath = '',
    [ValidateSet('all', 'observer')][string]$CheckGroup = 'all'
)
$ErrorActionPreference = 'Stop'
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
if ($HelperPath -eq '') { $HelperPath = Join-Path $repo 'scripts/check/lib/portable-hardlink-lock.pl' }
if ($LibraryPath -eq '') { $LibraryPath = Join-Path $repo 'scripts/check/lib/portable-process-lock.shs' }
foreach ($required in @($GitBash, $MsysBash, $HelperPath, $LibraryPath)) {
    if (-not (Test-Path -LiteralPath $required -PathType Leaf)) { throw "Missing prerequisite: $required" }
}
$Evidence = [IO.Path]::GetFullPath($Evidence)
if (Test-Path -LiteralPath $Evidence) { throw 'Fresh private evidence directory required' }
New-Item -ItemType Directory -Path $Evidence | Out-Null
$utf8 = New-Object Text.UTF8Encoding($false)
$script:checks = [Collections.Generic.List[string]]::new()
$script:failures = 0

function Write-Fixture([string]$Name, [string]$Text) {
    $path = Join-Path $Evidence $Name
    if ($Name.EndsWith('.shs')) { $Text = "PATH=/usr/bin:/bin:`$PATH; export PATH`n" + $Text }
    [IO.File]::WriteAllText($path, $Text.Replace("`r`n", "`n") + "`n", $utf8)
    return $path.Replace('\', '/')
}

function Start-FixtureShell([string]$Shell, [string[]]$Arguments, [string]$Name) {
    $stdout = Join-Path $Evidence ($Name + '.stdout')
    $stderr = Join-Path $Evidence ($Name + '.stderr')
    # Values are positional script arguments, never interpolated shell code.
    $quoted = foreach ($argument in (@('--noprofile', '--norc') + $Arguments)) {
        if ($argument.Contains('"') -or $argument.EndsWith('\')) { throw 'Unsupported fixture argument quoting' }
        '"' + $argument + '"'
    }
    $process = Start-Process -FilePath $Shell -ArgumentList ($quoted -join ' ') -WindowStyle Hidden -PassThru -RedirectStandardOutput $stdout -RedirectStandardError $stderr
    $null = $process.Handle
    return @{ Process = $process; Stdout = $stdout; Stderr = $stderr }
}

function Run-FixtureShell([string]$Shell, [string[]]$Arguments, [string]$Name) {
    $job = Start-FixtureShell $Shell $Arguments $Name
    if (-not $job.Process.WaitForExit(25000)) {
        $job.Process.Kill()
        throw "Private fixture timed out: $Name"
    }
    # A retained process handle makes ExitCode available after WaitForExit.
    return @{ Code = $job.Process.ExitCode; Text = ([IO.File]::ReadAllText($job.Stdout)).Trim() }
}

function Check-Value([string]$Name, $Observed, $Expected) {
    $status = 'PASS'
    if ("$Observed" -cne "$Expected") { $status = 'FAIL'; $script:failures++ }
    $row = "$status $Name expected=$Expected observed=$Observed"
    $script:checks.Add($row)
    Write-Output $row
}

$ownerScript = Write-Fixture 'owner.shs' @'
set -eu
root=$1
PORTABLE_LOCK_ATOMIC_HELPER_PATH=$2
export PORTABLE_LOCK_ATOMIC_HELPER_PATH
. "$3"
trap 'portable_lock_release_all' EXIT
portable_lock_acquire "$root/lock" fixture 0
cp "$PORTABLE_LOCK_HANDLE" "$root/claim.snapshot"
printf 'ready\n' > "$root/ready"
while [ ! -e "$root/stop" ]; do sleep 0.1; done
'@
$queryScript = Write-Fixture 'query.shs' @'
set -eu
helper=$1
owner=$2
start=$3
group=$4
if [ "${5:-}" = collision ]; then owner=$$; group=$$; fi
if [ -n "${6:-}" ]; then PATH="$(cygpath -u "$6"):$PATH"; export PATH; fi
/usr/bin/perl "$helper" claim-state "$owner" "$start" "$group"
'@
$identityScript = Write-Fixture 'identity.shs' @'
set -eu
/usr/bin/perl "$1" identity "$2"
'@
$contenderScript = Write-Fixture 'contender.shs' @'
set -eu
PORTABLE_LOCK_ATOMIC_HELPER_PATH=$1
export PORTABLE_LOCK_ATOMIC_HELPER_PATH
. "$2"
portable_lock_acquire "$3/lock" fixture 0
'@
$chmodScript = Write-Fixture 'chmod.shs' @'
set -eu
chmod u+x "$1"
'@
$reaperScript = Write-Fixture 'reaper.shs' @'
set -eu
. "$1"
PORTABLE_LOCK_OWNER_PGID=999999999
# Simulated local PID/group collision: kill is a recording function, never
# the real process-control builtin. sleep is also inert on the old code path.
portable_lock_pid_alive() { return 1; }
sleep() { :; }
trace=$3
# Functions have their own positional parameters: close over the trace path.
kill() { printf '%s\n' "$*" >> "$trace"; return 0; }
if portable_lock_reap_orphans 424242424 424242424 "$2"; then
    printf 'reaped\n'
else
    printf 'held\n'
fi
'@
New-Item -ItemType Directory -Path (Join-Path $Evidence 'lock') | Out-Null
$helperArg = [IO.Path]::GetFullPath($HelperPath).Replace('\', '/')
$libraryArg = [IO.Path]::GetFullPath($LibraryPath).Replace('\', '/')
$evidenceArg = $Evidence.Replace('\', '/')
$owner = $null
try {
    $owner = Start-FixtureShell $GitBash @($ownerScript, $evidenceArg, $helperArg, $libraryArg) 'owner'
    $ready = Join-Path $Evidence 'ready'
    $deadline = [DateTime]::UtcNow.AddSeconds(20)
    while (-not (Test-Path -LiteralPath $ready)) {
        if ($owner.Process.HasExited) { throw "Private owner exited: $([IO.File]::ReadAllText($owner.Stderr))" }
        if ([DateTime]::UtcNow -gt $deadline) { throw 'Private owner did not publish its claim' }
        Start-Sleep -Milliseconds 50
    }
    $fields = @{}
    foreach ($line in [IO.File]::ReadAllLines((Join-Path $Evidence 'claim.snapshot'))) {
        $pair = $line.Split('=', 2)
        if ($pair.Length -eq 2) { $fields[$pair[0]] = $pair[1] }
    }
    $ownerId = $fields.owner_pid
    $start = $fields.owner_start_hex
    $group = $fields.owner_pgid
    $bytes = for ($index = 0; $index -lt $start.Length; $index += 2) { [Convert]::ToByte($start.Substring($index, 2), 16) }
    $token = [Text.Encoding]::ASCII.GetString([byte[]]$bytes)
    if ($token -notmatch '^windows:([1-9][0-9]*):([1-9][0-9]*)$') { throw 'Private owner did not produce a native birth token' }
    $nativeOwner = [int]$Matches[1]
    $nativeBirth = [long]$Matches[2]
    $wrongToken = 'windows:{0}:{1}' -f $nativeOwner, ($nativeBirth + 1)
    $wrongStart = ([BitConverter]::ToString([Text.Encoding]::ASCII.GetBytes($wrongToken))).Replace('-', '').ToLowerInvariant()
    $stable = Join-Path $Evidence 'lock/.fixture.lock'
    $claimHash = (Get-FileHash -LiteralPath $stable -Algorithm SHA256).Hash
    $before = Run-FixtureShell $MsysBash @($identityScript, $helperArg, $stable.Replace('\', '/')) 'identity-before'
    $liveNative = Get-Process -Id $nativeOwner
    if ($CheckGroup -eq 'all') {
    Check-Value 'native owner birth matches claim' $liveNative.StartTime.ToUniversalTime().ToFileTimeUtc() $nativeBirth
    foreach ($runtime in @(@('same-runtime', $GitBash), @('cross-runtime', $MsysBash))) {
        $observed = Run-FixtureShell $runtime[1] @($queryScript, $helperArg, $ownerId, $start, $group) $runtime[0]
        Check-Value ($runtime[0] + ' query exit') $observed.Code 0
        Check-Value ($runtime[0] + ' live owner') $observed.Text 'live'
    }
    $collision = Run-FixtureShell $MsysBash @($queryScript, $helperArg, $ownerId, $start, $group, 'collision') 'collision'
    Check-Value 'local PID collision preserves foreign live owner' $collision.Text 'live'
    $wrong = Run-FixtureShell $MsysBash @($queryScript, $helperArg, $ownerId, $wrongStart, $group) 'wrong-birth'
    Check-Value 'simulated reused native PID token stays held' $wrong.Text 'unknown'
    $malformed = '77696e646f77733a696e76616c6964'
    $bad = Run-FixtureShell $MsysBash @($queryScript, $helperArg, $ownerId, $malformed, $group) 'malformed-token'
    Check-Value 'malformed native token stays held' $bad.Text 'unknown'
    $odd = Run-FixtureShell $MsysBash @($queryScript, $helperArg, $ownerId, ($start + '0'), $group) 'odd-hex'
    Check-Value 'odd-length hex is rejected' $odd.Code 2
    $contender = Run-FixtureShell $MsysBash @($contenderScript, $helperArg, $libraryArg, $evidenceArg) 'contender'
    Check-Value 'cross-runtime contender cannot acquire live owner lock' $contender.Code 75
    }
    $mockBin = New-Item -ItemType Directory -Path (Join-Path $Evidence 'mock')
    foreach ($mode in @('nonzero', 'malformed', 'timeout')) {
        $mockBody = switch ($mode) {
            'nonzero' { 'exit 1;' }
            'malformed' { 'print "invalid native identity\n";' }
            'timeout' { 'sleep 20;' }
        }
        $mock = Write-Fixture 'mock/powershell.exe' ("#!/usr/bin/perl`n" + $mockBody)
        $modeChmod = Run-FixtureShell $MsysBash @($chmodScript, $mock) ($mode + '-chmod')
        if ($modeChmod.Code -ne 0) { throw 'Mock observer chmod failed' }
        $failedObserver = Run-FixtureShell $MsysBash @($queryScript, $helperArg, $ownerId, $start, $group, 'normal', $mockBin.FullName.Replace('\', '/')) ('observer-' + $mode)
        Check-Value ($mode + ' observer failure keeps claim held') $failedObserver.Text 'unknown'
        Check-Value ($mode + ' observer failure query exit') $failedObserver.Code 0
    }
    if ($CheckGroup -eq 'all') {
    $trace = (Join-Path $Evidence 'signals.trace').Replace('\', '/')
    $reaped = Run-FixtureShell $MsysBash @($reaperScript, $libraryArg, $start, $trace) 'reaper'
    Check-Value 'native-token orphan reaper refuses local group' $reaped.Text 'held'
    Check-Value 'native-token orphan reaper made no kill calls' (Test-Path -LiteralPath $trace) $false
    $after = Run-FixtureShell $MsysBash @($identityScript, $helperArg, $stable.Replace('\', '/')) 'identity-after'
    Check-Value 'private claim hardlink identity unchanged' $after.Text $before.Text
    Check-Value 'private claim bytes unchanged' (Get-FileHash -LiteralPath $stable -Algorithm SHA256).Hash $claimHash
    $nativeAgain = Get-Process -Id $nativeOwner
    Check-Value 'private owner still same live generation' $nativeAgain.StartTime.ToUniversalTime().ToFileTimeUtc() $nativeBirth
    }
    [IO.File]::WriteAllText((Join-Path $Evidence 'stop'), 'stop', $utf8)
    if (-not $owner.Process.WaitForExit(10000)) { throw 'Private owner did not finish' }
    if ($CheckGroup -eq 'all') {
    Check-Value 'private owner releases its own claim' $owner.Process.ExitCode 0
    $dead = Run-FixtureShell $MsysBash @($queryScript, $helperArg, $ownerId, $start, $group) 'dead-native'
    Check-Value 'absent native owner cannot disprove foreign descendants' $dead.Text 'unknown'
    }
} finally {
    if ($null -ne $owner -and -not $owner.Process.HasExited) {
        [IO.File]::WriteAllText((Join-Path $Evidence 'stop'), 'stop', $utf8)
        if (-not $owner.Process.WaitForExit(10000)) { $owner.Process.Kill() }
    }
    [IO.File]::WriteAllLines((Join-Path $Evidence 'results.txt'), $script:checks, $utf8)
}
if ($script:failures -ne 0) { throw "$script:failures private lock regression checks failed" }
Write-Output ("PASS: {0} private lock checks; host harness only, no compiler admission" -f $script:checks.Count)
