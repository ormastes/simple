param(
    [int]$RootPid = 0,
    [int]$ExcludePid = 0,
    [string]$Bridge = '',
    [int]$IdentityPid = 0
)

# Native creation time is independent of the emulated /proc boot-time origin.
# Open twice so rapid PID reuse cannot combine two process generations.
function Get-BootstrapNativeProcessIdentity {
    param([int]$NativeProcessId)
    if ($NativeProcessId -le 0) { throw 'positive native process ID required' }
    $first = $null
    $second = $null
    try {
        $first = [Diagnostics.Process]::GetProcessById($NativeProcessId)
        $born = $first.StartTime.ToUniversalTime().ToFileTimeUtc()
        $second = [Diagnostics.Process]::GetProcessById($NativeProcessId)
        if ($first.HasExited -or $second.HasExited -or
            $second.StartTime.ToUniversalTime().ToFileTimeUtc() -ne $born) {
            throw 'native process generation changed'
        }
        return ('windows:{0}:{1}' -f $NativeProcessId,
            $born.ToString([Globalization.CultureInfo]::InvariantCulture))
    } finally {
        if ($null -ne $second) { $second.Dispose() }
        if ($null -ne $first) { $first.Dispose() }
    }
}

# Native children of MSYS processes are absent from MSYS /proc. Emit the
# existing progress watcher's portable process-table format from one native
# snapshot. No process control or repository/cache writes occur here.
function Initialize-BootstrapJobObserver {
    if (-not ('BootstrapJobObserver' -as [type])) {
        Add-Type -TypeDefinition @'
using System;
using System.ComponentModel;
using System.Runtime.InteropServices;
public static class BootstrapJobObserver {
    [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
    static extern IntPtr OpenJobObject(uint access, bool inherit, string name);
    [DllImport("kernel32.dll", SetLastError = true)]
    static extern bool QueryInformationJobObject(IntPtr job, int kind, IntPtr data, uint size, IntPtr returned);
    [DllImport("kernel32.dll")] static extern bool CloseHandle(IntPtr handle);
    public static int[] Members(int owner) {
        IntPtr job = OpenJobObject(4, false, "Local\\simple-bootstrap-session-" + owner);
        if (job == IntPtr.Zero) throw new Win32Exception(Marshal.GetLastWin32Error());
        try {
            for (int capacity = 16; capacity <= 65536; capacity *= 2) {
                int size = checked(8 + capacity * IntPtr.Size);
                IntPtr data = Marshal.AllocHGlobal(size);
                try {
                    if (!QueryInformationJobObject(job, 3, data, (uint)size, IntPtr.Zero)) {
                        int error = Marshal.GetLastWin32Error();
                        if (error == 234) continue;
                        throw new Win32Exception(error);
                    }
                    int assigned = Marshal.ReadInt32(data, 0), count = Marshal.ReadInt32(data, 4);
                    if (count < 0 || count > capacity || assigned != count)
                        throw new InvalidOperationException("incomplete session job snapshot");
                    int[] members = new int[count];
                    for (int i = 0; i < count; i++)
                        members[i] = checked((int)Marshal.ReadIntPtr(data, 8 + i * IntPtr.Size).ToInt64());
                    return members;
                } finally { Marshal.FreeHGlobal(data); }
            }
            throw new InvalidOperationException("session job snapshot exceeds member limit");
        } finally { CloseHandle(job); }
    }
}
'@
    }
}

function Get-BootstrapSessionJobMembers([int]$SessionOwnerId) {
    Initialize-BootstrapJobObserver
    return [BootstrapJobObserver]::Members($SessionOwnerId)
}

function ConvertTo-BootstrapProgressRows {
    param([object[]]$Processes, [int]$RootProcessId, [int]$ExcludedProcessId,
        [string]$BridgeParents = '',
        [scriptblock]$SessionMemberQuery = { param($OwnerId) Get-BootstrapSessionJobMembers $OwnerId })
    # MSYS exec leaves a child's native ParentProcessId on the exited fork
    # intermediate. The caller supplies "childWinPid:parentWinPid,..." from the
    # MSYS process table; those edges replace the stale native parent.
    $bridged = @{}
    if ($BridgeParents -ne '') {
        foreach ($pair in $BridgeParents.Split(',')) {
            if ($pair -notmatch '^(\d+):(\d+)$') { throw "malformed bridge edge: $pair" }
            $bridged[[int]$Matches[1]] = [int]$Matches[2]
        }
    }
    $byId = @{}
    $parentOf = @{}
    $children = @{}
    foreach ($entry in $Processes) {
        $key = [int]$entry.ProcessId
        $parentKey = [int]$entry.ParentProcessId
        if ($bridged.ContainsKey($key)) { $parentKey = $bridged[$key] }
        $parentOf[$key] = $parentKey
        $byId[$key] = $entry
        if (-not $children.ContainsKey($parentKey)) {
            $children[$parentKey] = [Collections.Generic.List[int]]::new()
        }
        $children[$parentKey].Add($key)
    }
    if (-not $byId.ContainsKey($RootProcessId)) { throw 'root absent from native snapshot' }
    $pending = [Collections.Generic.Queue[int]]::new()
    $seen = [Collections.Generic.HashSet[int]]::new()
    $pending.Enqueue($RootProcessId)
    $rows = [Collections.Generic.List[string]]::new()
    $culture = [Globalization.CultureInfo]::InvariantCulture
    while ($pending.Count -gt 0) {
        $current = $pending.Dequeue()
        if ($current -eq $ExcludedProcessId -or -not $seen.Add($current)) { continue }
        $entry = $byId[$current]
        # MSYS can orphan a compiler after exec even in its own process table.
        # The reachable supervisor's named Job Object remains the ownership
        # authority. Query only that job, never all system jobs or processes.
        if ($entry.Name -ieq 'bootstrap-session-exec.exe' -and
            $entry.CommandLine -match '(?:^|\s)--supervise(?:\s|$)') {
            $members = @(& $SessionMemberQuery $current)
            $memberSet = [Collections.Generic.HashSet[int]]::new()
            foreach ($member in $members) {
                $memberId = [int]$member
                if (-not $byId.ContainsKey($memberId)) {
                    $race = [InvalidOperationException]::new(
                        "session job member absent from native snapshot: $current/$memberId")
                    $race.Data['BootstrapSnapshotRace'] = $true
                    throw $race
                }
                if ([datetime]$byId[$memberId].CreationDate -lt [datetime]$entry.CreationDate) {
                    throw "session job member predates supervisor: $current/$memberId"
                }
                [void]$memberSet.Add($memberId)
            }
            foreach ($memberId in $memberSet) {
                if ($memberId -eq $current) { throw 'session supervisor included in its own job' }
                if (-not $memberSet.Contains([int]$parentOf[$memberId])) {
                    $parentOf[$memberId] = $current
                    $pending.Enqueue($memberId)
                }
            }
        }
        foreach ($field in @('CreationDate', 'KernelModeTime', 'UserModeTime', 'WorkingSetSize')) {
            if ($null -eq $entry.$field) { throw "native process metric unavailable: $current/$field" }
        }
        $born = ([datetime]$entry.CreationDate).ToUniversalTime()
        # Include subsecond birth identity to distinguish rapid PID reuse.
        $identity = $born.ToString('ddd MMM dd HH:mm:ss.fffffff yyyy', $culture)
        $seconds = ([decimal]$entry.KernelModeTime + [decimal]$entry.UserModeTime) / 10000000
        # WorkingSetSize is bytes. Do not use MSYS getconf PAGESIZE here:
        # its 64 KiB allocation granularity is not the 4 KiB unit exposed
        # by emulated /proc stat RSS (which inflated the old sampler 16x).
        $rss = [math]::Floor([double]$entry.WorkingSetSize / 1024)
        $name = ([string]$entry.Name) -replace '\s+', '_'
        if ($name -eq '') { $name = 'unknown' }
        # Windows has no POSIX pgid. The caller marks group metrics unknown.
        $rows.Add(('{0} {1} {0} {2} {3} {4} {5}' -f $current,
            $parentOf[$current], $rss.ToString('0', $culture), $identity,
            $seconds.ToString('0.0000000', $culture), $name))
        if ($children.ContainsKey($current)) {
            foreach ($child in $children[$current]) { $pending.Enqueue($child) }
        }
    }
    # Publish only a complete result. A failed required metric cannot look
    # like a smaller, idle process tree to the stall classifier.
    return $rows.ToArray()
}

function Get-BootstrapProgressRows {
    param([int]$RootProcessId, [int]$ExcludedProcessId,
        [string]$BridgeParents = '',
        [scriptblock]$SnapshotQuery = { @(Get-CimInstance Win32_Process -OperationTimeoutSec 5) },
        [scriptblock]$SessionMemberQuery = { param($OwnerId) Get-BootstrapSessionJobMembers $OwnerId },
        [scriptblock]$ObserverInitialize = { Initialize-BootstrapJobObserver },
        [ValidateRange(1, 3)][int]$MaxSnapshots = 3)
    # Add-Type can spawn csc inside the observed job. Initialize before the
    # process snapshot so our own interop compilation cannot create a member
    # between that snapshot and the authoritative job query.
    & $ObserverInitialize
    for ($attempt = 0; $attempt -lt $MaxSnapshots; $attempt++) {
        try {
            $snapshot = @(& $SnapshotQuery)
            return @(ConvertTo-BootstrapProgressRows $snapshot $RootProcessId $ExcludedProcessId $BridgeParents $SessionMemberQuery)
        } catch {
            # A child can start or exit between these two read-only APIs. Take
            # a fresh complete snapshot AND job query; never omit a missing
            # member from an owned job or treat Get-Process absence as proof.
            if (-not $_.Exception.Data.Contains('BootstrapSnapshotRace') -or
                $attempt + 1 -ge $MaxSnapshots) { throw }
        }
    }
}

if ($MyInvocation.InvocationName -ne '.') {
    $ErrorActionPreference = 'Stop'
    try {
        if ($IdentityPid -ne 0) {
            if ($RootPid -ne 0 -or $ExcludePid -ne 0 -or $Bridge -ne '') {
                throw 'identity mode excludes process-tree arguments'
            }
            Get-BootstrapNativeProcessIdentity $IdentityPid
            exit 0
        }
        if ($RootPid -le 0) { throw 'positive RootPid required' }
        Get-BootstrapProgressRows $RootPid $ExcludePid $Bridge
    } catch {
        [Console]::Error.WriteLine('windows-process-observer: ' + $_.Exception.Message)
        exit 1
    }
}
