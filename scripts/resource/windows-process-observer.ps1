param(
    [int]$RootPid = 0,
    [int]$ExcludePid = 0,
    [string]$Bridge = ''
)

# Native children of MSYS processes are absent from MSYS /proc. Emit the
# existing progress watcher's portable process-table format from one native
# snapshot. No process control or repository/cache writes occur here.
function ConvertTo-BootstrapProgressRows {
    param([object[]]$Processes, [int]$RootProcessId, [int]$ExcludedProcessId,
        [string]$BridgeParents = '')
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

if ($MyInvocation.InvocationName -ne '.') {
    $ErrorActionPreference = 'Stop'
    try {
        if ($RootPid -le 0) { throw 'positive RootPid required' }
        $snapshot = @(Get-CimInstance Win32_Process -OperationTimeoutSec 5)
        ConvertTo-BootstrapProgressRows $snapshot $RootPid $ExcludePid $Bridge
    } catch {
        [Console]::Error.WriteLine('windows-process-observer: ' + $_.Exception.Message)
        exit 1
    }
}
