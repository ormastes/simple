param(
    [Parameter(Mandatory = $true)][string]$OutputPath,
    [switch]$Worker
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

function Get-MsysParentBridge {
    # MSYS exec can leave native PPID pointing to an exited fork intermediate.
    # Query the live POSIX table, never accept an exclusion list from argv/env.
    $bridge = @{}
    $psCommand = Get-Command ps.exe -CommandType Application -ErrorAction SilentlyContinue | Select-Object -First 1
    if ($null -eq $psCommand) { return $bridge }
    $start = [System.Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $psCommand.Source
    $start.Arguments = '-l'
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $query = [System.Diagnostics.Process]::new()
    $query.StartInfo = $start
    try {
        if (-not $query.Start()) { throw 'MSYS ancestry query did not start' }
        # Drain both pipes asynchronously to avoid deadlock. The query has a
        # time bound; the size check below is post-capture validation, not a
        # hard bound on stream-buffer memory (stderr is drained and discarded).
        $stdout = $query.StandardOutput.ReadToEndAsync()
        $stderr = $query.StandardError.ReadToEndAsync()
        if (-not $query.WaitForExit(10000)) {
            $query.Kill()
            $null = $query.WaitForExit(5000)
            throw 'MSYS ancestry query exceeded 10 seconds'
        }
        $table = $stdout.GetAwaiter().GetResult()
        $null = $stderr.GetAwaiter().GetResult()
        if ($query.ExitCode -ne 0 -or $table.Length -gt 16777216) {
            throw 'MSYS ancestry query failed or exceeded size limit'
        }
        $lines = @($table -split '\r?\n' | Where-Object { $_.Trim().Length -gt 0 })
        if ($lines.Count -eq 0 -or $lines[0] -notmatch '^\s*PID\s+PPID\s+PGID\s+WINPID\s') {
            throw 'MSYS ancestry table has an unknown schema'
        }
        $rows = @{}
        $nativeIds = [System.Collections.Generic.HashSet[uint32]]::new()
        foreach ($line in ($lines | Select-Object -Skip 1)) {
            if ($line -notmatch '^\s*(?:[A-Z]\s+)?(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s') {
                throw 'MSYS ancestry table contains a malformed row'
            }
            $posix = [uint32]$Matches[1]
            $parent = [uint32]$Matches[2]
            $native = [uint32]$Matches[4]
            if ($rows.ContainsKey($posix) -or -not $nativeIds.Add($native) -or $rows.Count -ge 16384) {
                throw 'MSYS ancestry table contains duplicate or excess rows'
            }
            $rows[$posix] = @{ Parent = $parent; Native = $native }
        }
        foreach ($row in $rows.Values) {
            if ($rows.ContainsKey($row.Parent)) {
                $bridge[$row.Native] = $rows[$row.Parent].Native
            }
        }
        return $bridge
    } finally { $query.Dispose() }
}

if ($Worker) {
    try {
        $processes = @(Get-CimInstance -ClassName Win32_Process -OperationTimeoutSec 30)
        if ($processes.Count -eq 0 -or $processes.Count -gt 16384) {
            throw 'Windows process inventory count outside bounded contract'
        }
        # Identify this query's proven parent chain in the same native snapshot.
        # PowerShell, Git Bash and sh can each carry the same resume argv; they
        # are wrappers of this admission, not independent bootstrap jobs.
        $byPid = @{}
        foreach ($process in $processes) {
            if ($null -eq $process.ProcessId -or $null -eq $process.ParentProcessId) {
                throw 'Windows process inventory has an incomplete PID record'
            }
            $key = [uint32]$process.ProcessId
            if ($byPid.ContainsKey($key)) { throw 'Windows process inventory has duplicate PID records' }
            $byPid[$key] = $process
        }
        $msysParents = Get-MsysParentBridge
        $ancestors = [System.Collections.Generic.HashSet[uint32]]::new()
        $pending = [System.Collections.Generic.Stack[uint32]]::new()
        $pending.Push([uint32]$PID)
        while ($pending.Count -gt 0) {
            $cursor = $pending.Pop()
            if (-not $byPid.ContainsKey($cursor) -or -not $ancestors.Add($cursor)) { continue }
            if ($ancestors.Count -gt 256) { throw 'Windows process inventory ancestry is too deep' }
            $child = $byPid[$cursor]
            # Retain both edges: the native waiting wrapper and its MSYS exec
            # successor can coexist. Replacing PPID with the logical edge
            # would incorrectly leave the waiting wrapper classified as busy.
            $parents = @([uint32]$child.ParentProcessId)
            if ($msysParents.ContainsKey($cursor)) {
                $parents += [uint32]$msysParents[$cursor]
            }
            foreach ($next in $parents) {
                if ($next -eq 0 -or -not $byPid.ContainsKey($next)) { continue }
                $parent = $byPid[$next]
                # A reused parent PID must never excuse another process. Both
                # native and MSYS edges require a strictly older live parent.
                if ($null -eq $child.CreationDate -or $null -eq $parent.CreationDate -or
                    $parent.CreationDate -ge $child.CreationDate) { continue }
                $pending.Push($next)
            }
        }
        $rows = [System.Collections.Generic.List[string]]::new()
        $size = 0
        foreach ($process in ($processes | Sort-Object ProcessId)) {
            if ($null -eq $process.ProcessId -or $null -eq $process.ParentProcessId -or
                $null -eq $process.WorkingSetSize -or [string]::IsNullOrWhiteSpace($process.Name)) {
                throw 'Windows process inventory has an incomplete numeric/image record'
            }
            $command = [string]$process.CommandLine
            if ([string]::IsNullOrWhiteSpace($command)) {
                # Protected system/service processes commonly have no command line.
                # An unreadable compiler/interpreter could hide a heavy invocation.
                if ($process.Name -match '^(?i:simple|bash|sh|cmd|powershell|pwsh)\.exe$' -or
                    $process.Name -like 'qemu-system-*') {
                    # CIM can return a snapshot row after its process has
                    # already exited, with its command line consequently gone.
                    # Only omit it after a fresh bounded query proves no such
                    # PID exists. A live/reused PID or query error remains a
                    # refusal; neither can be classified from a stale row.
                    $current = @(Get-CimInstance -ClassName Win32_Process -Filter ("ProcessId = {0}" -f [uint32]$process.ProcessId) -OperationTimeoutSec 5)
                    if ($current.Count -eq 0) { continue }
                    throw "Windows process command line unavailable for gate-sensitive PID $($process.ProcessId)"
                }
                $command = [string]$process.Name
            }
            $command = $command.Replace('\', '/').Replace('|', ' ').Replace("`r", ' ').Replace("`n", ' ')
            if ($ancestors.Contains([uint32]$process.ProcessId) -and
                $process.Name -match '^(?i:bash|sh|cmd|powershell|pwsh|perl|timeout)\.exe$' -and
                $command.Contains('scripts/bootstrap/bootstrap-from-scratch.sh')) {
                continue
            }
            if ($process.Name -ieq 'simple.exe') {
                # Preserve the existing classifier's /simple argv identity. Use
                # the real image name, not an executable guessed from argv[0].
                $command = [regex]::Replace($command, '^("[^"]*"|\S+)\s*', '/simple ')
                $command = $command.TrimEnd()
            }
            $rss = [uint64][Math]::Floor([decimal]$process.WorkingSetSize / 1024)
            $row = '{0}|{1}|{2}|{3}' -f [uint32]$process.ProcessId, [uint32]$process.ParentProcessId, $rss, $command
            $size += [System.Text.Encoding]::UTF8.GetByteCount($row) + 1
            if ($size -gt 16777216) { throw 'Windows process inventory exceeds 16 MiB; refusing partial inventory' }
            $rows.Add($row)
        }
        if ($rows.Count -eq 0) { throw 'Windows process inventory has no live rows after revalidation' }
        [System.IO.File]::WriteAllText($OutputPath, ($rows -join "`n") + "`n", [System.Text.UTF8Encoding]::new($false))
        exit 0
    } catch {
        [Console]::Error.WriteLine($_.Exception.Message)
        exit 1
    }
}

$child = $null
$workerErrorPath = $null
try {
    # A separate native query owns its output. Bound the complete CIM call,
    # serialization, and startup; stop only this query if its deadline expires.
    $executable = Join-Path $PSHOME 'powershell.exe'
    $arguments = @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass',
        '-File', ('"' + $PSCommandPath + '"'), '-OutputPath', ('"' + $OutputPath + '"'), '-Worker')
    $workerErrorPath = [System.IO.Path]::GetTempFileName()
    $child = Start-Process -FilePath $executable -ArgumentList $arguments -PassThru -WindowStyle Hidden -RedirectStandardError $workerErrorPath
    $null = $child.Handle
    if (-not $child.WaitForExit(40000)) {
        $child.Kill()
        $null = $child.WaitForExit(5000)
        throw 'Windows process inventory query exceeded 40 seconds'
    }
    $child.Refresh()
    if ($null -eq $child.ExitCode -or $child.ExitCode -ne 0) {
        # The hidden worker's stderr is otherwise lost, leaving callers with no
        # evidence of whether CIM, a record, or the bounded contract failed.
        # Read only a bounded prefix; never accept an incomplete inventory.
        $errorStream = [System.IO.File]::OpenRead($workerErrorPath)
        try {
            $errorBytes = New-Object byte[] 4096
            $errorCount = $errorStream.Read($errorBytes, 0, $errorBytes.Length)
            $workerError = [System.Text.Encoding]::UTF8.GetString($errorBytes, 0, $errorCount).Trim()
        } finally { $errorStream.Dispose() }
        if ($workerError) { throw "Windows process inventory query failed: $workerError" }
        throw 'Windows process inventory query failed'
    }
    if (-not [System.IO.File]::Exists($OutputPath) -or (Get-Item -LiteralPath $OutputPath).Length -eq 0) {
        throw 'Windows process inventory query returned no rows'
    }
    exit 0
} catch {
    [Console]::Error.WriteLine($_.Exception.Message)
    exit 1
} finally {
    if ($null -ne $child) { $child.Dispose() }
    if ($null -ne $workerErrorPath) { Remove-Item -LiteralPath $workerErrorPath -Force -ErrorAction SilentlyContinue }
}
