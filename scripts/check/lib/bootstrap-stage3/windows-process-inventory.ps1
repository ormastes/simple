param(
    [Parameter(Mandatory = $true)][string]$OutputPath,
    [switch]$Worker
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

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
        $ancestors = [System.Collections.Generic.HashSet[uint32]]::new()
        $cursor = [uint32]$PID
        while ($byPid.ContainsKey($cursor)) {
            if (-not $ancestors.Add($cursor) -or $ancestors.Count -gt 256) {
                throw 'Windows process inventory ancestry is cyclic or too deep'
            }
            $child = $byPid[$cursor]
            $next = [uint32]$child.ParentProcessId
            if ($next -eq 0 -or -not $byPid.ContainsKey($next)) { break }
            $parent = $byPid[$next]
            # A reused parent PID must never excuse another process. Stop the
            # proven chain when either creation time is unavailable or the
            # recorded parent is not strictly older than its child.
            if ($null -eq $child.CreationDate -or $null -eq $parent.CreationDate -or
                $parent.CreationDate -ge $child.CreationDate) { break }
            $cursor = $next
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
