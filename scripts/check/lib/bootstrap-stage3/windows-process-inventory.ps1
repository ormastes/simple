param(
    [Parameter(Mandatory = $true)][string]$OutputPath,
    [switch]$Worker
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

if ($Worker) {
    try {
        $processes = @(Get-CimInstance -ClassName Win32_Process -OperationTimeoutSec 10)
        if ($processes.Count -eq 0 -or $processes.Count -gt 16384) {
            throw 'Windows process inventory count outside bounded contract'
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
                    throw "Windows process command line unavailable for gate-sensitive PID $($process.ProcessId)"
                }
                $command = [string]$process.Name
            }
            $command = $command.Replace('\', '/').Replace('|', ' ').Replace("`r", ' ').Replace("`n", ' ')
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
        [System.IO.File]::WriteAllText($OutputPath, ($rows -join "`n") + "`n", [System.Text.UTF8Encoding]::new($false))
        exit 0
    } catch {
        [Console]::Error.WriteLine($_.Exception.Message)
        exit 1
    }
}

$child = $null
try {
    # A separate native query owns its output. Bound the complete CIM call,
    # serialization, and startup; stop only this query if its deadline expires.
    $executable = Join-Path $PSHOME 'powershell.exe'
    $arguments = @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass',
        '-File', ('"' + $PSCommandPath + '"'), '-OutputPath', ('"' + $OutputPath + '"'), '-Worker')
    $child = Start-Process -FilePath $executable -ArgumentList $arguments -PassThru -WindowStyle Hidden
    $null = $child.Handle
    if (-not $child.WaitForExit(15000)) {
        $child.Kill()
        $null = $child.WaitForExit(5000)
        throw 'Windows process inventory query exceeded 15 seconds'
    }
    $child.Refresh()
    if ($null -eq $child.ExitCode -or $child.ExitCode -ne 0) {
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
}
