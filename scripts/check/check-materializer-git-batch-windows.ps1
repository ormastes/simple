$ErrorActionPreference = 'Stop'
$producer = Join-Path $PSScriptRoot '../setup/materialize-symlinks-windows.shs'
$source = [IO.File]::ReadAllText((Resolve-Path $producer))
$match = [regex]::Match($source, "(?s)<<'POWERSHELL'\r?\n(.*?)\r?\nPOWERSHELL")
if (!$match.Success) { throw 'cannot extract materializer helper' }
$fixture = Join-Path $env:TEMP ('materializer-batch-test-' + [guid]::NewGuid().ToString('N'))
[IO.Directory]::CreateDirectory($fixture) | Out-Null
try {
    $api = Join-Path $fixture 'api.ps1'
    [IO.File]::WriteAllText($api, $match.Groups[1].Value, [Text.UTF8Encoding]::new($false))
    & git -C $fixture init -q
    if ($LASTEXITCODE) { throw 'git init failed' }
    $blob = Join-Path $fixture 'target'
    [IO.File]::WriteAllText($blob, 'target', [Text.UTF8Encoding]::new($false))
    $oid = (& git -C $fixture hash-object -w $blob).Trim()
    if ($LASTEXITCODE) { throw 'git hash-object failed' }
    $blob2 = Join-Path $fixture 'target2'
    [IO.File]::WriteAllText($blob2, 'second-target', [Text.UTF8Encoding]::new($false))
    $oid2 = (& git -C $fixture hash-object -w $blob2).Trim()
    if ($LASTEXITCODE -or $oid2 -eq $oid) { throw 'second git hash-object failed' }
    $tree = Join-Path $fixture 'tree'
    [IO.File]::WriteAllText($tree, "100644 $oid target`0", [Text.UTF8Encoding]::new($false))
    $policy = Join-Path $fixture 'policy'
    [IO.File]::WriteAllBytes($policy, [byte[]]::new(0))
    $output = Join-Path $fixture 'blob'
    $start = [Diagnostics.ProcessStartInfo]::new('powershell.exe', "-NoProfile -NonInteractive -ExecutionPolicy Bypass -File `"$api`"")
    $start.WorkingDirectory = $fixture
    $start.UseShellExecute = $false
    $start.RedirectStandardInput = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.EnvironmentVariables['MATERIALIZER_ROOT'] = $fixture
    $start.EnvironmentVariables['MATERIALIZER_TREE'] = $tree
    $start.EnvironmentVariables['MATERIALIZER_POLICY'] = $policy
    $start.EnvironmentVariables['MATERIALIZER_POLICY_SHA256'] = 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
    $start.EnvironmentVariables['MATERIALIZER_BLOB'] = $output
    $process = [Diagnostics.Process]::Start($start)
    try {
        function Read-Response($expected) {
            $line = $process.StandardOutput.ReadLineAsync()
            if (!$line.Wait(30000)) { throw "materializer response timed out: $expected" }
            if ($line.Result -ne $expected) { throw "expected $expected; got $($line.Result)" }
        }
        Read-Response 'READY'
        foreach ($request in @(@($oid, 'target'), @($oid2, 'second-target'))) {
            $process.StandardInput.WriteLine("gitblob`t$($request[0])`t")
            $process.StandardInput.Flush()
            Read-Response 'OK'
            if ([IO.File]::ReadAllText($output) -ne $request[1]) { throw "incorrect blob for $($request[0])" }
        }
        $process.StandardInput.Close()
        if (!$process.WaitForExit(30000)) { throw 'helper did not exit cleanly: timeout' }
        if ($process.ExitCode) { throw "helper did not exit cleanly: $($process.StandardError.ReadToEnd())" }
    } finally {
        if (!$process.HasExited) { $process.Kill() }
        $process.Dispose()
    }
    $fakeGit = Join-Path $fixture 'git.exe'
    Add-Type -TypeDefinition 'using System; class DeadGit { static int Main() { Console.Error.WriteLine("simulated-batch-death"); return 42; } }' -OutputAssembly $fakeGit -OutputType ConsoleApplication
    $start.EnvironmentVariables['PATH'] = $fixture + ';' + $start.EnvironmentVariables['PATH']
    $process = [Diagnostics.Process]::Start($start)
    try {
        Read-Response 'READY'
        $process.StandardInput.WriteLine("gitblob`t$oid`t")
        $process.StandardInput.Flush()
        if (!$process.WaitForExit(30000)) { throw 'dead Git helper timed out' }
        $failure = $process.StandardError.ReadToEnd()
        if ($process.ExitCode -eq 0 -or $failure -notmatch 'git\.batch-eof:exit=42:stderr=simulated-batch-death') {
            throw "missing bounded Git exit diagnostic: $failure"
        }
    } finally {
        if (!$process.HasExited) { $process.Kill() }
        $process.Dispose()
    }
    Write-Output 'materializer git batch: PASS'
} finally {
    $tempRoot = [IO.Path]::GetFullPath($env:TEMP).TrimEnd('\') + '\'
    if (!$fixture.StartsWith($tempRoot, [StringComparison]::OrdinalIgnoreCase)) { throw 'unsafe fixture cleanup path' }
    Remove-Item -LiteralPath $fixture -Recurse -Force
}
