param([Parameter(Mandatory=$true)][string]$OutputDirectory)
$ErrorActionPreference = 'Stop'
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$output = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $output) { throw 'use a fresh output directory' }
[IO.Directory]::CreateDirectory($output) | Out-Null
$fixture = Join-Path $output 'repo with spaces'
$release = Join-Path $fixture 'bin/release/x86_64-pc-windows-msvc/simple.exe'
$seed = Join-Path $fixture 'src/compiler_rust/target/bootstrap/simple.exe'
$wrapper = Join-Path $fixture 'bin/simple.cmd'
foreach ($path in @($release, $seed)) {
    [IO.Directory]::CreateDirectory((Split-Path $path)) | Out-Null
}
Copy-Item -LiteralPath (Join-Path $root 'bin/simple.cmd') -Destination $wrapper
$stub = Join-Path $output 'runtime-stub.exe'
Add-Type -OutputAssembly $stub -OutputType ConsoleApplication -TypeDefinition @'
using System;
class RuntimeStub {
    static int Main(string[] args) {
        Console.WriteLine("runtime=" + System.Reflection.Assembly.GetExecutingAssembly().Location);
        for (int i = 0; i < args.Length; i++) Console.WriteLine("arg" + i + "=" + args[i]);
        return 37;
    }
}
'@
Copy-Item -LiteralPath $stub -Destination $release
Copy-Item -LiteralPath $stub -Destination $seed

function Invoke-Fixture([string]$label, [string]$explicitBinary) {
    $start = [Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $env:ComSpec
    $start.Arguments = '/d /s /c ""' + $wrapper + '" LiNt "two words" --deny-all"'
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.EnvironmentVariables.Remove('SIMPLE_BINARY')
    if ($explicitBinary) { $start.EnvironmentVariables['SIMPLE_BINARY'] = $explicitBinary }
    $process = [Diagnostics.Process]::Start($start)
    try {
        $stdout = $process.StandardOutput.ReadToEndAsync()
        $stderr = $process.StandardError.ReadToEndAsync()
        if (!$process.WaitForExit(10000)) { $process.Kill(); throw "timeout: $label" }
        if (![Threading.Tasks.Task]::WaitAll([Threading.Tasks.Task[]]@($stdout,$stderr),5000)) {
            throw "output drain timeout: $label"
        }
        $text = $stdout.Result + $stderr.Result
        [IO.File]::WriteAllText((Join-Path $output "$label.log"), $text)
        return @{ Code = $process.ExitCode; Text = $text }
    } finally { $process.Dispose() }
}
function Assert-Route($result, [string]$runtime) {
    if ($result.Code -ne 37) { throw "runtime exit was not propagated: $($result.Code)" }
    foreach ($line in @("runtime=$runtime", 'arg0=LiNt', 'arg1=two words', 'arg2=--deny-all')) {
        if (!($result.Text -split '\r?\n').Contains($line)) { throw "missing exact output: $line" }
    }
}
Assert-Route (Invoke-Fixture 'release-precedes-seed' '') $release
Assert-Route (Invoke-Fixture 'explicit-binary-precedes-release' $seed) $seed
[IO.File]::WriteAllBytes($release, [byte[]]@())
$empty = Invoke-Fixture 'empty-release-rejects-seed' ''
if ($empty.Code -ne 1 -or $empty.Text -notmatch 'lint requires a deployed self-hosted' -or $empty.Text -match 'runtime=') {
    throw 'empty release did not fail closed'
}
Remove-Item -LiteralPath $release
$missing = Invoke-Fixture 'missing-release-rejects-seed' ''
if ($missing.Code -ne 1 -or $missing.Text -notmatch 'lint requires a deployed self-hosted' -or $missing.Text -match 'runtime=') {
    throw 'missing release did not fail closed'
}
Assert-Route (Invoke-Fixture 'explicit-diagnostic-without-release' $seed) $seed
Write-Output 'PASS: five cmd.exe lint routing cases; argument and exit propagation verified'
