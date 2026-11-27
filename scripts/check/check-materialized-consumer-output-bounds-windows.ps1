$ErrorActionPreference = 'Stop'
$owner = Join-Path $PSScriptRoot 'lib/bootstrap-stage3/authority.shs'
$source = [IO.File]::ReadAllText((Resolve-Path $owner))
$native = [regex]::Match($source, "(?s)bootstrap_stage3_materialized_native_source\(\).*?Add-Type -TypeDefinition @'\r?\n(.*?)\r?\n'@")
if (!$native.Success) { throw 'production materialized consumer source missing' }
Add-Type -TypeDefinition $native.Groups[1].Value
$type = [Stage3MaterializedConsumer]
$flags = [Reflection.BindingFlags]'NonPublic,Static'
$fixture = Join-Path $env:TEMP ('consumer-output-bounds-' + [guid]::NewGuid().ToString('N'))
[IO.Directory]::CreateDirectory($fixture) | Out-Null
$priorGit = $env:STAGE3_GIT
$priorMode = $env:CONSUMER_FIXTURE_MODE
try {
    $fake = Join-Path $fixture 'fixture-git.exe'
    Add-Type -TypeDefinition @'
using System;
class ConsumerFixtureGit {
    static int Main() {
        string mode = Environment.GetEnvironmentVariable("CONSUMER_FIXTURE_MODE");
        if (mode == "failure") { Console.Error.WriteLine("fixture real command failure"); return 42; }
        if (mode == "tree") {
            string padding = new string('p', 96);
            for (int i=0; i<130000; i++) Console.Write("100644 blob 1111111111111111111111111111111111111111\t" + padding + i.ToString("D8") + "\0");
            return 0;
        }
        using (var output = Console.OpenStandardOutput()) {
            byte[] block = new byte[65536];
            long remaining = mode == "tree-overflow" ? 64L*1024*1024+1 : 17L*1024*1024;
            while (remaining > 0) { int n = (int)Math.Min(block.Length, remaining); output.Write(block, 0, n); remaining -= n; }
        }
        return 0;
    }
}
'@ -OutputAssembly $fake -OutputType ConsoleApplication
    $env:STAGE3_GIT = $fake
    $env:CONSUMER_FIXTURE_MODE = 'tree'
    $gitlinks = [Collections.Generic.Dictionary[string,string]]::new()
    $links = $type.GetMethod('HeadLinks', $flags).Invoke($null, [object[]]@([string]$fixture, [string]'HEAD', $gitlinks))
    $entries = $type.GetField('entries', $flags).GetValue($null)
    if ($entries -ne 130000 -or $links.Count -ne 0 -or $gitlinks.Count -ne 0) { throw 'large real inventory parsing failed' }
    # Each row is 158 bytes: the valid positive inventory is over 16 MiB.
    if (130000 * 158 -le 16*1024*1024) { throw 'fixture is too small to fence the regression' }
    function Expect-CommandFailure($method, $mode, $expected) {
        $env:CONSUMER_FIXTURE_MODE = $mode
        try {
            $null = $type.GetMethod($method, $flags).Invoke($null, [object[]]@([string]$fixture, [string[]]@('ls-tree')))
        } catch {
            $failure = $_.Exception.GetBaseException().Message
            if (!$failure.StartsWith($expected, [StringComparison]::Ordinal)) { throw "expected $expected; got $failure" }
            if ($type.GetField('ActiveChild', $flags).GetValue($null)) { throw 'command failure retained its active child' }
            return
        }
        throw "unexpected success: $method $mode"
    }
    Expect-CommandFailure 'Git' 'ordinary-overflow' 'bound.command-output max=16777216'
    Expect-CommandFailure 'GitTree' 'tree-overflow' 'bound.command-output max=67108864'
    Expect-CommandFailure 'GitTree' 'failure' 'command.failed:42'
    Write-Output 'PASS: valid >16MiB inventory, ordinary bound, tree bound and real exit42 failure'
} finally {
    $env:STAGE3_GIT = $priorGit
    $env:CONSUMER_FIXTURE_MODE = $priorMode
    $tempRoot = [IO.Path]::GetFullPath($env:TEMP).TrimEnd('\') + '\'
    if (!$fixture.StartsWith($tempRoot, [StringComparison]::OrdinalIgnoreCase)) { throw 'unsafe fixture cleanup path' }
    Remove-Item -LiteralPath $fixture -Recurse -Force
}
