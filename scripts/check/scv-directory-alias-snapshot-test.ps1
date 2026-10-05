param([Parameter(Mandatory=$true)][string]$FixtureBinary)
$ErrorActionPreference = 'Stop'
$binary = (Resolve-Path -LiteralPath $FixtureBinary).Path
$root = Join-Path ([IO.Path]::GetTempPath()) ('simple-scv-alias-' + [Guid]::NewGuid().ToString('N'))
[IO.Directory]::CreateDirectory((Join-Path $root 'src/app')) | Out-Null
[IO.Directory]::CreateDirectory((Join-Path $root 'examples/tool')) | Out-Null
[IO.Directory]::CreateDirectory((Join-Path $root 'build/scv')) | Out-Null
[IO.File]::WriteAllText((Join-Path $root 'examples/tool/mod.spl'), "pub fn fixture_value() -> i64: 73`n", [Text.UTF8Encoding]::new($false))
$link = New-Item -ItemType Junction -Path (Join-Path $root 'src/app/tool') -Target (Join-Path $root 'examples/tool')
if (($link.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0) { throw 'Expected a real directory junction' }
$previous = [Environment]::GetEnvironmentVariable('SIMPLE_SCV_ALIAS_FIXTURE_ROOT')
try {
    $env:SIMPLE_SCV_ALIAS_FIXTURE_ROOT = $root
    $output = @(& $binary 2>&1)
    $raw = $LASTEXITCODE
    [IO.File]::WriteAllLines((Join-Path $root 'fixture-output.txt'), [string[]]$output)
    if ($raw -ne 0 -or ($output -join "`n") -ne 'SCV_DIRECTORY_ALIAS_SNAPSHOT_PASS') {
        throw "Native alias fixture failed: raw=$raw; evidence=$root"
    }
    $snapshots = @(Get-ChildItem -LiteralPath (Join-Path $root 'build/scv/snapshots') -Directory | Where-Object { $_.Name -like 'scv-revision-v1-*' })
    if ($snapshots.Count -ne 1) { throw 'Expected one immutable snapshot' }
    $copied = Get-Item -LiteralPath (Join-Path $snapshots[0].FullName 'src/app/tool/mod.spl')
    if (($copied.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) { throw 'Snapshot retained a link instead of regular bytes' }
    $ancestor = $copied.Directory
    while ($ancestor.FullName -ne $snapshots[0].FullName) {
        if (($ancestor.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) { throw 'Snapshot contains a linked ancestor' }
        $ancestor = $ancestor.Parent
    }
    Write-Output "PASS native alias selection/materialization/drift; evidence=$root"
} finally {
    [Environment]::SetEnvironmentVariable('SIMPLE_SCV_ALIAS_FIXTURE_ROOT', $previous)
}
