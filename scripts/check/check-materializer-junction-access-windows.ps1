param([string]$FixtureRoot = $env:TEMP)
$ErrorActionPreference = 'Stop'
$producer = Join-Path $PSScriptRoot '../setup/materialize-symlinks-windows.shs'
$source = [IO.File]::ReadAllText((Resolve-Path $producer))
$match = [regex]::Match($source, '(?s)Add-Type -TypeDefinition @"\r?\n(.*?)\r?\n"@')
if (!$match.Success) { throw 'cannot extract materializer native API' }
Add-Type -TypeDefinition $match.Groups[1].Value
$root = [IO.Path]::GetFullPath((Resolve-Path $FixtureRoot).Path).TrimEnd('\') + '\'
$fixture = Join-Path $root ('materializer-junction-test-' + [guid]::NewGuid().ToString('N'))
$link = Join-Path $fixture 'link'
$oldBlob = $env:MATERIALIZER_BLOB
$oldJournal = $env:MATERIALIZER_JOURNAL
$held = [Collections.Generic.List[Microsoft.Win32.SafeHandles.SafeFileHandle]]::new()
try {
    [IO.Directory]::CreateDirectory($fixture) | Out-Null
    $target = Join-Path $fixture 'target'
    $other = Join-Path $fixture 'other'
    [IO.Directory]::CreateDirectory($target) | Out-Null
    [IO.Directory]::CreateDirectory($other) | Out-Null
    $env:MATERIALIZER_BLOB = Join-Path $fixture 'blob'
    $env:MATERIALIZER_JOURNAL = Join-Path $fixture 'journal'
    [IO.File]::WriteAllText($env:MATERIALIZER_BLOB, 'target')
    [IO.File]::WriteAllText($link, 'target')
    [MaterializerApi]::Create($link, $target, $true)
    [MaterializerApi]::Validate($link, $target, $true)
    $rejected = $false
    try { [MaterializerApi]::Validate($link, $other, $true) }
    catch { if ($_ -notmatch 'identity.volume-file-id.mismatch') { throw }; $rejected = $true }
    if (!$rejected) { throw 'wrong junction target accepted' }
    $rejected = $false
    try { [MaterializerApi]::ProbeTarget($link) }
    catch { if ($_ -notmatch 'target.reparse') { throw }; $rejected = $true }
    if (!$rejected) { throw 'reparse target accepted' }
    $tampered = Join-Path $fixture 'tampered'
    [IO.File]::WriteAllText($tampered, 'altered')
    $rejected = $false
    try { [MaterializerApi]::Create($tampered, $target, $true) }
    catch { if ($_ -notmatch 'tampered placeholder bytes') { throw }; $rejected = $true }
    if (!$rejected -or [IO.File]::ReadAllText($tampered) -ne 'altered') { throw 'tampered placeholder not preserved' }
    # Exercise actual parent creation and rename under the retained handles.
    $destination = Join-Path $fixture 'new\nested\receipt'
    $parents = [MaterializerApi].GetMethod('Parents', [Reflection.BindingFlags]'NonPublic,Static')
    $arguments = [object[]]::new(3)
    $arguments[0] = $destination.PSObject.BaseObject
    $arguments[1] = $true
    $arguments[2] = $held
    $parents.Invoke($null, $arguments) | Out-Null
    $pending = Join-Path $fixture 'pending'
    [IO.File]::WriteAllText($pending, 'receipt')
    [IO.File]::Move($pending, $destination)
    if ([IO.File]::ReadAllText($destination) -ne 'receipt') { throw 'receipt rename failed' }
    Write-Output "materializer junction access and receipt parent rename: PASS ($root)"
} finally {
    foreach ($handle in $held) { $handle.Dispose() }
    $env:MATERIALIZER_BLOB = $oldBlob
    $env:MATERIALIZER_JOURNAL = $oldJournal
    if (![IO.Path]::GetFullPath($fixture).StartsWith($root, [StringComparison]::OrdinalIgnoreCase)) { throw 'unsafe fixture cleanup path' }
    # Remove only the junction itself before recursive fixture cleanup.
    if ([IO.Directory]::Exists($link)) { [IO.Directory]::Delete($link, $false) }
    if (Test-Path -LiteralPath $fixture) { Remove-Item -LiteralPath $fixture -Recurse -Force }
}
