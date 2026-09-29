param([string]$NativeScript, [string]$Repo)
$ErrorActionPreference = 'Stop'

# Exercise the generated consumer itself without requiring a materialization
# receipt. Keep its real private path checks and Git inventory methods intact.
$source = Get-Content -Raw -LiteralPath $NativeScript
$entry = '[Stage3MaterializedConsumer]::Run()'
if ($source.Split([string[]]@($entry), [StringSplitOptions]::None).Length -ne 2) {
    throw 'Stage3 native entry point changed'
}
$source = $source.Replace($entry, '')
$source = $source -replace '(?m)^exit 0\r?$', ''
Invoke-Expression $source

$flags = [Reflection.BindingFlags]::NonPublic -bor [Reflection.BindingFlags]::Static
$type = [Stage3MaterializedConsumer]
$check = $type.GetMethod('CheckPath', $flags)
$headLinks = $type.GetMethod('HeadLinks', $flags)
$inventory = $type.GetMethod('Inventory', $flags)
$entries = $type.GetField('entries', $flags)
$maxEntries = $type.GetField('MaxEntries', $flags)
$maxUntracked = $type.GetField('MaxUntracked', $flags)
if ($null -eq $check -or $null -eq $headLinks -or $null -eq $inventory -or
    $null -eq $entries -or $null -eq $maxEntries -or $null -eq $maxUntracked) {
    throw 'Stage3 native path methods missing'
}
if ($maxUntracked.GetValue($null) -ne 100000) {
    throw 'Stage3 untracked inventory ceiling changed'
}

function Invoke-Checked($Method, [object[]]$Arguments) {
    for ($n = 0; $n -lt $Arguments.Length; $n++) {
        $Arguments[$n] = $Arguments[$n].PSObject.BaseObject
    }
    try { return $Method.Invoke($null, $Arguments) }
    catch [Reflection.TargetInvocationException] { throw $_.Exception.InnerException }
}

$valid = @(
    'assets/fonts/google-fonts/apache/robotoslab/RobotoSlab[wght].ttf',
    'Untracked[wght].txt',
    'Untrackedw.txt',
    '$(touch injected-marker).txt'
)
foreach ($path in $valid) { [void](Invoke-Checked $check @($path)) }

$invalid = @(
    '../escape', 'dir/../escape', 'dir/./file', '/absolute',
    'dir//file', 'dir\file', 'C:/absolute', 'file:stream',
    'file*glob', 'file?glob', "file`nline",
    "file`rline", "file`tline", 'CON.txt', 'trailing.', 'trailing '
)
foreach ($path in $invalid) {
    $rejected = $false
    try { [void](Invoke-Checked $check @($path)) }
    catch [IO.IOException] { $rejected = $true }
    if (-not $rejected) { throw "Stage3 accepted unsafe path: $path" }
}

$head = (& $env:STAGE3_GIT -C $Repo rev-parse HEAD).Trim()
$links = New-Object 'System.Collections.Generic.Dictionary[string,string]'
$gitlinks = New-Object 'System.Collections.Generic.Dictionary[string,string]'
[void]$entries.SetValue($null, 100000)
[void](Invoke-Checked $headLinks @($Repo, $head, $gitlinks))
if ($entries.GetValue($null) -ne 100002) {
    throw 'Stage3 rejected a tracked entry count above the former 100000 cap'
}
$limit = $maxEntries.GetValue($null)
[void]$entries.SetValue($null, $limit - 2)
[void](Invoke-Checked $headLinks @($Repo, $head, $gitlinks))
if ($entries.GetValue($null) -ne $limit) {
    throw 'Stage3 rejected the exact admitted entry boundary'
}
[void]$entries.SetValue($null, $limit - 1)
$overflowRejected = $false
try { [void](Invoke-Checked $headLinks @($Repo, $head, $gitlinks)) }
catch [IO.IOException] { $overflowRejected = $_.Exception.Message -eq 'bound.entries' }
if (-not $overflowRejected) { throw 'Stage3 accepted one entry past its ceiling' }
[void]$entries.SetValue($null, 0)
$result = Invoke-Checked $inventory @($Repo, $head, $links)
if ($result -notmatch '(?m)^dirty_fingerprint=[0-9a-f]{64}$') {
    throw 'Stage3 inventory did not fingerprint untracked bracket paths'
}
if (Test-Path -LiteralPath (Join-Path $Repo 'injected-marker')) {
    throw 'Stage3 evaluated shell syntax in a filename'
}
Write-Output "stage3_windows_bracket_path_cases=$($valid.Count + $invalid.Count + 5)"
