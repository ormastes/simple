param([string]$NativeScript)
$ErrorActionPreference = 'Stop'
$source = Get-Content -Raw -LiteralPath $NativeScript
$entry = '[Stage3MaterializedConsumer]::Run()'
if ($source.Split([string[]]@($entry), [StringSplitOptions]::None).Length -ne 2) { throw 'native entry changed' }
$source = $source.Replace($entry, '') -replace '(?m)^exit 0\r?$', ''
Invoke-Expression $source
$flags = [Reflection.BindingFlags]::NonPublic -bor [Reflection.BindingFlags]::Static
$type = [Stage3MaterializedConsumer]
function Invoke-Owner([string]$Name, [object[]]$Arguments) {
    $method = $type.GetMethod($Name, $flags)
    if ($null -eq $method) { throw "missing owner method: $Name" }
    for ($n = 0; $n -lt $Arguments.Length; $n++) { $Arguments[$n] = $Arguments[$n].PSObject.BaseObject }
    try { return $method.Invoke($null, $Arguments) }
    catch [Reflection.TargetInvocationException] { throw $_.Exception.InnerException }
}
function Extended([string]$Path) { return '\\?\' + $Path }
$owned = Join-Path ([IO.Path]::GetTempPath()) ('stage3-long-' + [Guid]::NewGuid().ToString('N'))
$external = Join-Path ([IO.Path]::GetTempPath()) ('stage3-external-' + [Guid]::NewGuid().ToString('N'))
$junction = Join-Path $owned 'junction'
try {
    [void][IO.Directory]::CreateDirectory($owned)
    [void][IO.Directory]::CreateDirectory($external)
    $sentinel = Join-Path $external 'sentinel.txt'
    [IO.File]::WriteAllText($sentinel, 'external retained')
    $nested = Join-Path (Join-Path $owned ('a' * 110)) ('b' * 110)
    [void][IO.Directory]::CreateDirectory((Extended $nested))
    $paths = @((Join-Path $owned 'ordinary.txt'), (Join-Path $owned (('c' * 200) + '.txt')), (Join-Path $nested 'unicode-경로.txt'))
    if ($paths[1].Length -lt 260 -or $paths[2].Length -le 260) { throw 'fixture did not cross MAX_PATH' }
    foreach ($path in $paths) {
        [IO.File]::WriteAllText((Extended $path), 'actual native bytes')
        $held = New-Object 'System.Collections.Generic.List[Microsoft.Win32.SafeHandles.SafeFileHandle]'
        try {
            [void](Invoke-Owner 'Parents' @($path, $false, $held))
            $handle = Invoke-Owner 'Open' @($path, $true, [uint32]2147483648)
            try {
                $stream = [IO.FileStream]::new($handle, [IO.FileAccess]::Read)
                $reader = [IO.StreamReader]::new($stream)
                try { if ($reader.ReadToEnd() -ne 'actual native bytes') { throw 'wrong native bytes' } }
                finally { $reader.Dispose() }
            } finally { $handle.Dispose() }
        } finally { foreach ($handle in $held) { $handle.Dispose() } }
    }
    foreach ($path in @('../escape', 'a/../escape', 'C:/absolute', 'a\\b')) {
        $rejected = $false
        try { [void](Invoke-Owner 'CheckPath' @($path)) } catch [IO.IOException] { $rejected = $true }
        if (-not $rejected) { throw "unsafe lexical path admitted: $path" }
    }
    $missingRejected = $false
    try { [void](Invoke-Owner 'Open' @((Join-Path $nested 'missing.txt'), $true, [uint32]0)) }
    catch [IO.IOException] { $missingRejected = $_.Exception.Message -match 'api.open:.*:win32=2$' }
    if (-not $missingRejected) { throw 'missing long path did not fail closed' }
    & cmd.exe /d /c mklink /J $junction $external >$null
    if ($LASTEXITCODE -ne 0) { throw 'junction setup failed' }
    $held = New-Object 'System.Collections.Generic.List[Microsoft.Win32.SafeHandles.SafeFileHandle]'
    $reparseRejected = $false
    try { [void](Invoke-Owner 'Parents' @((Join-Path $junction 'sentinel.txt'), $false, $held)) }
    catch [IO.IOException] { $reparseRejected = $_.Exception.Message -like 'ancestor.reparse:*' }
    finally { foreach ($handle in $held) { $handle.Dispose() } }
    if (-not $reparseRejected) { throw 'junction ancestor admitted' }
    if ([IO.File]::ReadAllText($sentinel) -ne 'external retained') { throw 'external sentinel changed' }
    Write-Output 'stage3_windows_long_path_cases=9'
} finally {
    # Remove the junction itself before recursive cleanup of the owned tree.
    if ([IO.Directory]::Exists($junction)) { [IO.Directory]::Delete($junction, $false) }
    if ([IO.Directory]::Exists((Extended $owned))) { [IO.Directory]::Delete((Extended $owned), $true) }
    if ([IO.Directory]::Exists($external)) { [IO.Directory]::Delete($external, $true) }
}
