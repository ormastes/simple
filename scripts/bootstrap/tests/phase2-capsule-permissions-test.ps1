param(
    [string]$PermissionsScript = (Join-Path $PSScriptRoot '../phase2-capsule-permissions.ps1'),
    [ValidateSet('ordinary', 'long')][string[]]$Cases = @('ordinary', 'long'),
    [switch]$CleanupOnly
)
$ErrorActionPreference = 'Stop'
$PermissionsScript = (Resolve-Path -LiteralPath $PermissionsScript).Path
$windowsPowerShell = Join-Path $env:SystemRoot 'System32/WindowsPowerShell/v1.0/powershell.exe'
$ownedParent = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../build/native_probe'))
$ownedRoot = Join-Path $ownedParent ('capsule-acl-test-' + [Guid]::NewGuid().ToString('N'))

function Assert-True($Condition, [string]$Message) {
    if (-not $Condition) { throw $Message }
}
function Invoke-Permissions([string]$Action, [string]$Path, [bool]$Success) {
    $saved = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $output = & $windowsPowerShell -NoLogo -NoProfile -NonInteractive -ExecutionPolicy Bypass `
        -File $PermissionsScript -Action $Action -Path $Path 2>&1 | Out-String
    $code = $LASTEXITCODE
    $ErrorActionPreference = $saved
    Assert-True (($code -eq 0) -eq $Success) "$Action exit=$code path=$Path output=$output"
    return $output
}
function Assert-Denied([scriptblock]$Operation, [string]$Message) {
    $denied = $false
    try { & $Operation } catch [UnauthorizedAccessException] { $denied = $true }
    Assert-True $denied $Message
}

# Exercise the path converter without executing the permission script body.
$tokens = $null; $errors = $null
$ast = [Management.Automation.Language.Parser]::ParseFile($PermissionsScript, [ref]$tokens, [ref]$errors)
Assert-True ($errors.Count -eq 0) 'permission script parse failed'
$converter = $ast.Find({ param($n)
    $n -is [Management.Automation.Language.FunctionDefinitionAst] -and $n.Name -eq 'ConvertTo-NativeAclPath'
}, $false)
Assert-True ($null -ne $converter) 'missing converter'
. ([scriptblock]::Create($converter.Extent.Text))
if (-not $CleanupOnly) {
Assert-True ((ConvertTo-NativeAclPath 'C:/root/leaf') -ceq '\\?\C:\root\leaf') 'DOS spelling'
Assert-True ((ConvertTo-NativeAclPath '\\server\share\leaf') -ceq '\\?\UNC\server\share\leaf') 'UNC spelling'
Assert-True ((ConvertTo-NativeAclPath '\\?\UNC\server\share\leaf') -ceq '\\?\UNC\server\share\leaf') 'extended UNC spelling'
Assert-True ((ConvertTo-NativeAclPath '\\?\C:\root\leaf') -ceq '\\?\C:\root\leaf') 'extended DOS spelling'
foreach ($invalid in @('relative\leaf', 'C:relative', '\\server', '\\?\GLOBALROOT\Device\HarddiskVolume1')) {
    $rejected = $false
    try { $null = ConvertTo-NativeAclPath $invalid } catch { $rejected = $true }
    Assert-True $rejected "accepted unsupported path $invalid"
}
}

$capsules = @()
$frozen = @{}
$junction = $null
try {
    $null = [IO.Directory]::CreateDirectory($ownedRoot)
    if ($CleanupOnly) {
        # Isolate cleanup verification without repeating already-passing ACL cases.
        $cleanupLeaf = Join-Path $ownedRoot (('x' * 180) + '.rlib')
        Assert-True ($cleanupLeaf.Length -gt 260) 'cleanup fixture too short'
        [IO.File]::WriteAllText((ConvertTo-NativeAclPath $cleanupLeaf), 'cleanup')
    } else {
    foreach ($kind in $Cases) {
        $capsule = Join-Path $ownedRoot $kind
        $capsules += $capsule
        $leafParent = Join-Path $capsule 'deps'
        $null = [IO.Directory]::CreateDirectory((ConvertTo-NativeAclPath $leafParent))
        # Match the capsule failure: parent directories are traversable, while
        # the content-addressed hosted-runtime filename crosses MAX_PATH.
        $leafName = 'probe.txt'
        if ($kind -eq 'long') { $leafName = ('x' * 150) + '.rlib' }
        $leaf = Join-Path $leafParent $leafName
        [IO.File]::WriteAllText((ConvertTo-NativeAclPath $leaf), 'before')
        if ($kind -eq 'long') { Assert-True ($leaf.Length -gt 260) 'long fixture too short' }
        $null = Invoke-Permissions verify $capsule $false
        $frozen[$capsule] = $true
        $null = Invoke-Permissions freeze $capsule $true
        $null = Invoke-Permissions verify $capsule $true
        Assert-Denied { [IO.File]::WriteAllText((ConvertTo-NativeAclPath $leaf), 'forbidden') } 'file writes allowed'
        Assert-Denied { $null = [IO.Directory]::CreateDirectory((ConvertTo-NativeAclPath (Join-Path $capsule 'forbidden'))) } 'namespace writes allowed'
        Assert-Denied { [IO.File]::Delete((ConvertTo-NativeAclPath $leaf)) } 'child delete allowed'
        $null = Invoke-Permissions thaw $capsule $true
        $frozen[$capsule] = $false
        $null = Invoke-Permissions verify $capsule $false
        [IO.File]::WriteAllText((ConvertTo-NativeAclPath $leaf), 'after')
        Assert-True ([IO.File]::ReadAllText((ConvertTo-NativeAclPath $leaf)) -eq 'after') 'thaw did not restore writes'
        Write-Output "PASS $kind freeze/verify/deny/thaw leaf_length=$($leaf.Length)"
    }
    $reparseRoot = Join-Path $ownedRoot 'reparse'
    $target = Join-Path $ownedRoot 'outside-capsule'
    $null = [IO.Directory]::CreateDirectory($reparseRoot)
    $null = [IO.Directory]::CreateDirectory($target)
    $junction = Join-Path $reparseRoot 'link'
    try { $null = New-Item -ItemType Junction -Path $junction -Target $target -ErrorAction Stop }
    catch { $junction = $null; Write-Output 'SKIP junction creation unavailable' }
    if ($null -ne $junction) {
        $sections = [Security.AccessControl.AccessControlSections]::All
        $before = [IO.Directory]::GetAccessControl($target).GetSecurityDescriptorSddlForm($sections)
        foreach ($action in @('freeze', 'verify', 'thaw')) {
            $output = Invoke-Permissions $action $reparseRoot $false
            Assert-True ($output.Contains('reparse point')) "wrong $action rejection"
        }
        $after = [IO.Directory]::GetAccessControl($target).GetSecurityDescriptorSddlForm($sections)
        Assert-True ($after -eq $before) 'reparse target ACL changed'
        Write-Output 'PASS reparse rejection for freeze/verify/thaw'
    }
    }
} finally {
    # Never recurse through a junction, and only clean this freshly generated root.
    $resolved = [IO.Path]::GetFullPath($ownedRoot)
    $prefix = $ownedParent.TrimEnd('\') + '\'
    Assert-True ($resolved.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) 'cleanup escaped owned parent'
    Assert-True ([IO.Path]::GetFileName($resolved).StartsWith('capsule-acl-test-')) 'cleanup root mismatch'
    if ($null -ne $junction -and [IO.Directory]::Exists($junction)) { [IO.Directory]::Delete($junction) }
    foreach ($capsule in $capsules) {
        if ($frozen[$capsule] -and [IO.Directory]::Exists($capsule)) { $null = Invoke-Permissions thaw $capsule $true }
    }
    if ([IO.Directory]::Exists($resolved)) {
        # Windows PowerShell Remove-Item also truncates long leaves. Use the
        # same native spelling after the owned-root checks above.
        [IO.Directory]::Delete((ConvertTo-NativeAclPath $resolved), $true)
    }
}
Write-Output 'STATUS: PASS (including owned-root cleanup)'
