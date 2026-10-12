param(
    [Parameter(Mandatory=$true)][ValidateSet('freeze', 'verify', 'thaw')][string]$Action,
    [Parameter(Mandatory=$true)][string]$Path
)
$ErrorActionPreference = 'Stop'
function ConvertTo-NativeAclPath([string]$FullName) {
    # FileSystemInfo retains the ordinary path for traversal and reparse checks.
    # Only .NET ACL operations need the extended Windows spelling: Framework
    # GetAccessControl rejects otherwise valid leaves beyond MAX_PATH.
    $native = $FullName.Replace('/', '\')
    if ($native.StartsWith('\\?\UNC\', [StringComparison]::OrdinalIgnoreCase)) {
        $native = '\\' + $native.Substring(8)
    } elseif ($native.StartsWith('\\?\', [StringComparison]::Ordinal)) {
        $native = $native.Substring(4)
    }
    if ($native -match '^[A-Za-z]:\\') { return '\\?\' + $native }
    if ($native -match '^\\\\[^\\]+\\[^\\]+(?:\\|$)') {
        return '\\?\UNC\' + $native.Substring(2)
    }
    throw "unsupported absolute Windows ACL path: $FullName"
}
try {
    # MSYS chmod maps file writes to READONLY, but cannot protect directories.
    # Deny content/namespace writes explicitly, as POSIX a-w does. The owner can
    # deliberately thaw either representation; neither is an adversarial seal.
    $root = Get-Item -LiteralPath $Path -Force
    if (-not $root.PSIsContainer) { throw 'capsule root is not a directory' }
    $nodes = [System.Collections.Generic.List[System.IO.FileSystemInfo]]::new()
    $pending = [System.Collections.Generic.Queue[System.IO.FileSystemInfo]]::new()
    $pending.Enqueue($root)
    while ($pending.Count -gt 0) {
        $node = $pending.Dequeue()
        if ($node.Attributes -band [IO.FileAttributes]::ReparsePoint) {
            throw "capsule contains a reparse point: $($node.FullName)"
        }
        $nodes.Add($node)
        if ($node.PSIsContainer) {
            foreach ($child in Get-ChildItem -LiteralPath $node.FullName -Force) {
                $pending.Enqueue($child)
            }
        }
    }
    $everyone = [System.Security.Principal.SecurityIdentifier]::new('S-1-1-0')
    $baseRights = [System.Security.AccessControl.FileSystemRights]::Write -bor
        [System.Security.AccessControl.FileSystemRights]::DeleteSubdirectoriesAndFiles
    foreach ($node in $nodes) {
        if ($node.Attributes -band [IO.FileAttributes]::ReparsePoint) {
            throw "capsule contains a reparse point: $($node.FullName)"
        }
        $rights = $baseRights
        if ($node.FullName -ne $root.FullName) {
            $rights = $rights -bor [System.Security.AccessControl.FileSystemRights]::Delete
        }
        $rule = [System.Security.AccessControl.FileSystemAccessRule]::new(
            $everyone, $rights, [System.Security.AccessControl.AccessControlType]::Deny)
        # Use the Windows PowerShell/.NET ACL API directly. An inherited
        # PowerShell 7 PSModulePath can prevent Security-module auto-loading.
        $aclPath = ConvertTo-NativeAclPath $node.FullName
        if ($node.PSIsContainer) {
            $acl = [IO.Directory]::GetAccessControl($aclPath)
        } else {
            $acl = [IO.File]::GetAccessControl($aclPath)
        }
        if ($Action -eq 'freeze') {
            $acl.AddAccessRule($rule)
            if ($node.PSIsContainer) { [IO.Directory]::SetAccessControl($aclPath, $acl) }
            else { [IO.File]::SetAccessControl($aclPath, $acl) }
        } elseif ($Action -eq 'thaw') {
            $acl.RemoveAccessRuleSpecific($rule)
            # Test/output cleanup may thaw a parent containing several roots.
            $baseRule = [System.Security.AccessControl.FileSystemAccessRule]::new(
                $everyone, $baseRights, [System.Security.AccessControl.AccessControlType]::Deny)
            $acl.RemoveAccessRuleSpecific($baseRule)
            if ($node.PSIsContainer) { [IO.Directory]::SetAccessControl($aclPath, $acl) }
            else { [IO.File]::SetAccessControl($aclPath, $acl) }
        } else {
            $denied = 0
            foreach ($entry in $acl.GetAccessRules($true, $true,
                [System.Security.Principal.SecurityIdentifier])) {
                if ($entry.IdentityReference -eq $everyone -and
                    $entry.AccessControlType -eq 'Deny' -and
                    -not ($entry.PropagationFlags -band
                        [System.Security.AccessControl.PropagationFlags]::InheritOnly)) {
                    $denied = $denied -bor [int]$entry.FileSystemRights
                }
            }
            if (($denied -band [int]$rights) -ne [int]$rights) {
                throw "capsule node permits writes: $($node.FullName)"
            }
        }
    }
} catch {
    [Console]::Error.WriteLine("phase2-capsule-permissions: action=$Action node=$($node.FullName): $($_.Exception.Message)")
    exit 1
}
