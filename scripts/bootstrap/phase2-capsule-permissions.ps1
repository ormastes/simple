param(
    [Parameter(Mandatory=$true)][ValidateSet('freeze', 'verify', 'thaw')][string]$Action,
    [Parameter(Mandatory=$true)][string]$Path
)
$ErrorActionPreference = 'Stop'
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
        $acl = $node.GetAccessControl()
        if ($Action -eq 'freeze') {
            $acl.AddAccessRule($rule)
            $node.SetAccessControl($acl)
        } elseif ($Action -eq 'thaw') {
            $acl.RemoveAccessRuleSpecific($rule)
            # Test/output cleanup may thaw a parent containing several roots.
            $baseRule = [System.Security.AccessControl.FileSystemAccessRule]::new(
                $everyone, $baseRights, [System.Security.AccessControl.AccessControlType]::Deny)
            $acl.RemoveAccessRuleSpecific($baseRule)
            $node.SetAccessControl($acl)
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
    [Console]::Error.WriteLine("phase2-capsule-permissions: $($_.Exception.Message)")
    exit 1
}
