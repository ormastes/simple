param(
    [switch]$Check,
    [switch]$Install
)

$ErrorActionPreference = "Stop"
$Root = (Resolve-Path (Join-Path $PSScriptRoot "../..")).Path
$Source = Join-Path $Root "scripts/hooks/pre-push-worktree-launcher"
$Dispatcher = Join-Path $Root "scripts/hooks/pre-push"
$HooksPath = (& git -C $Root rev-parse --git-path hooks 2>$null)
if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($HooksPath)) {
    Write-Error "install-must-check-hooks: not a Git worktree"
    exit 2
}
if (-not [System.IO.Path]::IsPathRooted($HooksPath)) {
    $HooksPath = Join-Path $Root $HooksPath
}
$Destination = Join-Path $HooksPath "pre-push"
$Local = "$Destination.local"

function Test-CurrentHook {
    if (-not (Test-Path -LiteralPath $Destination -PathType Leaf)) { return $false }
    $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $Source).Hash
    $destHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $Destination).Hash
    return $sourceHash -eq $destHash
}

function Test-LegacyCanonicalHook {
    if (-not (Test-Path -LiteralPath $Destination)) { return $false }
    $legacy = Join-Path $Root "scripts/check/pre-push-conflict-tree-guard.shs"
    try {
        $destinationHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $Destination).Hash
        return ((Get-FileHash -Algorithm SHA256 -LiteralPath $legacy).Hash -eq $destinationHash) -or
               ((Get-FileHash -Algorithm SHA256 -LiteralPath $Dispatcher).Hash -eq $destinationHash)
    } catch {
        return $false
    }
}

if ($Check -or -not $Install) {
    if (Test-CurrentHook) {
        Write-Output "must-check pre-push hook: INSTALLED"
        exit 0
    }
    Write-Output "must-check pre-push hook: NOT INSTALLED OR OUTDATED"
    exit 1
}

New-Item -ItemType Directory -Force -Path $HooksPath | Out-Null
if ((Test-Path -LiteralPath $Destination) -and -not (Test-CurrentHook)) {
    if (Test-LegacyCanonicalHook) {
        Remove-Item -LiteralPath $Destination -Force
    } elseif (Test-Path -LiteralPath $Local) {
        Write-Error "install-must-check-hooks: refusing to overwrite existing $Local"
        exit 1
    } else {
        Move-Item -LiteralPath $Destination -Destination $Local
        Write-Output "install-must-check-hooks: preserved existing hook as $Local"
    }
}
Copy-Item -LiteralPath $Source -Destination $Destination -Force
if (-not (Test-CurrentHook)) {
    Write-Error "install-must-check-hooks: installed hook failed verification"
    exit 1
}
Write-Output "must-check pre-push hook: INSTALLED"
