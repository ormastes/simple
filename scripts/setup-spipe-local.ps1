param(
    [string]$Organization = "",
    [string]$Project = "",
    [switch]$Yes
)
$ErrorActionPreference = "Stop"
$Root = (& git -C (Join-Path $PSScriptRoot "..") rev-parse --show-toplevel).Trim()
$CommonHome = if ($env:SPIPE_HOME) { $env:SPIPE_HOME } else { Join-Path $HOME "spipe" }
$CommonRoute = Join-Path $Root ".spipe/common"
$CommonPackage = Join-Path $CommonHome "package.json"
$Legacy = ((& git -C $Root ls-files --stage -- .spipe/spipe) -join "`n").StartsWith("160000 ")
if ((Test-Path $CommonPackage) -and ((Get-Content -Raw $CommonPackage) -match '"name"\s*:\s*"@simple-lang/spipe"')) {
    if (-not (Test-Path $CommonRoute)) {
        New-Item -ItemType SymbolicLink -Path $CommonRoute -Target $CommonHome | Out-Null
    }
    $ResolvedRoute = (Resolve-Path $CommonRoute).Path
    $ResolvedHome = (Resolve-Path $CommonHome).Path
    if ($ResolvedRoute -ne $ResolvedHome) { throw ".spipe/common does not resolve to $CommonHome" }
    & (Join-Path $CommonHome "scripts/setup-local-knowledge.ps1") -Mode project -Destination $Root -Organization $Organization -Project $Project -Yes:$Yes
} elseif ($Legacy) {
    & git -C $Root submodule update --init -- .spipe/spipe
    & (Join-Path $Root ".spipe/spipe/scripts/setup-local-knowledge.ps1") -Mode project -Destination $Root -Organization $Organization -Project $Project -Yes:$Yes
} else { throw "Install canonical common at $CommonHome; no usable legacy submodule is recorded" }
