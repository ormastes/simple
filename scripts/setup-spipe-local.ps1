param(
    [string]$Organization = "",
    [string]$Project = "",
    [switch]$Yes
)
$ErrorActionPreference = "Stop"
$Root = (& git -C (Join-Path $PSScriptRoot "..") rev-parse --show-toplevel).Trim()
$Direct = ((& git -C $Root ls-files --stage -- .spipe) -join "`n").StartsWith("160000 ")
$Legacy = ((& git -C $Root ls-files --stage -- .spipe/spipe) -join "`n").StartsWith("160000 ")
if ($Direct) {
    & git -C $Root submodule update --init -- .spipe
    & (Join-Path $Root ".spipe/scripts/setup-local-knowledge.ps1") -Mode project -Destination $Root -Organization $Organization -Project $Project -Yes:$Yes
} elseif ($Legacy) {
    & git -C $Root submodule update --init -- .spipe/spipe
    & (Join-Path $Root ".spipe/spipe/scripts/setup-local-knowledge.ps1") -Mode project -Destination $Root -Organization $Organization -Project $Project -Yes:$Yes
} else { throw "No .spipe submodule is recorded" }
