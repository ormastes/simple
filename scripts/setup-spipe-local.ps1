param(
    [string]$Organization = "",
    [string]$Project = "",
    [switch]$Yes
)
$ErrorActionPreference = "Stop"
$Root = (& git -C (Join-Path $PSScriptRoot "..") rev-parse --show-toplevel).Trim()
function Expand-HomePrefix([string]$Value) {
    if ($Value -eq '{home}') { return $HOME }
    if ($Value.StartsWith('{home}/') -or $Value.StartsWith('{home}\')) {
        return Join-Path $HOME $Value.Substring(7)
    }
    return $Value
}
$CommonHome = if ($env:SPIPE_HOME) { $env:SPIPE_HOME } else { Join-Path $HOME ".spipe" }
$PrivateHome = if ($env:SPIPE_WORKSPACE) { $env:SPIPE_WORKSPACE } else { Join-Path $HOME "spipe" }
$CommonHome = Expand-HomePrefix $CommonHome
$PrivateHome = Expand-HomePrefix $PrivateHome
$PrivateRoute = Join-Path $PrivateHome "common"
$CommonRoute = Join-Path $Root ".spipe/common"
$CommonPackage = Join-Path $CommonHome "package.json"
$Legacy = ((& git -C $Root ls-files --stage -- .spipe/spipe) -join "`n").StartsWith("160000 ")
if ((Test-Path $CommonPackage) -and ((Get-Content -Raw $CommonPackage) -match '"name"\s*:\s*"@simple-lang/spipe"')) {
    function Get-PhysicalPath([string]$Path) {
        if (-not (Test-Path -LiteralPath $Path)) {
            $Full = [IO.Path]::GetFullPath($Path)
            return Join-Path (Get-PhysicalPath (Split-Path $Full -Parent)) (Split-Path $Full -Leaf)
        }
        $Item = Get-Item -Force -LiteralPath $Path
        if ($Item.LinkType) {
            $Target = @($Item.Target)[0]
            if (-not [IO.Path]::IsPathRooted($Target)) { $Target = Join-Path $Item.Parent.FullName $Target }
            return Get-PhysicalPath $Target
        }
        if ($Item.Parent) { return Join-Path (Get-PhysicalPath $Item.Parent.FullName) $Item.Name }
        return $Item.FullName
    }
    $CorePhysical = (Get-PhysicalPath $CommonHome).TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar
    $PrivatePhysical = (Get-PhysicalPath $PrivateHome).TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar
    if ($CorePhysical.StartsWith($PrivatePhysical, [StringComparison]::OrdinalIgnoreCase) -or $PrivatePhysical.StartsWith($CorePhysical, [StringComparison]::OrdinalIgnoreCase)) { throw "Core and private workspace must be disjoint" }
    $PrivatePackage = Join-Path $PrivateHome "package.json"
    if ((Test-Path $PrivatePackage) -and ((Get-Content -Raw $PrivatePackage) -match '"name"\s*:\s*"@simple-lang/spipe"')) { throw "Private workspace contains legacy core; migrate existing data explicitly" }
    foreach ($Route in @($PrivateRoute, $CommonRoute)) {
        $Target = if ($Route -eq $PrivateRoute) { $CommonHome } else { $PrivateRoute }
        New-Item -ItemType Directory -Force -Path (Split-Path $Route -Parent) | Out-Null
        if (-not (Get-Item -Force -LiteralPath $Route -ErrorAction SilentlyContinue)) {
            $LinkType = if ($env:OS -eq "Windows_NT") { "Junction" } else { "SymbolicLink" }
            New-Item -ItemType $LinkType -Path $Route -Target $Target | Out-Null
        }
        if ((Get-PhysicalPath $Route) -ne (Get-PhysicalPath $CommonHome)) { throw "$Route does not resolve to $CommonHome; preserve and migrate existing data explicitly" }
    }
    $PreviousCore = $env:SPIPE_HOME
    $PreviousWorkspace = $env:SPIPE_WORKSPACE
    try {
        $env:SPIPE_HOME = $CommonHome
        $env:SPIPE_WORKSPACE = $PrivateHome
        & (Join-Path $CommonHome "scripts/setup-local-knowledge.ps1") -Mode project -Destination $Root -Organization $Organization -Project $Project -Yes:$Yes
    } finally {
        $env:SPIPE_HOME = $PreviousCore
        $env:SPIPE_WORKSPACE = $PreviousWorkspace
    }
} elseif ($Legacy) {
    & git -C $Root submodule update --init -- .spipe/spipe
    & (Join-Path $Root ".spipe/spipe/scripts/setup-local-knowledge.ps1") -Mode project -Destination $Root -Organization $Organization -Project $Project -Yes:$Yes
} else { throw "Install canonical common at $CommonHome; no usable legacy submodule is recorded" }
