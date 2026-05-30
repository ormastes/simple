param(
    [switch]$Force,
    [switch]$DryRun
)

$ErrorActionPreference = "Stop"

$RootDir = Resolve-Path (Join-Path $PSScriptRoot "..")
$ModuleDir = Join-Path $RootDir ".spipe\spipe"

Set-Location $RootDir
git submodule update --init --recursive -- .spipe/spipe

$setup = Join-Path $ModuleDir "scripts\setup-spipe-links.ps1"
if (-not (Test-Path -LiteralPath $setup -PathType Leaf)) {
    Write-Error "setup-spipe-submodule: missing $setup"
}

$argsList = @()
if ($Force) {
    $argsList += "-Force"
}
if ($DryRun) {
    $argsList += "-DryRun"
}

& powershell -ExecutionPolicy Bypass -File $setup @argsList
