param(
    [switch]$Force,
    [switch]$DryRun,
    [string]$DocRoot = ""
)

$ErrorActionPreference = "Stop"

$RootDir = Resolve-Path (Join-Path $PSScriptRoot "..")
$ModuleDir = Join-Path $RootDir ".spipe\spipe"
$ExampleDir = Join-Path $RootDir "examples\spipe"

Set-Location $RootDir
if ($DryRun) {
    Write-Output "would_init_submodules .spipe/spipe"
} else {
    git submodule update --init --recursive -- .spipe/spipe
}

if (-not $DryRun) {
    & powershell -ExecutionPolicy Bypass -File "scripts\check-spipe-submodule-gitlinks.ps1" --repair | Out-Null
}

$SpPipeDir = Join-Path $RootDir ".spipe"
if (-not (Test-Path $SpPipeDir) -and -not $DryRun) {
    New-Item -ItemType Directory -Path $SpPipeDir -Force | Out-Null
}

$ProjectLink = Join-Path $SpPipeDir "spipe_project"
if (-not (Test-Path $ProjectLink) -and -not $DryRun) {
    New-Item -ItemType Junction -Path $ProjectLink -Target $ExampleDir | Out-Null
}

function New-CommonLink {
    param(
        [string]$LinkPath,
        [string]$TargetPath
    )
    if ($DryRun) {
        Write-Output "would_link $LinkPath -> $TargetPath"
        return
    }
    $Parent = Split-Path -Parent $LinkPath
    if ($Parent -and -not (Test-Path $Parent)) {
        New-Item -ItemType Directory -Path $Parent -Force | Out-Null
    }
    if (-not (Test-Path $LinkPath)) {
        New-Item -ItemType Junction -Path $LinkPath -Target $TargetPath | Out-Null
    }
}

New-CommonLink (Join-Path $SpPipeDir "domain_expert") (Join-Path $ExampleDir "doc\00_llm_process\domain_expert")
New-CommonLink (Join-Path $SpPipeDir "template") (Join-Path $ExampleDir "doc\00_llm_process\template")
New-CommonLink (Join-Path $SpPipeDir "spipe_docs") (Join-Path $ExampleDir "doc\00_llm_process\spipe")
New-CommonLink (Join-Path $SpPipeDir "tool_expert\spipe_submodule") (Join-Path $ExampleDir "doc\00_llm_process\tool_expert\spipe_submodule")
New-CommonLink (Join-Path $SpPipeDir "project_expert\spipe") (Join-Path $ExampleDir "doc\00_llm_process\project_expert\simple")

$Cli = Join-Path $ExampleDir "cli\spipe.js"
if ((Test-Path $Cli) -and -not $DryRun) {
    if ($DocRoot -eq "") {
        node $Cli doc-link $RootDir | Out-Null
    } else {
        node $Cli doc-link $RootDir $DocRoot | Out-Null
    }
}

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
if ($DocRoot -ne "") {
    $argsList += "-DocRoot"
    $argsList += $DocRoot
}

& powershell -ExecutionPolicy Bypass -File $setup @argsList
