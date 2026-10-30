param(
    [ValidateSet("--check", "--repair")]
    [string]$Mode = "--check"
)

$ErrorActionPreference = "Stop"

$RootDir = Resolve-Path (Join-Path $PSScriptRoot "..")
Set-Location $RootDir

$failures = 0

function Get-GitIndexLines($Path) {
    $output = git ls-files --stage $Path
    if ($LASTEXITCODE -ne 0) {
        throw "git ls-files failed for $Path"
    }
    @($output | Where-Object { $_ -ne "" })
}

function Test-Gitlink($Path) {
    $lines = Get-GitIndexLines $Path
    $mode = ""
    if ($lines.Count -gt 0) {
        $mode = ($lines[0] -split "\s+")[0]
    }
    if ($lines.Count -eq 1 -and $mode -eq "160000") {
        Write-Output "gitlink_ok $Path"
        return
    }
    $script:failures += 1
    if ($mode -eq "") {
        $mode = "missing"
    }
    Write-Output "gitlink_bad $Path entries=$($lines.Count) mode=$mode"
}

function Repair-Gitlink($Path) {
    if (-not (Test-Path -LiteralPath $Path -PathType Container)) {
        Write-Error "gitlink_repair_missing_worktree $Path"
    }
    $head = git -C $Path rev-parse HEAD
    if ($LASTEXITCODE -ne 0) {
        throw "git rev-parse failed for $Path"
    }
    $entries = git ls-files -z $Path
    if ($entries) {
        $entries -split "`0" |
            Where-Object { $_ -ne "" } |
            ForEach-Object { git update-index --force-remove -- $_ | Out-Null }
    }
    git update-index --add --cacheinfo "160000,$head,$Path"
    if ($LASTEXITCODE -ne 0) {
        throw "git update-index failed for $Path"
    }
    Write-Output "gitlink_repaired $Path $head"
}

if ($Mode -eq "--repair") {
    Repair-Gitlink ".spipe/spipe"
}

Test-Gitlink ".spipe/spipe"
function Test-TrackedTree($Path) {
    $lines = Get-GitIndexLines $Path
    $mode = ""
    if ($lines.Count -gt 0) {
        $mode = ($lines[0] -split "\s+")[0]
    }
    if ($lines.Count -gt 1 -and $mode -ne "160000") {
        Write-Output "tracked_tree_ok $Path entries=$($lines.Count)"
        return
    }
    $script:failures += 1
    if ($mode -eq "") {
        $mode = "missing"
    }
    Write-Output "tracked_tree_bad $Path entries=$($lines.Count) mode=$mode"
}

Test-TrackedTree "examples/05_stdlib/spipe"

if ($failures -eq 0) {
    Write-Output "STATUS: PASS spipe-submodule-gitlinks"
} else {
    Write-Output "STATUS: FAIL spipe-submodule-gitlinks"
    exit 1
}
