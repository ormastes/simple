param(
    [ValidateSet("--apply", "--check")]
    [string]$Mode = "--apply"
)

$ErrorActionPreference = "Stop"

$RootDir = Resolve-Path (Join-Path $PSScriptRoot "..")
Set-Location $RootDir

function Fail($Message) {
    Write-Error "spipe-dev-install: $Message"
}

function Require-File($Path) {
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        Fail "missing required file: $Path"
    }
}

Require-File ".codex\skills\sp_dev\SKILL.md"
Require-File ".claude\agents\spipe\dev.md"
Require-File ".claude\skills\spipe.md"
Require-File "scripts\check-spipe-submodule-gitlinks.ps1"

if (Test-Path -LiteralPath ".codex\skills\dev") {
    if ($Mode -eq "--apply") {
        $skill = ".codex\skills\dev\SKILL.md"
        if (Test-Path -LiteralPath $skill -PathType Leaf) {
            Remove-Item -LiteralPath $skill -Force
        }
        $remaining = Get-ChildItem -LiteralPath ".codex\skills\dev" -Force -ErrorAction SilentlyContinue
        if ($remaining) {
            Fail ".codex\skills\dev contains unexpected files; remove them manually"
        }
        Remove-Item -LiteralPath ".codex\skills\dev" -Force
        Write-Output "removed retired .codex\skills\dev"
    } else {
        Fail "retired .codex\skills\dev still exists"
    }
}

$content = Get-Content -LiteralPath ".codex\skills\sp_dev\SKILL.md" -Raw
if ($content -notmatch "(?m)^name: sp_dev$") {
    Fail ".codex\skills\sp_dev\SKILL.md must declare name: sp_dev"
}
if ($content -notmatch [regex]::Escape(".claude/agents/spipe/dev.md")) {
    Fail "sp_dev skill must link to .claude/agents/spipe/dev.md"
}
if ($content -notmatch [regex]::Escape(".claude/skills/spipe.md")) {
    Fail "sp_dev skill must link to .claude/skills/spipe.md"
}

& powershell -ExecutionPolicy Bypass -File "scripts\check-spipe-submodule-gitlinks.ps1" --check | Out-Null

Write-Output "STATUS: PASS spipe-dev-command wiring"
