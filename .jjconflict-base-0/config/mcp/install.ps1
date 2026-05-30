param(
    [switch]$SkipCodex
)

$ErrorActionPreference = "Stop"

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Resolve-Path (Join-Path $scriptDir "..\..")
$src = Join-Path $scriptDir "win\.mcp.json"
$dst = Join-Path $projectRoot ".mcp.json"

Copy-Item -LiteralPath $src -Destination $dst -Force
Write-Host "Installed Windows .mcp.json"

if ($SkipCodex) {
    Write-Host "Skipped Codex MCP setup"
    exit 0
}

$codex = Get-Command codex -ErrorAction SilentlyContinue
if ($null -eq $codex) {
    Write-Host "Codex CLI not found, skipping Codex MCP setup"
    exit 0
}

$servers = @(
    @{ Name = "simple-mcp"; Wrapper = "simple_mcp_server.cmd" },
    @{ Name = "simple-lsp-mcp"; Wrapper = "simple_lsp_mcp_server.cmd" }
)

foreach ($server in $servers) {
    $cmd = Join-Path $projectRoot ("bin\" + $server.Wrapper)
    if (-not (Test-Path -LiteralPath $cmd)) {
        Write-Host ("Warning: {0} not found, skipping {1}" -f $cmd, $server.Name)
        continue
    }

    & codex mcp remove $server.Name 2>$null
    & codex mcp add $server.Name `
        --env "SIMPLE_LOG=error" `
        --env "RUST_LOG=error" `
        --env ("SIMPLE_LIB=" + (Join-Path $projectRoot "src")) `
        -- $cmd
}

& codex mcp remove "chrome-devtools" 2>$null

$node = Get-Command node -ErrorAction SilentlyContinue
$stitch = Join-Path $projectRoot "bin\codex_stitch_mcp.js"
if (($null -ne $node) -and (Test-Path -LiteralPath $stitch)) {
    & codex mcp remove "stitch-mcp" 2>$null
    & codex mcp remove "stitch" 2>$null
    & codex mcp add "stitch-mcp" -- node $stitch
} else {
    Write-Host "Warning: node or bin\codex_stitch_mcp.js not found, skipping stitch"
}

Write-Host "Installed Codex MCP servers for Windows"
