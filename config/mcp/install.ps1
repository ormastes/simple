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

# Kimi Code: Windows-only project layer (shell:false spawn needs .exe paths).
# Kept out of the tracked tree root because it overrides the root .mcp.json
# by server name and would break every POSIX checkout.
$kimiDir = Join-Path $projectRoot ".kimi-code"
New-Item -ItemType Directory -Force -Path $kimiDir | Out-Null
Copy-Item -LiteralPath (Join-Path $scriptDir "win\.kimi-code\mcp.json") -Destination (Join-Path $kimiDir "mcp.json") -Force
Write-Host "Installed Windows .kimi-code\mcp.json"

# Antigravity CLI (agy): its MCP config (~/.gemini/config/mcp_config.json) is
# user-global with no project cwd, so register absolute backslash .cmd paths
# (the cmd.exe-safe spelling, see win/.mcp.json).
$agy = Get-Command agy -ErrorAction SilentlyContinue
if ($null -eq $agy) {
    Write-Host "Antigravity CLI (agy) not found, skipping agy MCP setup"
} else {
    $agyServers = @(
        @{ Name = "simple-mcp"; Wrapper = "simple_mcp_server.cmd" },
        @{ Name = "simple-lsp-mcp"; Wrapper = "simple_lsp_mcp_server.cmd" },
        @{ Name = "t32-mcp"; Wrapper = "t32_mcp_server.cmd" },
        @{ Name = "t32-lsp-mcp"; Wrapper = "t32_lsp_mcp_server.cmd" }
    )
    foreach ($server in $agyServers) {
        $cmd = Join-Path $projectRoot ("bin\" + $server.Wrapper)
        if (-not (Test-Path -LiteralPath $cmd)) {
            Write-Host ("Warning: {0} not found, skipping agy {1}" -f $cmd, $server.Name)
            continue
        }
        & agy mcp add -e "SIMPLE_LOG=error" -e "RUST_LOG=error" `
            -e "SIMPLE_EXECUTION_MODE=interpreter" $server.Name $cmd
    }
    & agy mcp add spipe node (Join-Path $projectRoot ".spipe\spipe\mcp\server.js")
    Write-Host "Installed Antigravity (agy) MCP servers"
}

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
& codex mcp remove "stitch-mcp" 2>$null
& codex mcp remove "stitch" 2>$null

Write-Host "Installed Codex MCP servers for Windows"
