[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..")).Path
$BinDir = Join-Path $RepoRoot "bin"
$Resolver = Join-Path $BinDir "resolve_native_tool.ps1"

function Assert-Contract([bool]$Condition, [string]$Message) {
    if (-not $Condition) { throw $Message }
}

$wrappers = @(
    (Join-Path $BinDir "simple.cmd"),
    (Join-Path $BinDir "simple_mcp_server.cmd"),
    (Join-Path $BinDir "simple_lsp_mcp_server.cmd")
)
$source = ($wrappers | ForEach-Object { Get-Content -LiteralPath $_ -Raw }) -join "`n"
Assert-Contract ($source -notmatch 'compiler_rust|BOOTSTRAP_BIN|CURRENT_DRIVER_BIN|:source|ALLOW_SOURCE_FALLBACK|PREFER_NATIVE|simple\.cmd" run') "unsafe Windows fallback remains"
Assert-Contract ($source -match 'resolve_native_tool\.ps1') "wrappers do not share the native resolver"
foreach ($wrapper in $wrappers) {
    Assert-Contract ((Get-Content -LiteralPath $wrapper -Raw) -match '%\*') "$wrapper does not forward arguments"
}
$resolverSource = Get-Content -LiteralPath $Resolver -Raw
Assert-Contract ($resolverSource -match 'Get-FileHash' -and $resolverSource -match '\.sha256') "resolver lacks SHA-256 admission"
Assert-Contract ($resolverSource -match 'simple_pipe' -and $resolverSource -match 'lsp_symbols') "resolver lacks real MCP/LSP calls"

$simpleOutput = & $env:ComSpec /d /c ('"{0}" --version' -f (Join-Path $BinDir "simple.cmd")) 2>&1
Assert-Contract ($LASTEXITCODE -eq 0) "simple.cmd did not resolve an admitted runtime"
Assert-Contract (($simpleOutput -join "`n") -notmatch '(?i)bootstrap seed|Rust-built|debug build') "simple.cmd admitted a seed/debug runtime"

$savedMcp = $env:SIMPLE_MCP_NATIVE
$savedLsp = $env:SIMPLE_LSP_MCP_NATIVE
$temp = Join-Path ([IO.Path]::GetTempPath()) "simple-windows-wrapper-$PID"
New-Item -ItemType Directory -Force -Path $temp | Out-Null
try {
    foreach ($kind in @("mcp", "lsp")) {
        $resolved = @(& $Resolver -Kind $kind)
        Assert-Contract ($LASTEXITCODE -eq 0 -and $resolved.Count -eq 1) "$kind resolver failed"
        $native = $resolved[0]
        $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $native).Hash.ToLowerInvariant()
        Remove-Item -Force -ErrorAction SilentlyContinue (Join-Path $RepoRoot ".simple\cache\mcp-probe\$kind-$hash-windows-native-v1.stamp")
        $resolved = @(& $Resolver -Kind $kind)
        Assert-Contract ($LASTEXITCODE -eq 0 -and $resolved.Count -eq 1) "$kind real protocol probe failed"

        $tampered = Join-Path $temp ([IO.Path]::GetFileName($native))
        Copy-Item -LiteralPath $native -Destination $tampered
        Set-Content -LiteralPath "$tampered.sha256" -Value ("0" * 64) -Encoding Ascii
        if ($kind -eq "mcp") {
            $env:SIMPLE_MCP_NATIVE = $tampered
            $wrapper = Join-Path $BinDir "simple_mcp_server.cmd"
        } else {
            $env:SIMPLE_LSP_MCP_NATIVE = $tampered
            $wrapper = Join-Path $BinDir "simple_lsp_mcp_server.cmd"
        }
        & $env:ComSpec /d /c ('"{0}" --version >nul 2>nul' -f $wrapper)
        Assert-Contract ($LASTEXITCODE -eq 127) "$kind wrapper did not reject a mismatched sidecar"
    }
} finally {
    $env:SIMPLE_MCP_NATIVE = $savedMcp
    $env:SIMPLE_LSP_MCP_NATIVE = $savedLsp
    Remove-Item -LiteralPath $temp -Recurse -Force -ErrorAction SilentlyContinue
}

Write-Output "windows_tool_wrapper_contract=pass"
