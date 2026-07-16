[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..")).Path
$BinDir = Join-Path $RepoRoot "bin"
$Resolver = Join-Path $BinDir "resolve_native_tool.ps1"

function Assert-Contract([bool]$Condition, [string]$Message) {
    if (-not $Condition) { throw $Message }
}

function New-FakeNative([string]$Path, [string]$ClassName) {
    $source = @"
using System;
using System.IO;

public static class $ClassName {
    public static int Main(string[] args) {
        string mode = Environment.GetEnvironmentVariable("SIMPLE_WRAPPER_FAKE_MODE") ?? "";
        string log = Environment.GetEnvironmentVariable("SIMPLE_WRAPPER_FAKE_LOG") ?? "";
        if (log.Length > 0) File.AppendAllText(log, mode + Environment.NewLine);
        Console.In.ReadToEnd();
        if (mode == "mcp-good") {
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"result\":{\"tools\":[{\"name\":\"simple_pipe\"}]}}");
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"content\":\"spipe: linked\"}}");
        } else if (mode == "mcp-error") {
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"result\":{\"tools\":[{\"name\":\"simple_pipe\"}]}}");
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":3,\"error\":{\"message\":\"spipe: linked\"}}");
        } else if (mode == "lsp-error") {
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"result\":{\"tools\":[{\"name\":\"lsp_definition\"}]}}");
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":\"lsp-call-probe\",\"error\":{\"message\":\"Missing tool name\"}}");
        } else if (mode == "lsp-good") {
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"result\":{\"tools\":[{\"name\":\"lsp_definition\"}]}}");
            Console.WriteLine("{\"jsonrpc\":\"2.0\",\"id\":\"lsp-call-probe\",\"result\":{\"symbols\":[]}}");
        }
        return 0;
    }
}
"@
    Add-Type -TypeDefinition $source -Language CSharp -OutputAssembly $Path -OutputType ConsoleApplication
}

function Write-Sidecar([string]$Path) {
    (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant() |
        Set-Content -LiteralPath "$Path.sha256" -Encoding Ascii
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
$savedFakeMode = $env:SIMPLE_WRAPPER_FAKE_MODE
$savedFakeLog = $env:SIMPLE_WRAPPER_FAKE_LOG
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

    # Isolated negative admission: no deployed binary or production stamp is touched.
    $fakeRoot = Join-Path $temp "fake-root"
    $fakeBin = Join-Path $fakeRoot "bin"
    $fakeRelease = Join-Path $fakeBin "release\x86_64-pc-windows-msvc"
    New-Item -ItemType Directory -Force -Path $fakeRelease | Out-Null
    $fakeResolver = Join-Path $fakeBin "resolve_native_tool.ps1"
    Copy-Item -LiteralPath $Resolver -Destination $fakeResolver
    $good = Join-Path $temp "fake-good.exe"
    $bad = Join-Path $temp "fake-bad.exe"
    New-FakeNative $good "SimpleWrapperFakeGood"
    New-FakeNative $bad "SimpleWrapperFakeBad"
    $candidate = Join-Path $fakeRelease "simple_mcp_server.exe"
    Copy-Item -LiteralPath $good -Destination $candidate
    $fakeLog = Join-Path $temp "fake.log"
    $env:SIMPLE_WRAPPER_FAKE_LOG = $fakeLog
    $env:SIMPLE_MCP_NATIVE = $candidate

    Remove-Item -Force -ErrorAction SilentlyContinue "$candidate.sha256", $fakeLog
    $null = @(& $fakeResolver -Kind mcp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127 -and -not (Test-Path -LiteralPath $fakeLog)) "MCP resolver executed a candidate without a sidecar"

    Set-Content -LiteralPath "$candidate.sha256" -Value ("0" * 64) -Encoding Ascii
    $null = @(& $fakeResolver -Kind mcp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127 -and -not (Test-Path -LiteralPath $fakeLog)) "MCP resolver executed a candidate with a bad sidecar"

    Write-Sidecar $candidate
    $env:SIMPLE_WRAPPER_FAKE_MODE = "mcp-error"
    $null = @(& $fakeResolver -Kind mcp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127) "MCP resolver accepted an error response containing uncorrelated success text"

    $env:SIMPLE_WRAPPER_FAKE_MODE = "mcp-good"
    $resolved = @(& $fakeResolver -Kind mcp)
    Assert-Contract ($LASTEXITCODE -eq 0 -and $resolved.Count -eq 1) "MCP fake candidate was not admitted"
    $oldHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $candidate).Hash.ToLowerInvariant()
    Assert-Contract (Test-Path -LiteralPath (Join-Path $fakeRoot ".simple\cache\mcp-probe\mcp-$oldHash-windows-native-v1.stamp")) "MCP fake admission did not write its content-addressed stamp"

    Copy-Item -LiteralPath $bad -Destination $candidate -Force
    Write-Sidecar $candidate
    $env:SIMPLE_WRAPPER_FAKE_MODE = "mcp-error"
    $null = @(& $fakeResolver -Kind mcp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127) "MCP resolver reused a stale stamp after candidate replacement"

    Copy-Item -LiteralPath $good -Destination $candidate -Force
    Write-Sidecar $candidate
    $env:SIMPLE_WRAPPER_FAKE_MODE = "mcp-good"
    $env:SIMPLE_MCP_NATIVE = Join-Path $temp "missing.exe"
    $null = @(& $fakeResolver -Kind mcp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127) "MCP explicit override fell through to a valid default candidate"

    $lspCandidate = Join-Path $fakeRelease "simple_lsp_mcp_server.exe"
    Copy-Item -LiteralPath $bad -Destination $lspCandidate
    Write-Sidecar $lspCandidate
    $env:SIMPLE_LSP_MCP_NATIVE = $lspCandidate
    $env:SIMPLE_WRAPPER_FAKE_MODE = "lsp-error"
    $null = @(& $fakeResolver -Kind lsp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127) "LSP resolver accepted a correlated Missing tool name error"

    Copy-Item -LiteralPath $good -Destination $lspCandidate -Force
    Write-Sidecar $lspCandidate
    $env:SIMPLE_WRAPPER_FAKE_MODE = "lsp-good"
    $env:SIMPLE_LSP_MCP_NATIVE = Join-Path $temp "missing-lsp.exe"
    $null = @(& $fakeResolver -Kind lsp 2>$null)
    Assert-Contract ($LASTEXITCODE -eq 127) "LSP explicit override fell through to a valid default candidate"
} finally {
    $env:SIMPLE_MCP_NATIVE = $savedMcp
    $env:SIMPLE_LSP_MCP_NATIVE = $savedLsp
    $env:SIMPLE_WRAPPER_FAKE_MODE = $savedFakeMode
    $env:SIMPLE_WRAPPER_FAKE_LOG = $savedFakeLog
    Remove-Item -LiteralPath $temp -Recurse -Force -ErrorAction SilentlyContinue
}

Write-Output "windows_tool_wrapper_contract=pass"
