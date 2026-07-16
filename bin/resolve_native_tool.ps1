[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [ValidateSet("simple", "mcp", "lsp")]
    [string]$Kind
)

$ErrorActionPreference = "Stop"
$BinDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$RepoRoot = Split-Path -Parent $BinDir
$ContractVersion = "windows-native-v1"

function Write-Failure([string]$Message) {
    [Console]::Error.WriteLine($Message)
}

function Invoke-BoundedProbe([string]$Path, [string]$Arguments, [string]$InputText) {
    $start = New-Object System.Diagnostics.ProcessStartInfo
    $start.FileName = $Path
    $start.Arguments = $Arguments
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.RedirectStandardInput = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true

    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $start
    if (-not $process.Start()) {
        return $null
    }
    $stdout = $process.StandardOutput.ReadToEndAsync()
    $stderr = $process.StandardError.ReadToEndAsync()
    if ($InputText.Length -gt 0) {
        $process.StandardInput.Write($InputText)
    }
    $process.StandardInput.Close()
    if (-not $process.WaitForExit(5000)) {
        try { $process.Kill() } catch {}
        return $null
    }
    [PSCustomObject]@{
        ExitCode = $process.ExitCode
        Output = $stdout.GetAwaiter().GetResult() + $stderr.GetAwaiter().GetResult()
    }
}

function Test-NativeProbe([string]$Path) {
    if ($Kind -eq "simple") {
        $probe = Invoke-BoundedProbe $Path "--version" ""
        return $null -ne $probe -and $probe.ExitCode -eq 0 -and
            $probe.Output -match "Simple" -and
            $probe.Output -notmatch "(?i)bootstrap seed|Rust-built|debug build"
    }

    if ($Kind -eq "mcp") {
        $inputText = '{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"windows-wrapper-probe","version":"1"}}}' + "`n" +
            '{"jsonrpc":"2.0","method":"notifications/initialized","params":{}}' + "`n" +
            '{"jsonrpc":"2.0","id":"2","method":"tools/list","params":{}}' + "`n" +
            '{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"simple_pipe","arguments":{"surface":"spipe"}}}' + "`n"
        $probe = Invoke-BoundedProbe $Path "" $inputText
        return $null -ne $probe -and $probe.ExitCode -eq 0 -and
            $probe.Output -match '"simple_pipe"' -and
            $probe.Output -match '"id"\s*:\s*3[^\r\n]*"result"\s*:' -and
            $probe.Output -match 'spipe: linked' -and
            $probe.Output -notmatch '"id"\s*:\s*3[^\r\n]*"error"\s*:'
    }

    $inputText = '{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"windows-wrapper-probe","version":"1"}}}' + "`n" +
        '{"jsonrpc":"2.0","id":"2","method":"tools/list","params":{}}' + "`n" +
        '{"jsonrpc":"2.0","id":"lsp-call-probe","method":"tools/call","params":{"name":"lsp_symbols","arguments":{"file":"src/app/simple_lsp_mcp/main.spl"}}}' + "`n"
    $probe = Invoke-BoundedProbe $Path "" $inputText
    $null -ne $probe -and $probe.ExitCode -eq 0 -and
        $probe.Output -match '"lsp_definition"' -and
        $probe.Output -match '"id"\s*:\s*"lsp-call-probe"[^\r\n]*"result"\s*:' -and
        $probe.Output -notmatch '"id"\s*:\s*"lsp-call-probe"[^\r\n]*"error"\s*:' -and
        $probe.Output -notmatch 'Missing tool name'
}

$fileName = switch ($Kind) {
    "simple" { "simple.exe" }
    "mcp" { "simple_mcp_server.exe" }
    default { "simple_lsp_mcp_server.exe" }
}
$override = switch ($Kind) {
    "simple" { $env:SIMPLE_BINARY }
    "mcp" { $env:SIMPLE_MCP_NATIVE }
    default { $env:SIMPLE_LSP_MCP_NATIVE }
}

$candidates = @()
if (-not [string]::IsNullOrWhiteSpace($override)) {
    $candidates = @($override)
} else {
    foreach ($triple in @("x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu", "aarch64-pc-windows-msvc", "aarch64-pc-windows-gnu")) {
        $candidates += Join-Path $BinDir "release\$triple\$fileName"
    }
    $candidates += Join-Path $BinDir "release\$fileName"
}

foreach ($candidate in $candidates) {
    if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) { continue }
    $item = Get-Item -LiteralPath $candidate
    if ($item.Length -le 0) { continue }
    $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $candidate).Hash.ToLowerInvariant()
    if ($Kind -ne "simple") {
        $sidecar = "$candidate.sha256"
        if (-not (Test-Path -LiteralPath $sidecar -PathType Leaf)) { continue }
        $expected = ((Get-Content -LiteralPath $sidecar -TotalCount 1).Trim() -split '\s+')[0].ToLowerInvariant()
        if ($expected -notmatch '^[0-9a-f]{64}$' -or $actual -ne $expected) { continue }
    }

    $cacheDir = Join-Path $RepoRoot ".simple\cache\mcp-probe"
    $stamp = Join-Path $cacheDir "$Kind-$actual-$ContractVersion.stamp"
    if (-not (Test-Path -LiteralPath $stamp)) {
        if (-not (Test-NativeProbe $candidate)) { continue }
        New-Item -ItemType Directory -Force -Path $cacheDir | Out-Null
        $tempStamp = "$stamp.$PID.tmp"
        [IO.File]::WriteAllText($tempStamp, "ok`n")
        Move-Item -LiteralPath $tempStamp -Destination $stamp -Force
    }
    Write-Output $item.FullName
    exit 0
}

Write-Failure "error: no hash-matched, protocol-admitted $Kind native artifact found"
exit 127
