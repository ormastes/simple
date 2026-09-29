$ErrorActionPreference = 'Stop'
$sandbox = Join-Path ([IO.Path]::GetTempPath()) ('codex-launcher-' + [guid]::NewGuid())
New-Item -ItemType Directory -Path $sandbox | Out-Null
$fixture = Join-Path $sandbox 'fake codex.cjs'
[IO.File]::WriteAllText($fixture, 'process.stdout.write(JSON.stringify(process.argv.slice(2))); process.exit(Number(process.env.CODEX_LAUNCHER_TEST_EXIT || 0));')
$destination = Join-Path $sandbox 'installed launcher'
& (Join-Path $PSScriptRoot '../install-windows-codex-launcher.ps1') -CodexEntry $fixture -InstallDirectory $destination -NoPathUpdate
$cases = @(
    @{ InputArgs = @(); Expected = @('--no-daemon') },
    @{ InputArgs = @('resume', 'session with spaces'); Expected = @('--no-daemon', 'resume', 'session with spaces') },
    @{ InputArgs = @('--no-daemon', '--version'); Expected = @('--no-daemon', '--version') },
    @{ InputArgs = @('app-server', '--help'); Expected = @('app-server', '--help') },
    @{ InputArgs = @('--remote=example', '--help'); Expected = @('--remote=example', '--help') }
)
$checks = 0
foreach ($name in @('codex.cmd', 'codex.ps1')) {
    $launcher = Join-Path $destination $name
    foreach ($case in $cases) {
        $forward = $case.InputArgs
        $result = & $launcher @forward
        if ($LASTEXITCODE -ne 0) { throw "$name failed: $LASTEXITCODE" }
        $actual = @($result | ConvertFrom-Json) | ConvertTo-Json -Compress -AsArray
        $expected = $case.Expected | ConvertTo-Json -Compress -AsArray
        if ($actual -cne $expected) { throw "$name argument mismatch: $actual versus $expected" }
        $checks++
    }
    $priorExit = $env:CODEX_LAUNCHER_TEST_EXIT
    try {
        $env:CODEX_LAUNCHER_TEST_EXIT = '17'
        & $launcher --version | Out-Null
        if ($LASTEXITCODE -ne 17) { throw "$name lost child exit status" }
        $checks++
    } finally {
        $env:CODEX_LAUNCHER_TEST_EXIT = $priorExit
    }
}
Write-Output "PASS: $checks launcher checks; fixture retained at $sandbox"
