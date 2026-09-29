# Run on Windows with Git Bash and jq/curl installed. No network or credentials.
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../../..')).Path
$launcher = Join-Path $repo 'tools/mail-cli/bin/mail.cmd'
$config = Join-Path ([System.IO.Path]::GetTempPath()) ('mail launcher ' + [guid]::NewGuid() + '.json')
$originalBash = $env:MAIL_BASH
try {
    # --help must preserve a configuration argument containing spaces and avoid
    # creating that file. Using help also avoids a dependency on a real server.
    $output = & $launcher --help --config-file ($config.Replace('\', '/')) 2>&1
    if ($LASTEXITCODE -ne 0) { throw "Launcher help failed: $output" }
    if (($output -join "`n") -notmatch 'USAGE') { throw 'Missing CLI help' }
    if (Test-Path $config) { throw 'Help unexpectedly wrote configuration' }

    $env:MAIL_BASH = Join-Path ([System.IO.Path]::GetTempPath()) 'missing-mail-bash.exe'
    # Native stderr is expected for the negative case (Windows PowerShell).
    $ErrorActionPreference = 'Continue'
    $null = & $launcher --help 2>&1
    $ErrorActionPreference = 'Stop'
    if ($LASTEXITCODE -ne 127) { throw 'Invalid MAIL_BASH must fail with 127' }
    Write-Output 'PASS: Windows launcher help, spaced config path, missing Bash'
} finally {
    $env:MAIL_BASH = $originalBash
    Remove-Item -LiteralPath $config -Force -ErrorAction SilentlyContinue
}
