# Installs a user-owned launcher, leaving npm's generated shims untouched.
[CmdletBinding()]
param(
    [string]$CodexEntry,
    [string]$InstallDirectory = (Join-Path $env:LOCALAPPDATA 'Simple\codex-cli'),
    [switch]$NoPathUpdate
)
$ErrorActionPreference = 'Stop'
if ($env:OS -ne 'Windows_NT') { throw 'This installer requires Windows.' }
Get-Command node -ErrorAction Stop | Out-Null
if (-not $CodexEntry) {
    $npmPrefix = (& npm.cmd prefix --global | Select-Object -Last 1)
    if ($LASTEXITCODE -ne 0) { throw 'Cannot locate the global npm prefix.' }
    $CodexEntry = Join-Path $npmPrefix 'node_modules\@openai\codex\bin\codex.js'
}
$CodexEntry = (Resolve-Path -LiteralPath $CodexEntry).Path
$InstallDirectory = [IO.Path]::GetFullPath($InstallDirectory)
$source = Join-Path $PSScriptRoot 'windows-codex'
New-Item -ItemType Directory -Path $InstallDirectory -Force | Out-Null
foreach ($name in @('codex.cmd', 'codex.ps1', 'launch.cjs')) {
    Copy-Item -LiteralPath (Join-Path $source $name) -Destination (Join-Path $InstallDirectory $name) -Force
}
$target = @{ entry = $CodexEntry } | ConvertTo-Json -Compress
[IO.File]::WriteAllText((Join-Path $InstallDirectory 'target.json'), $target)
if (-not $NoPathUpdate) {
    $userPath = [Environment]::GetEnvironmentVariable('Path', 'User')
    $remaining = @($userPath -split ';' | Where-Object { $_ -and $_.TrimEnd('\') -ine $InstallDirectory.TrimEnd('\') })
    [Environment]::SetEnvironmentVariable('Path', (@($InstallDirectory) + $remaining -join ';'), 'User')
    $env:Path = $InstallDirectory + ';' + $env:Path
}
Write-Output "Installed Windows Codex launcher: $InstallDirectory"
Write-Output 'New sessions use --no-daemon. Existing daemons are not stopped.'
Write-Output 'Open a new terminal; use where.exe codex to confirm this directory wins PATH lookup.'
