param(
    [string]$BuildDir = "build\tmp\windows_simple_cmd_launcher_health",
    [string]$ReportPath = "",
    [int]$TimeoutSecs = 30
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)

function Resolve-RepoPath([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path)) {
        return $path
    }
    if ([System.IO.Path]::IsPathRooted($path)) {
        return $path
    }
    return Join-Path $repoRoot $path
}

$BuildDir = Resolve-RepoPath $BuildDir
if ([string]::IsNullOrWhiteSpace($ReportPath)) {
    $ReportPath = Join-Path $BuildDir "report.md"
}
$ReportPath = Resolve-RepoPath $ReportPath

$EvidencePath = Join-Path $BuildDir "evidence.env"
$ProofPath = Join-Path $BuildDir "bin_simple_cmd_source_probe.env"
$SourceOutPath = Join-Path $BuildDir "bin_simple_cmd_source_probe.out"
$VersionOutPath = Join-Path $BuildDir "bin_simple_cmd_version.out"
$SimpleCmd = Resolve-RepoPath "bin\simple.cmd"
$Entry = Resolve-RepoPath "src\os\hosted\hosted_win32_mdi_probe.spl"

function Add-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
}

function Write-Rows([string]$path, $rows) {
    $dir = Split-Path -Parent $path
    if (-not [string]::IsNullOrWhiteSpace($dir)) {
        New-Item -ItemType Directory -Force -Path $dir | Out-Null
    }
    Set-Content -LiteralPath $path -Value $rows -Encoding utf8
}

function Read-Field([string]$path, [string]$key) {
    if (-not (Test-Path -LiteralPath $path)) { return "" }
    $prefix = "$key="
    foreach ($line in Get-Content -LiteralPath $path) {
        $line = $line.TrimStart([char]0xfeff)
        if ($line.StartsWith($prefix)) { return $line.Substring($prefix.Length) }
    }
    return ""
}

function Invoke-Cmd([string[]]$arguments, [string]$stdoutPath, [int]$timeoutSecs) {
    $startInfo = New-Object System.Diagnostics.ProcessStartInfo
    $startInfo.FileName = "cmd.exe"
    $cmdArgs = New-Object System.Collections.Generic.List[string]
    $cmdArgs.Add("/c") | Out-Null
    $cmdArgs.Add($SimpleCmd) | Out-Null
    foreach ($arg in $arguments) { $cmdArgs.Add($arg) | Out-Null }
    $startInfo.Arguments = ($cmdArgs | ForEach-Object {
        if ($_ -match '[\s"]') { '"' + $_.Replace('"', '\"') + '"' } else { $_ }
    }) -join " "
    $startInfo.WorkingDirectory = $repoRoot
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.Environment["SIMPLE_HOME"] = $repoRoot
    $startInfo.Environment["SIMPLE_WIN32_MDI_PROOF_PATH"] = $ProofPath
    $startInfo.Environment["SIMPLE_WIN32_MDI_HOLD_MS"] = "100"
    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $startInfo
    [void]$process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    if (-not $process.WaitForExit($timeoutSecs * 1000)) {
        try { $process.Kill($true) } catch { try { $process.Kill() } catch {} }
        Set-Content -LiteralPath $stdoutPath -Value ($stdoutTask.Result + "`n" + $stderrTask.Result + "`ntimed out") -Encoding utf8
        return 124
    }
    Set-Content -LiteralPath $stdoutPath -Value ($stdoutTask.Result + "`n" + $stderrTask.Result) -Encoding utf8
    return $process.ExitCode
}

function Write-Report {
    $report = New-Object System.Collections.Generic.List[string]
    $report.Add("# Windows simple.cmd Launcher Health") | Out-Null
    $report.Add("") | Out-Null
    $report.Add("## Raw Evidence") | Out-Null
    $report.Add("") | Out-Null
    if (Test-Path -LiteralPath $EvidencePath) {
        foreach ($line in Get-Content -LiteralPath $EvidencePath) { $report.Add("- $line") | Out-Null }
    }
    if (Test-Path -LiteralPath $ProofPath) {
        $report.Add("") | Out-Null
        $report.Add("## Source Probe Proof") | Out-Null
        foreach ($line in Get-Content -LiteralPath $ProofPath) { $report.Add("- $line") | Out-Null }
    }
    Write-Rows $ReportPath $report
}

New-Item -ItemType Directory -Force -Path $BuildDir | Out-Null
Remove-Item -LiteralPath $EvidencePath, $ProofPath, $SourceOutPath, $VersionOutPath, $ReportPath -Force -ErrorAction SilentlyContinue

$failures = New-Object System.Collections.Generic.List[string]
$sourceExit = Invoke-Cmd @($Entry, "--interpret") $SourceOutPath $TimeoutSecs
$versionExit = Invoke-Cmd @("--version") $VersionOutPath $TimeoutSecs
$versionText = if (Test-Path -LiteralPath $VersionOutPath) { ((Get-Content -LiteralPath $VersionOutPath -TotalCount 1) -join "").Trim() } else { "" }

if ($sourceExit -ne 0) { $failures.Add("source-launch") | Out-Null }
if (-not (Test-Path -LiteralPath $ProofPath)) { $failures.Add("source-proof") | Out-Null }
if ((Read-Field $ProofPath "status") -ne "pass") { $failures.Add("probe-status") | Out-Null }
if ((Read-Field $ProofPath "backend") -ne "win32-native") { $failures.Add("probe-backend") | Out-Null }
if ((Read-Field $ProofPath "drag_moved") -ne "true") { $failures.Add("probe-drag") | Out-Null }
if ((Read-Field $ProofPath "focus_cycle_changed") -ne "true") { $failures.Add("probe-focus") | Out-Null }
if ((Read-Field $ProofPath "rendered_titlebar_css_applied") -ne "true") { $failures.Add("probe-titlebar-css") | Out-Null }
if ($versionExit -ne 0 -or $versionText -notmatch '^Simple v') { $failures.Add("version") | Out-Null }

$status = if ($failures.Count -eq 0) { "pass" } else { "fail" }
$reason = if ($failures.Count -eq 0) { "pass" } else { $failures -join "," }

$rows = New-Object System.Collections.Generic.List[string]
Add-Row $rows "windows_simple_cmd_launcher_health_status" $status
Add-Row $rows "windows_simple_cmd_launcher_health_reason" $reason
Add-Row $rows "windows_simple_cmd_launcher_health_source_exit_code" "$sourceExit"
Add-Row $rows "windows_simple_cmd_launcher_health_version_exit_code" "$versionExit"
Add-Row $rows "windows_simple_cmd_launcher_health_version" $versionText
Add-Row $rows "windows_simple_cmd_launcher_health_simple_cmd" $SimpleCmd
Add-Row $rows "windows_simple_cmd_launcher_health_entry" $Entry
Add-Row $rows "windows_simple_cmd_launcher_health_proof_path" $ProofPath
Add-Row $rows "windows_simple_cmd_launcher_health_source_output_path" $SourceOutPath
Add-Row $rows "windows_simple_cmd_launcher_health_version_output_path" $VersionOutPath
Add-Row $rows "windows_simple_cmd_launcher_health_report_path" $ReportPath
Add-Row $rows "windows_simple_cmd_launcher_health_probe_status" (Read-Field $ProofPath "status")
Add-Row $rows "windows_simple_cmd_launcher_health_probe_backend" (Read-Field $ProofPath "backend")
Add-Row $rows "windows_simple_cmd_launcher_health_probe_drag_moved" (Read-Field $ProofPath "drag_moved")
Add-Row $rows "windows_simple_cmd_launcher_health_probe_focus_cycle_changed" (Read-Field $ProofPath "focus_cycle_changed")
Add-Row $rows "windows_simple_cmd_launcher_health_probe_rendered_titlebar_css_applied" (Read-Field $ProofPath "rendered_titlebar_css_applied")
Add-Row $rows "windows_simple_cmd_launcher_health_probe_rendered_titlebar_css_pixels" (Read-Field $ProofPath "rendered_titlebar_css_pixels")
Write-Rows $EvidencePath $rows
Write-Report
Get-Content -LiteralPath $EvidencePath

if ($status -eq "pass") { exit 0 }
exit 1
