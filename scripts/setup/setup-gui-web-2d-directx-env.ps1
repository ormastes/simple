param(
    [ValidateSet("--check", "--browser-backing", "--print-install")]
    [string]$Mode = "--check",
    [string]$BuildDir = "build\gui-web-2d-directx-env-windows",
    [string]$EvidencePath = "",
    [string]$HtmlPath = "test\fixtures\html_css\generated_gui_vulkan_renderdoc_fixture.html",
    [int]$Width = 1280,
    [int]$Height = 720,
    [int]$TimeoutSecs = 90,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$RemainingArgs = @()
)

$ErrorActionPreference = "Stop"

if ($RemainingArgs -contains "--print-install" -or $MyInvocation.Line -match '(^|\s)--print-install(\s|$)') {
    $Mode = "--print-install"
} elseif ($RemainingArgs -contains "--browser-backing" -or $MyInvocation.Line -match '(^|\s)--browser-backing(\s|$)') {
    $Mode = "--browser-backing"
} elseif ($RemainingArgs -contains "--check" -or $MyInvocation.Line -match '(^|\s)--check(\s|$)') {
    $Mode = "--check"
}

function Write-Install {
    @"
Windows PowerShell:
  winget install --id Google.Chrome --accept-source-agreements --accept-package-agreements
  winget install --id OpenJS.NodeJS.LTS --accept-source-agreements --accept-package-agreements
  npm install -g electron

Required checks:
  Get-Command dxdiag
  Get-Command cargo
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --check
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --browser-backing
"@
}

function Command-Source([string]$name) {
    $cmd = Get-Command $name -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    return ""
}

function Existing-Path([string[]]$paths) {
    foreach ($path in $paths) {
        if (-not [string]::IsNullOrWhiteSpace($path) -and (Test-Path -LiteralPath $path)) { return $path }
    }
    return ""
}

function Candidate-Path([string]$base, [string]$child) {
    if ([string]::IsNullOrWhiteSpace($base)) { return "" }
    return Join-Path $base $child
}

function Tool-Source([string[]]$names, [string[]]$paths = @()) {
    foreach ($name in $names) {
        $source = Command-Source $name
        if ($source -ne "") { return $source }
    }
    return Existing-Path $paths
}

function Tool-Status([string]$source) {
    if ($source -ne "") { return "pass" }
    return "missing"
}

function Add-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
}

function Add-EnvRows($rows, [string[]]$lines) {
    foreach ($line in $lines) {
        if ([string]::IsNullOrWhiteSpace($line)) { continue }
        if ($line -notmatch '^[A-Za-z0-9_]+=') { continue }
        $rows.Add($line) | Out-Null
    }
}

function Read-KeyValueFile([string]$path) {
    $map = @{}
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $map }
    Get-Content -LiteralPath $path | ForEach-Object {
        $line = $_.Trim()
        if ($line -eq "" -or $line.StartsWith("#")) { return }
        $idx = $line.IndexOf("=")
        if ($idx -le 0) { return }
        $map[$line.Substring(0, $idx)] = $line.Substring($idx + 1)
    }
    return $map
}

function Value-Or($map, [string[]]$keys, [string]$defaultValue = "") {
    foreach ($key in $keys) {
        if ($map.ContainsKey($key) -and "$($map[$key])" -ne "") { return "$($map[$key])" }
    }
    return $defaultValue
}

function Json-Value-Or([string]$path, [string[]]$keys, [string]$defaultValue = "") {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $defaultValue }
    try {
        $json = Get-Content -LiteralPath $path -Raw | ConvertFrom-Json
        foreach ($key in $keys) {
            $value = $json
            foreach ($part in $key.Split(".")) {
                if ($null -eq $value) { break }
                $value = $value.$part
            }
            if ($null -ne $value -and "$value" -ne "") { return "$value" }
        }
    } catch {
        return $defaultValue
    }
    return $defaultValue
}

function Proof-Status([string]$proofPath, [string]$argbPath) {
    $status = Json-Value-Or $proofPath @("status") ""
    $written = Json-Value-Or $proofPath @("captured_argb_written") ""
    if ($status -eq "pass" -and ($written -eq "True" -or $written -eq "true") -and (Test-Path -LiteralPath $argbPath)) {
        return "pass"
    }
    if (-not (Test-Path -LiteralPath $argbPath)) { return "missing" }
    if ($status -ne "") { return $status }
    return "unknown"
}

function Wait-ForFile([string]$path, [int]$timeoutMs = 5000) {
    $deadline = (Get-Date).AddMilliseconds($timeoutMs)
    while ((Get-Date) -lt $deadline) {
        if (Test-Path -LiteralPath $path) { return $true }
        Start-Sleep -Milliseconds 100
    }
    return (Test-Path -LiteralPath $path)
}

function Quote-Arg([string]$arg) {
    if ($arg -match '[\s"]') { return '"' + ($arg -replace '"', '\"') + '"' }
    return $arg
}

function Invoke-ProcessBound([string]$exe, [string[]]$argList, [string]$stdoutPath, [string]$stderrPath, [int]$timeoutSecs, [hashtable]$envMap = @{}) {
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $exe
    $psi.Arguments = (($argList | ForEach-Object { Quote-Arg $_ }) -join " ")
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.UseShellExecute = $false
    $psi.CreateNoWindow = $true
    foreach ($key in $envMap.Keys) {
        $psi.Environment[$key] = "$($envMap[$key])"
    }
    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $psi
    [void]$process.Start()
    if (-not $process.WaitForExit($timeoutSecs * 1000)) {
        try { $process.Kill() } catch {}
        "" | Set-Content -Encoding ASCII -Path $stdoutPath
        "timeout" | Set-Content -Encoding ASCII -Path $stderrPath
        return 124
    }
    $process.StandardOutput.ReadToEnd() | Set-Content -Encoding ASCII -Path $stdoutPath
    $process.StandardError.ReadToEnd() | Set-Content -Encoding ASCII -Path $stderrPath
    return $process.ExitCode
}

function Invoke-Capture([string]$exe, [string[]]$argList, [hashtable]$envMap, [string]$stdoutPath, [string]$stderrPath, [int]$timeoutSecs) {
    return Invoke-ProcessBound $exe $argList $stdoutPath $stderrPath $timeoutSecs $envMap
}

if ($Mode -eq "--print-install") {
    Write-Install
    exit 0
}

if ([string]::IsNullOrWhiteSpace($EvidencePath)) {
    $EvidencePath = Join-Path $BuildDir "evidence.env"
}

$RootDir = Resolve-Path (Join-Path $PSScriptRoot "..\..")
$BuildFullDir = if ([System.IO.Path]::IsPathRooted($BuildDir)) { $BuildDir } else { Join-Path $RootDir $BuildDir }
$EvidencePath = if ([System.IO.Path]::IsPathRooted($EvidencePath)) { $EvidencePath } else { Join-Path $RootDir $EvidencePath }
$HtmlFullPath = if ([System.IO.Path]::IsPathRooted($HtmlPath)) { $HtmlPath } else { Join-Path $RootDir $HtmlPath }

New-Item -ItemType Directory -Force -Path $BuildFullDir | Out-Null
New-Item -ItemType Directory -Force -Path (Split-Path -Parent $EvidencePath) | Out-Null

$rows = New-Object System.Collections.Generic.List[string]
$NodeSource = Command-Source "node"
$CargoSource = Command-Source "cargo"
$DxdiagSource = Command-Source "dxdiag"
$ElectronCaptureScript = Join-Path $RootDir "tools\electron-live-bitmap\capture_html_argb.js"
$ChromeCaptureScript = Join-Path $RootDir "tools\chrome-live-bitmap\capture_html_argb.js"
$DirectxBackingScript = Join-Path $RootDir "scripts\check\gui-web-2d-directx-browser-backing-status.js"
$chromeSource = Tool-Source @("chrome", "chrome.exe", "msedge", "msedge.exe") @(
    (Candidate-Path $env:ProgramFiles "Google\Chrome\Application\chrome.exe"),
    (Candidate-Path ${env:ProgramFiles(x86)} "Google\Chrome\Application\chrome.exe"),
    (Candidate-Path $env:LocalAppData "Google\Chrome\Application\chrome.exe"),
    (Candidate-Path $env:ProgramFiles "Microsoft\Edge\Application\msedge.exe"),
    (Candidate-Path ${env:ProgramFiles(x86)} "Microsoft\Edge\Application\msedge.exe")
)
$electronSource = Existing-Path @(
    (Join-Path $RootDir "tools\electron-shell\node_modules\electron\dist\electron.exe")
)
if ($electronSource -eq "") {
    $electronSource = Tool-Source @("electron.cmd", "electron.exe", "electron") @()
}

$directxFlags = @("--no-sandbox", "--disable-gpu-sandbox", "--use-angle=d3d11", "--enable-gpu-rasterization", "--enable-zero-copy")

Add-Row $rows "gui_web_2d_directx_mode" $(if ($Mode -eq "--browser-backing") { "windows-browser-backing" } else { "windows-check" })
Add-Row $rows "gui_web_2d_directx_build_dir" "$BuildFullDir"
Add-Row $rows "gui_web_2d_directx_evidence_path" "$EvidencePath"
Add-Row $rows "gui_web_2d_directx_windows_setup_wrapper" "scripts/setup/setup-gui-web-2d-directx-env.ps1"
Add-Row $rows "gui_web_2d_directx_html_path" "$HtmlFullPath"
Add-Row $rows "gui_web_2d_directx_width" "$Width"
Add-Row $rows "gui_web_2d_directx_height" "$Height"
Add-Row $rows "gui_web_2d_directx_timeout_secs" "$TimeoutSecs"
Add-Row $rows "gui_web_2d_directx_dxdiag_status" (Tool-Status $DxdiagSource)
Add-Row $rows "gui_web_2d_directx_dxdiag_path" "$DxdiagSource"
Add-Row $rows "gui_web_2d_directx_cargo_status" (Tool-Status $CargoSource)
Add-Row $rows "gui_web_2d_directx_cargo_path" "$CargoSource"
Add-Row $rows "gui_web_2d_directx_node_status" (Tool-Status $NodeSource)
Add-Row $rows "gui_web_2d_directx_node_path" "$NodeSource"
Add-Row $rows "gui_web_2d_directx_electron_status" (Tool-Status $electronSource)
Add-Row $rows "gui_web_2d_directx_electron_path" "$electronSource"
Add-Row $rows "gui_web_2d_directx_chrome_status" (Tool-Status $chromeSource)
Add-Row $rows "gui_web_2d_directx_chrome_path" "$chromeSource"
Add-Row $rows "gui_web_2d_directx_requested_api" "directx"
Add-Row $rows "gui_web_2d_directx_requested_angle" "d3d11"
Add-Row $rows "gui_web_2d_directx_launch_flags" ($directxFlags -join " ")

$nativeDir = Join-Path $BuildFullDir "directx-native"
New-Item -ItemType Directory -Force -Path $nativeDir | Out-Null
$nativeOut = Join-Path $nativeDir "stdout.env"
$nativeErr = Join-Path $nativeDir "stderr.log"
$nativeHarness = Join-Path $RootDir "build\directx\native_readback_probe.exe"
$nativeStatus = "unavailable"
$nativeReason = "missing-cargo-or-directx-native-readback-harness"
$nativeSource = "not_device_readback"
$nativeHandle = "0"
$nativeExpected = "0"
$nativeActual = "-1"
$nativeCode = "missing"
if (Test-Path -LiteralPath $nativeHarness) {
    $nativeCode = Invoke-ProcessBound $nativeHarness @() $nativeOut $nativeErr $TimeoutSecs
} elseif ($CargoSource -ne "") {
    $nativeCode = Invoke-ProcessBound $CargoSource @("run", "--manifest-path", "src/runtime/hosted/Cargo.toml", "--features", "win32-real", "--example", "directx_native_readback_probe") $nativeOut $nativeErr $TimeoutSecs
} else {
    "" | Set-Content -Encoding ASCII -Path $nativeOut
    "missing cargo and native harness" | Set-Content -Encoding ASCII -Path $nativeErr
}
if ("$nativeCode" -eq "124") {
    $nativeReason = "timeout-after-${TimeoutSecs}s"
} elseif ("$nativeCode" -eq "0" -and (Test-Path -LiteralPath $nativeOut)) {
    $native = Read-KeyValueFile $nativeOut
    $nativeStatus = Value-Or $native @("directx_native_readback_status") "missing"
    $nativeReason = Value-Or $native @("directx_native_readback_reason") ""
    $nativeSource = Value-Or $native @("directx_native_readback_source") ""
    $nativeHandle = Value-Or $native @("directx_native_readback_backend_handle") "0"
    $nativeExpected = Value-Or $native @("directx_native_readback_expected_checksum") "0"
    $nativeActual = Value-Or $native @("directx_native_readback_actual_checksum") "-1"
} elseif ("$nativeCode" -ne "missing") {
    $nativeReason = "directx-native-readback-probe-failed"
}
$nativeGate = "unavailable"
if ($nativeStatus -eq "pass" -and $nativeSource -eq "device_readback" -and $nativeHandle -match '^[1-9][0-9]*$' -and $nativeExpected -match '^[1-9][0-9]*$' -and $nativeActual -eq $nativeExpected) {
    $nativeGate = "pass"
} elseif ($nativeStatus -ne "unavailable") {
    $nativeGate = "fail"
}
Add-Row $rows "gui_web_2d_directx_native_readback_exit_code" "$nativeCode"
Add-Row $rows "gui_web_2d_directx_native_readback_status" "$nativeStatus"
Add-Row $rows "gui_web_2d_directx_native_readback_reason" "$nativeReason"
Add-Row $rows "gui_web_2d_directx_native_readback_source" "$nativeSource"
Add-Row $rows "gui_web_2d_directx_native_readback_backend_handle" "$nativeHandle"
Add-Row $rows "gui_web_2d_directx_native_readback_expected_checksum" "$nativeExpected"
Add-Row $rows "gui_web_2d_directx_native_readback_actual_checksum" "$nativeActual"
Add-Row $rows "gui_web_2d_directx_native_readback_gate_status" "$nativeGate"
Add-Row $rows "gui_web_2d_directx_native_readback_stdout" "$nativeOut"
Add-Row $rows "gui_web_2d_directx_native_readback_stderr" "$nativeErr"

$browserBackingStatus = "not-run"
if ($Mode -eq "--browser-backing") {
    $electronArgb = Join-Path $BuildFullDir "electron_argb.json"
    $electronProof = Join-Path $BuildFullDir "electron_argb_proof.json"
    $electronOut = Join-Path $BuildFullDir "electron.out"
    $electronLog = Join-Path $BuildFullDir "electron.log"
    if ($electronSource -ne "" -and (Test-Path -LiteralPath $ElectronCaptureScript)) {
        $electronEnv = @{
            ELECTRON_CAPTURE_HTML = "$HtmlFullPath"
            ELECTRON_CAPTURE_WIDTH = "$Width"
            ELECTRON_CAPTURE_HEIGHT = "$Height"
            ELECTRON_CAPTURE_OUTPUT = "$electronArgb"
            ELECTRON_CAPTURE_PROOF_PATH = "$electronProof"
            ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT = "43217"
            ELECTRON_CAPTURE_SETTLE_MS = "1000"
            ELECTRON_ENABLE_LOGGING = "1"
        }
        $electronCode = Invoke-Capture $electronSource ($directxFlags + @("$ElectronCaptureScript")) $electronEnv $electronOut $electronLog $TimeoutSecs
        Wait-ForFile $electronProof | Out-Null
        Add-Row $rows "gui_web_2d_directx_electron_exit_code" "$electronCode"
        Add-Row $rows "gui_web_2d_directx_electron_stdout" "$electronOut"
        Add-Row $rows "gui_web_2d_directx_electron_log" "$electronLog"
        Add-Row $rows "gui_web_2d_directx_electron_argb_path" "$electronArgb"
        Add-Row $rows "gui_web_2d_directx_electron_argb_proof" "$electronProof"
        Add-Row $rows "gui_web_2d_directx_electron_argb_status" (Proof-Status $electronProof $electronArgb)
        Add-Row $rows "gui_web_2d_directx_electron_argb_checksum" (Json-Value-Or $electronProof @("checksum", "captured_argb_sha256") "")
        if ($NodeSource -ne "" -and (Test-Path -LiteralPath $DirectxBackingScript)) {
            Add-EnvRows $rows @(& $NodeSource "$DirectxBackingScript" "$electronProof" "gui_web_2d_directx_electron")
        }
    } else {
        Add-Row $rows "gui_web_2d_directx_electron_argb_status" "unavailable"
        Add-Row $rows "gui_web_2d_directx_electron_browser_backing_status" "unavailable"
        Add-Row $rows "gui_web_2d_directx_electron_browser_backing_reason" "missing-electron-or-capture-script"
    }

    $chromeArgb = Join-Path $BuildFullDir "chrome_argb.json"
    $chromeProof = Join-Path $BuildFullDir "chrome_argb_proof.json"
    $chromeGeometry = Join-Path $BuildFullDir "chrome_geometry.json"
    $chromeOut = Join-Path $BuildFullDir "chrome_argb.out"
    $chromeLog = Join-Path $BuildFullDir "chrome_argb.log"
    if ($chromeSource -ne "" -and $NodeSource -ne "" -and (Test-Path -LiteralPath $ChromeCaptureScript)) {
        $chromeEnv = @{
            CHROME_CAPTURE_HTML = "$HtmlFullPath"
            CHROME_CAPTURE_WIDTH = "$Width"
            CHROME_CAPTURE_HEIGHT = "$Height"
            CHROME_CAPTURE_OUTPUT = "$chromeArgb"
            CHROME_CAPTURE_PROOF_PATH = "$chromeProof"
            CHROME_CAPTURE_GEOMETRY_OUTPUT = "$chromeGeometry"
            CHROME_CAPTURE_BIN = "$chromeSource"
            CHROME_CAPTURE_DISABLE_GPU = "false"
            CHROME_CAPTURE_EXTRA_ARGS = ($directxFlags -join " ")
            CHROME_CAPTURE_TIMEOUT_MS = "$($TimeoutSecs * 1000)"
        }
        $chromeCode = Invoke-Capture $NodeSource @("$ChromeCaptureScript") $chromeEnv $chromeOut $chromeLog $TimeoutSecs
        Wait-ForFile $chromeProof | Out-Null
        Add-Row $rows "gui_web_2d_directx_chrome_argb_exit_code" "$chromeCode"
        Add-Row $rows "gui_web_2d_directx_chrome_argb_stdout" "$chromeOut"
        Add-Row $rows "gui_web_2d_directx_chrome_argb_log" "$chromeLog"
        Add-Row $rows "gui_web_2d_directx_chrome_argb_path" "$chromeArgb"
        Add-Row $rows "gui_web_2d_directx_chrome_argb_proof" "$chromeProof"
        Add-Row $rows "gui_web_2d_directx_chrome_geometry" "$chromeGeometry"
        Add-Row $rows "gui_web_2d_directx_chrome_argb_status" (Proof-Status $chromeProof $chromeArgb)
        Add-Row $rows "gui_web_2d_directx_chrome_argb_checksum" (Json-Value-Or $chromeProof @("checksum") "")
        if ($NodeSource -ne "" -and (Test-Path -LiteralPath $DirectxBackingScript)) {
            Add-EnvRows $rows @(& $NodeSource "$DirectxBackingScript" "$chromeProof" "gui_web_2d_directx_chrome")
        }
    } else {
        Add-Row $rows "gui_web_2d_directx_chrome_argb_status" "unavailable"
        Add-Row $rows "gui_web_2d_directx_chrome_browser_backing_status" "unavailable"
        Add-Row $rows "gui_web_2d_directx_chrome_browser_backing_reason" "missing-chrome-node-or-capture-script"
    }

    $electronBacking = ($rows | Where-Object { $_ -like "gui_web_2d_directx_electron_browser_backing_status=*" } | Select-Object -Last 1) -replace '^.*=', ''
    $chromeBacking = ($rows | Where-Object { $_ -like "gui_web_2d_directx_chrome_browser_backing_status=*" } | Select-Object -Last 1) -replace '^.*=', ''
    if ($nativeGate -eq "pass" -and $electronBacking -eq "pass" -and $chromeBacking -eq "pass") {
        $browserBackingStatus = "pass"
        Add-Row $rows "gui_web_2d_directx_browser_backing_status" "pass"
        Add-Row $rows "gui_web_2d_directx_browser_backing_reason" "native-d3d11-electron-chrome-pass"
    } else {
        $browserBackingStatus = "fail"
        Add-Row $rows "gui_web_2d_directx_browser_backing_status" "fail"
        Add-Row $rows "gui_web_2d_directx_browser_backing_reason" "native-or-browser-directx-proof-missing"
    }
} else {
    Add-Row $rows "gui_web_2d_directx_electron_browser_backing_status" "not-run"
    Add-Row $rows "gui_web_2d_directx_electron_browser_backing_reason" "check-only"
    Add-Row $rows "gui_web_2d_directx_chrome_browser_backing_status" "not-run"
    Add-Row $rows "gui_web_2d_directx_chrome_browser_backing_reason" "check-only"
    Add-Row $rows "gui_web_2d_directx_browser_backing_status" $(if ($nativeGate -eq "pass") { "native-only" } else { "unavailable" })
    Add-Row $rows "gui_web_2d_directx_browser_backing_reason" $(if ($nativeGate -eq "pass") { "browser-backing-not-run" } else { "native-d3d11-readback-not-proven" })
}

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
$rows | ForEach-Object { Write-Output $_ }

if (($Mode -eq "--check" -and $nativeGate -eq "pass") -or ($Mode -eq "--browser-backing" -and $browserBackingStatus -eq "pass")) {
    exit 0
}
exit 1
