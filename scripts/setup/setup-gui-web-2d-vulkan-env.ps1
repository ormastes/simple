param(
    [ValidateSet("--check", "--run", "--renderdoc", "--print-install")]
    [string]$Mode = "--check",
    [string]$BuildDir = "build\gui-web-2d-vulkan-env-windows",
    [string]$EvidencePath = "",
    [string]$SimpleReadbackEvidencePath = "build\simpleos_multiconfig_live_evidence\vulkan-engine2d-readback-final.env",
    [string]$HtmlPath = "test\fixtures\html_css\generated_gui_vulkan_renderdoc_fixture.html",
    [int]$Width = 1280,
    [int]$Height = 720,
    [int]$TimeoutSecs = 45,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$RemainingArgs = @()
)

$ErrorActionPreference = "Stop"

if ($RemainingArgs -contains "--print-install" -or $MyInvocation.Line -match '(^|\s)--print-install(\s|$)') {
    $Mode = "--print-install"
} elseif ($RemainingArgs -contains "--run" -or $MyInvocation.Line -match '(^|\s)--run(\s|$)') {
    $Mode = "--run"
} elseif ($RemainingArgs -contains "--renderdoc" -or $MyInvocation.Line -match '(^|\s)--renderdoc(\s|$)') {
    $Mode = "--renderdoc"
} elseif ($RemainingArgs -contains "--check" -or $MyInvocation.Line -match '(^|\s)--check(\s|$)') {
    $Mode = "--check"
}

function Write-Install {
    @"
Windows PowerShell:
  winget install --id KhronosGroup.VulkanSDK --accept-source-agreements --accept-package-agreements
  winget install --id Google.Chrome --accept-source-agreements --accept-package-agreements
  winget install --id OpenJS.NodeJS.LTS --accept-source-agreements --accept-package-agreements
  npm install -g electron

RenderDoc:
  Install RenderDoc from https://renderdoc.org/builds, then open a fresh shell.
  Confirm renderdoccmd.exe is on PATH or set RDOC_HOME to the install root.

Required checks:
  Get-Command vulkaninfo
  Get-Command glslangValidator
  Get-Command spirv-as
  Get-Command dxc
  Get-Command renderdoccmd
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-vulkan-env.ps1 --check
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-vulkan-env.ps1 --run
  powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-vulkan-env.ps1 --renderdoc
"@
}

function Command-Source([string]$name) {
    $cmd = Get-Command $name -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    return ""
}

function Existing-Path([string[]]$paths) {
    foreach ($path in $paths) {
        if (-not [string]::IsNullOrWhiteSpace($path) -and (Test-Path -LiteralPath $path)) {
            return $path
        }
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

function Read-KeyValueFile([string]$path) {
    $map = @{}
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return $map
    }
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
        if ($map.ContainsKey($key) -and "$($map[$key])" -ne "") {
            return "$($map[$key])"
        }
    }
    return $defaultValue
}

function Add-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
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
    if ($arg -match '[\s"]') {
        return '"' + ($arg -replace '"', '\"') + '"'
    }
    return $arg
}

function Has-RdocMagic([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) { return $false }
    $stream = [System.IO.File]::OpenRead($path)
    try {
        if ($stream.Length -lt 4) { return $false }
        $bytes = New-Object byte[] 4
        [void]$stream.Read($bytes, 0, 4)
        return ([System.Text.Encoding]::ASCII.GetString($bytes) -eq "RDOC")
    } finally {
        $stream.Dispose()
    }
}

function Invoke-ProcessBound([string]$exe, [string[]]$argList, [string]$stdoutPath, [string]$stderrPath, [int]$timeoutSecs) {
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $exe
    $psi.Arguments = (($argList | ForEach-Object { Quote-Arg $_ }) -join " ")
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.UseShellExecute = $false
    $psi.CreateNoWindow = $true
    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $psi
    [void]$process.Start()
    if (-not $process.WaitForExit($timeoutSecs * 1000)) {
        try { $process.Kill() } catch {}
        "timeout" | Set-Content -Encoding ASCII -Path $stderrPath
        return 124
    }
    $process.StandardOutput.ReadToEnd() | Set-Content -Encoding ASCII -Path $stdoutPath
    $process.StandardError.ReadToEnd() | Set-Content -Encoding ASCII -Path $stderrPath
    return $process.ExitCode
}

function Invoke-Capture([string]$exe, [string[]]$argList, [hashtable]$envMap, [string]$stdoutPath, [string]$stderrPath, [int]$timeoutSecs) {
    $oldValues = @{}
    foreach ($key in $envMap.Keys) {
        $oldValues[$key] = (Get-Item -LiteralPath "Env:\$key" -ErrorAction SilentlyContinue).Value
        Set-Item -LiteralPath "Env:\$key" -Value "$($envMap[$key])"
    }
    try {
        & $exe @argList > $stdoutPath 2> $stderrPath
        if ($null -ne $global:LASTEXITCODE) { return [int]$global:LASTEXITCODE }
        return 0
    } finally {
        foreach ($key in $oldValues.Keys) {
            if ($null -eq $oldValues[$key]) {
                Remove-Item -LiteralPath "Env:\$key" -ErrorAction SilentlyContinue
            } else {
                Set-Item -LiteralPath "Env:\$key" -Value $oldValues[$key]
            }
        }
    }
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

New-Item -ItemType Directory -Force -Path (Split-Path -Parent $EvidencePath) | Out-Null
New-Item -ItemType Directory -Force -Path $BuildFullDir | Out-Null

$rows = New-Object System.Collections.Generic.List[string]
$simple = Read-KeyValueFile $SimpleReadbackEvidencePath
$HtmlFullPath = if ([System.IO.Path]::IsPathRooted($HtmlPath)) { $HtmlPath } else { Join-Path $RootDir $HtmlPath }
$NodeSource = Command-Source "node"
$ElectronCaptureScript = Join-Path $RootDir "tools\electron-live-bitmap\capture_html_argb.js"
$ChromeCaptureScript = Join-Path $RootDir "tools\chrome-live-bitmap\capture_html_argb.js"

$vulkanSdkBin = Candidate-Path $env:VULKAN_SDK "Bin"
$vulkanInfoSource = Tool-Source @("vulkaninfo", "vulkaninfo.exe") @(
    (Candidate-Path $vulkanSdkBin "vulkaninfo.exe")
)
$glslangSource = Tool-Source @("glslangValidator", "glslangValidator.exe") @(
    (Candidate-Path $vulkanSdkBin "glslangValidator.exe")
)
$spirvAsSource = Tool-Source @("spirv-as", "spirv-as.exe") @(
    (Candidate-Path $vulkanSdkBin "spirv-as.exe")
)
$dxcSource = Tool-Source @("dxc", "dxc.exe") @(
    (Candidate-Path $vulkanSdkBin "dxc.exe")
)
$chromeSource = Tool-Source @("chrome", "chrome.exe") @(
    (Candidate-Path $env:ProgramFiles "Google\Chrome\Application\chrome.exe"),
    (Candidate-Path ${env:ProgramFiles(x86)} "Google\Chrome\Application\chrome.exe"),
    (Candidate-Path $env:LocalAppData "Google\Chrome\Application\chrome.exe")
)
$electronSource = Existing-Path @(
    (Join-Path $RootDir "tools\electron-shell\node_modules\electron\dist\electron.exe")
)
if ($electronSource -eq "") {
    $electronSource = Tool-Source @("electron.cmd", "electron.exe", "electron") @()
}
$renderdocSource = Tool-Source @("renderdoccmd", "renderdoccmd.exe", "qrenderdoc", "qrenderdoc.exe") @(
    (Candidate-Path $env:RDOC_HOME "renderdoccmd.exe"),
    (Candidate-Path $env:RDOC_HOME "qrenderdoc.exe"),
    (Candidate-Path (Candidate-Path $env:RDOC_HOME "bin") "renderdoccmd.exe"),
    (Candidate-Path (Candidate-Path $env:RDOC_HOME "bin") "qrenderdoc.exe"),
    (Candidate-Path $env:ProgramFiles "RenderDoc\renderdoccmd.exe"),
    (Candidate-Path $env:ProgramFiles "RenderDoc\qrenderdoc.exe"),
    (Candidate-Path ${env:ProgramFiles(x86)} "RenderDoc\renderdoccmd.exe"),
    (Candidate-Path ${env:ProgramFiles(x86)} "RenderDoc\qrenderdoc.exe")
)

$vulkanInfoStatus = Tool-Status $vulkanInfoSource
$glslangStatus = Tool-Status $glslangSource
$spirvAsStatus = Tool-Status $spirvAsSource
$dxcStatus = Tool-Status $dxcSource
$chromeStatus = Tool-Status $chromeSource
$electronStatus = Tool-Status $electronSource
$renderdocStatus = Tool-Status $renderdocSource

$sdkToolsStatus = if ($glslangStatus -eq "pass" -and $spirvAsStatus -eq "pass" -and $dxcStatus -eq "pass") { "pass" } else { "blocked:sdk-tools-missing" }
$simpleReadbackStatus = Value-Or $simple @("vulkan_engine2d_readback_status") "missing"
$simpleBackend = Value-Or $simple @("vulkan_engine2d_readback_backend_name", "simpleos_engine2d_runtime_backend") ""
$simpleChecksum = Value-Or $simple @("vulkan_engine2d_readback_rect_actual_checksum", "simpleos_engine2d_readback_checksum") ""
$simpleStatus = if ($simpleReadbackStatus -eq "pass" -and $simpleBackend -eq "vulkan" -and $simpleChecksum -ne "") { "pass" } else { "blocked:simple-vulkan-readback-missing" }

if ($vulkanInfoStatus -ne "pass") {
    $hostReadiness = "blocked:vulkaninfo-missing-or-failed"
} elseif ($sdkToolsStatus -ne "pass") {
    $hostReadiness = "blocked:sdk-tools-missing"
} elseif ($renderdocStatus -ne "pass") {
    $hostReadiness = "blocked:renderdoc-tools-missing"
} elseif ($chromeStatus -ne "pass" -or $electronStatus -ne "pass") {
    $hostReadiness = "blocked:host-tools-incomplete"
} else {
    $hostReadiness = "pass"
}

Add-Row $rows "gui_web_2d_vulkan_mode" $(if ($Mode -eq "--renderdoc") { "windows-renderdoc" } elseif ($Mode -eq "--run") { "windows-run" } else { "windows-check" })
Add-Row $rows "gui_web_2d_vulkan_build_dir" "$BuildFullDir"
Add-Row $rows "gui_web_2d_vulkan_evidence_path" "$EvidencePath"
Add-Row $rows "gui_web_2d_vulkan_windows_setup_wrapper" "scripts/setup/setup-gui-web-2d-vulkan-env.ps1"
Add-Row $rows "gui_web_2d_vulkan_html_path" "$HtmlFullPath"
Add-Row $rows "gui_web_2d_vulkan_width" "$Width"
Add-Row $rows "gui_web_2d_vulkan_height" "$Height"
Add-Row $rows "gui_web_2d_vulkan_timeout_secs" "$TimeoutSecs"
Add-Row $rows "gui_web_2d_vulkan_simple_readback_evidence_path" "$SimpleReadbackEvidencePath"
Add-Row $rows "gui_web_2d_vulkan_simple_status" "$simpleStatus"
Add-Row $rows "gui_web_2d_vulkan_simple_backend_name" "$simpleBackend"
Add-Row $rows "gui_web_2d_vulkan_simple_argb_checksum" "$simpleChecksum"
Add-Row $rows "gui_web_2d_vulkan_vulkaninfo_status" "$vulkanInfoStatus"
Add-Row $rows "gui_web_2d_vulkan_vulkaninfo_path" "$vulkanInfoSource"
Add-Row $rows "gui_web_2d_vulkan_glslang_validator_status" "$glslangStatus"
Add-Row $rows "gui_web_2d_vulkan_glslang_validator_path" "$glslangSource"
Add-Row $rows "gui_web_2d_vulkan_spirv_as_status" "$spirvAsStatus"
Add-Row $rows "gui_web_2d_vulkan_spirv_as_path" "$spirvAsSource"
Add-Row $rows "gui_web_2d_vulkan_dxc_status" "$dxcStatus"
Add-Row $rows "gui_web_2d_vulkan_dxc_path" "$dxcSource"
Add-Row $rows "gui_web_2d_vulkan_chrome_status" "$chromeStatus"
Add-Row $rows "gui_web_2d_vulkan_chrome_path" "$chromeSource"
Add-Row $rows "gui_web_2d_vulkan_electron_status" "$electronStatus"
Add-Row $rows "gui_web_2d_vulkan_electron_path" "$electronSource"
Add-Row $rows "gui_web_2d_vulkan_renderdoc_status" "$renderdocStatus"
Add-Row $rows "gui_web_2d_vulkan_renderdoc_cmd" "$renderdocSource"
Add-Row $rows "gui_web_2d_vulkan_sdk_tools_status" "$sdkToolsStatus"
Add-Row $rows "gui_web_2d_vulkan_host_readiness_status" "$hostReadiness"

$runStatus = "not-run"
if ($Mode -eq "--run" -or $Mode -eq "--renderdoc") {
    $runStatus = "fail"
    $electronOut = Join-Path $BuildFullDir "electron.out"
    $electronLog = Join-Path $BuildFullDir "electron.log"
    $electronArgb = Join-Path $BuildFullDir "electron_argb.json"
    $electronProof = Join-Path $BuildFullDir "electron_argb_proof.json"
    $chromeOut = Join-Path $BuildFullDir "chrome_argb.out"
    $chromeLog = Join-Path $BuildFullDir "chrome_argb.log"
    $chromeArgb = Join-Path $BuildFullDir "chrome_argb.json"
    $chromeProof = Join-Path $BuildFullDir "chrome_argb_proof.json"
    $chromeGeometry = Join-Path $BuildFullDir "chrome_geometry.json"

    $electronFlags = @("--no-sandbox", "--disable-gpu-sandbox", "--disable-dev-shm-usage", "--enable-features=Vulkan", "--use-angle=vulkan")
    $chromeFlags = "--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan"

    Add-Row $rows "gui_web_2d_vulkan_node_status" (Tool-Status $NodeSource)
    Add-Row $rows "gui_web_2d_vulkan_node_path" "$NodeSource"
    Add-Row $rows "gui_web_2d_vulkan_electron_requested_api" "vulkan"
    Add-Row $rows "gui_web_2d_vulkan_electron_requested_angle" "vulkan"
    Add-Row $rows "gui_web_2d_vulkan_electron_launch_flags" ($electronFlags -join " ")
    Add-Row $rows "gui_web_2d_vulkan_chrome_requested_api" "vulkan"
    Add-Row $rows "gui_web_2d_vulkan_chrome_requested_angle" "vulkan"
    Add-Row $rows "gui_web_2d_vulkan_chrome_launch_flags" "$chromeFlags"

    if ($electronStatus -eq "pass" -and (Test-Path -LiteralPath $ElectronCaptureScript)) {
        $electronEnv = @{
            ELECTRON_CAPTURE_HTML = "$HtmlFullPath"
            ELECTRON_CAPTURE_WIDTH = "$Width"
            ELECTRON_CAPTURE_HEIGHT = "$Height"
            ELECTRON_CAPTURE_OUTPUT = "$electronArgb"
            ELECTRON_CAPTURE_PROOF_PATH = "$electronProof"
            ELECTRON_CAPTURE_SETTLE_MS = "1000"
            ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT = "38217"
            ELECTRON_ENABLE_LOGGING = "1"
        }
        $electronCode = Invoke-Capture $electronSource ($electronFlags + @("$ElectronCaptureScript")) $electronEnv $electronOut $electronLog $TimeoutSecs
        Wait-ForFile $electronArgb | Out-Null
        Wait-ForFile $electronProof | Out-Null
        Add-Row $rows "gui_web_2d_vulkan_electron_exit_code" "$electronCode"
        Add-Row $rows "gui_web_2d_vulkan_electron_stdout" "$electronOut"
        Add-Row $rows "gui_web_2d_vulkan_electron_log" "$electronLog"
        Add-Row $rows "gui_web_2d_vulkan_electron_argb_path" "$electronArgb"
        Add-Row $rows "gui_web_2d_vulkan_electron_argb_proof" "$electronProof"
        Add-Row $rows "gui_web_2d_vulkan_electron_argb_status" (Proof-Status $electronProof $electronArgb)
        Add-Row $rows "gui_web_2d_vulkan_electron_argb_checksum" (Json-Value-Or $electronProof @("checksum", "captured_argb_sha256") "")
        Add-Row $rows "gui_web_2d_vulkan_electron_vulkan" (Json-Value-Or $electronProof @("gpu_feature_status.vulkan", "gpuFeatureStatus.vulkan") "")
    } else {
        Add-Row $rows "gui_web_2d_vulkan_electron_exit_code" ""
        Add-Row $rows "gui_web_2d_vulkan_electron_argb_status" "unavailable"
        Add-Row $rows "gui_web_2d_vulkan_electron_argb_reason" "missing-electron-or-capture-script"
    }

    if ($chromeStatus -eq "pass" -and $NodeSource -ne "" -and (Test-Path -LiteralPath $ChromeCaptureScript)) {
        $chromeEnv = @{
            CHROME_CAPTURE_HTML = "$HtmlFullPath"
            CHROME_CAPTURE_WIDTH = "$Width"
            CHROME_CAPTURE_HEIGHT = "$Height"
            CHROME_CAPTURE_OUTPUT = "$chromeArgb"
            CHROME_CAPTURE_PROOF_PATH = "$chromeProof"
            CHROME_CAPTURE_GEOMETRY_OUTPUT = "$chromeGeometry"
            CHROME_CAPTURE_BIN = "$chromeSource"
            CHROME_CAPTURE_DISABLE_GPU = "false"
            CHROME_CAPTURE_EXTRA_ARGS = "$chromeFlags"
            CHROME_CAPTURE_TIMEOUT_MS = "$($TimeoutSecs * 1000)"
        }
        $chromeCode = Invoke-Capture $NodeSource @("$ChromeCaptureScript") $chromeEnv $chromeOut $chromeLog $TimeoutSecs
        Wait-ForFile $chromeArgb | Out-Null
        Wait-ForFile $chromeProof | Out-Null
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_exit_code" "$chromeCode"
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_stdout" "$chromeOut"
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_log" "$chromeLog"
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_path" "$chromeArgb"
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_proof" "$chromeProof"
        Add-Row $rows "gui_web_2d_vulkan_chrome_geometry" "$chromeGeometry"
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_status" (Proof-Status $chromeProof $chromeArgb)
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_checksum" (Json-Value-Or $chromeProof @("checksum") "")
    } else {
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_exit_code" ""
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_status" "unavailable"
        Add-Row $rows "gui_web_2d_vulkan_chrome_argb_reason" "missing-chrome-node-or-capture-script"
    }

    $electronArgbStatus = ($rows | Where-Object { $_ -like "gui_web_2d_vulkan_electron_argb_status=*" } | Select-Object -Last 1) -replace '^.*=', ''
    $chromeArgbStatus = ($rows | Where-Object { $_ -like "gui_web_2d_vulkan_chrome_argb_status=*" } | Select-Object -Last 1) -replace '^.*=', ''
    if ($simpleStatus -eq "pass" -and $electronArgbStatus -eq "pass" -and $chromeArgbStatus -eq "pass") {
        $runStatus = "pass"
    }
    Add-Row $rows "gui_web_2d_vulkan_direct_run_status" "$runStatus"
}

$renderdocCaptureStatus = "not-run"
if ($Mode -eq "--renderdoc") {
    $renderdocOut = Join-Path $BuildFullDir "renderdoc-chrome.out"
    $renderdocLog = Join-Path $BuildFullDir "renderdoc-chrome.log"
    $renderdocPrefix = Join-Path $BuildFullDir "renderdoc_chrome"
    $renderdocRdc = "$renderdocPrefix.rdc"
    Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_prefix" "$renderdocPrefix"
    Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_rdc" "$renderdocRdc"
    Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_stdout" "$renderdocOut"
    Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_log" "$renderdocLog"
    if ($renderdocStatus -ne "pass") {
        $renderdocCaptureStatus = "blocked:renderdoc-tools-missing"
        Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_status" "$renderdocCaptureStatus"
        Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_reason" "missing-renderdoccmd-or-qrenderdoc"
    } elseif ($chromeStatus -ne "pass") {
        $renderdocCaptureStatus = "blocked:chrome-missing"
        Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_status" "$renderdocCaptureStatus"
        Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_reason" "missing-chrome"
    } else {
        $chromeUserData = Join-Path $BuildFullDir "renderdoc-chrome-user-data"
        New-Item -ItemType Directory -Force -Path $chromeUserData | Out-Null
        $chromeFlagsForRenderDoc = @(
            "--headless=new",
            "--no-sandbox",
            "--disable-gpu-sandbox",
            "--disable-dev-shm-usage",
            "--enable-features=Vulkan",
            "--use-angle=vulkan",
            "--user-data-dir=$chromeUserData",
            "--window-size=$Width,$Height",
            "--screenshot=$(Join-Path $BuildFullDir 'renderdoc_chrome.png')",
            "file:///$($HtmlFullPath -replace '\\', '/')"
        )
        $renderdocArgs = @("capture", "-w", "-c", "$renderdocPrefix", "$chromeSource") + $chromeFlagsForRenderDoc
        $renderdocCode = Invoke-ProcessBound $renderdocSource $renderdocArgs $renderdocOut $renderdocLog $TimeoutSecs
        Wait-ForFile $renderdocRdc 5000 | Out-Null
        Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_exit_code" "$renderdocCode"
        if (Has-RdocMagic $renderdocRdc) {
            $renderdocCaptureStatus = "pass"
            Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_status" "$renderdocCaptureStatus"
            Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_reason" "rdc-magic-pass"
        } else {
            $renderdocCaptureStatus = "fail"
            Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_status" "$renderdocCaptureStatus"
            Add-Row $rows "gui_web_2d_vulkan_renderdoc_capture_reason" "missing-rdoc-magic"
        }
    }
}

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
$rows | ForEach-Object { Write-Output $_ }

if (($Mode -eq "--check" -and $hostReadiness -eq "pass" -and $simpleStatus -eq "pass") -or ($Mode -eq "--run" -and $runStatus -eq "pass") -or ($Mode -eq "--renderdoc" -and $runStatus -eq "pass" -and $renderdocCaptureStatus -eq "pass")) {
    exit 0
}
exit 1
