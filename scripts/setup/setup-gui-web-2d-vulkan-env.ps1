param(
    [ValidateSet("--check", "--print-install")]
    [string]$Mode = "--check",
    [string]$BuildDir = "build\gui-web-2d-vulkan-env-windows",
    [string]$EvidencePath = "",
    [string]$SimpleReadbackEvidencePath = "build\simpleos_multiconfig_live_evidence\vulkan-engine2d-readback-final.env",
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$RemainingArgs = @()
)

$ErrorActionPreference = "Stop"

if ($RemainingArgs -contains "--print-install" -or $MyInvocation.Line -match '(^|\s)--print-install(\s|$)') {
    $Mode = "--print-install"
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
"@
}

function Command-Source([string]$name) {
    $cmd = Get-Command $name -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    return ""
}

function Command-Status([string]$name) {
    if ((Command-Source $name) -ne "") { return "pass" }
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

if ($Mode -eq "--print-install") {
    Write-Install
    exit 0
}

if ([string]::IsNullOrWhiteSpace($EvidencePath)) {
    $EvidencePath = Join-Path $BuildDir "evidence.env"
}

New-Item -ItemType Directory -Force -Path (Split-Path -Parent $EvidencePath) | Out-Null

$rows = New-Object System.Collections.Generic.List[string]
$simple = Read-KeyValueFile $SimpleReadbackEvidencePath

$vulkanInfoStatus = Command-Status "vulkaninfo"
$glslangStatus = Command-Status "glslangValidator"
$spirvAsStatus = Command-Status "spirv-as"
$dxcStatus = Command-Status "dxc"
$chromeStatus = Command-Status "chrome"
if ($chromeStatus -ne "pass") { $chromeStatus = Command-Status "chrome.exe" }
$electronStatus = Command-Status "electron"
if ($electronStatus -ne "pass") { $electronStatus = Command-Status "electron.exe" }
$renderdocStatus = Command-Status "renderdoccmd"
if ($renderdocStatus -ne "pass") { $renderdocStatus = Command-Status "qrenderdoc" }

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

Add-Row $rows "gui_web_2d_vulkan_mode" "windows-check"
Add-Row $rows "gui_web_2d_vulkan_build_dir" "$BuildDir"
Add-Row $rows "gui_web_2d_vulkan_evidence_path" "$EvidencePath"
Add-Row $rows "gui_web_2d_vulkan_windows_setup_wrapper" "scripts/setup/setup-gui-web-2d-vulkan-env.ps1"
Add-Row $rows "gui_web_2d_vulkan_simple_readback_evidence_path" "$SimpleReadbackEvidencePath"
Add-Row $rows "gui_web_2d_vulkan_simple_status" "$simpleStatus"
Add-Row $rows "gui_web_2d_vulkan_simple_backend_name" "$simpleBackend"
Add-Row $rows "gui_web_2d_vulkan_simple_argb_checksum" "$simpleChecksum"
Add-Row $rows "gui_web_2d_vulkan_vulkaninfo_status" "$vulkanInfoStatus"
Add-Row $rows "gui_web_2d_vulkan_vulkaninfo_path" (Command-Source "vulkaninfo")
Add-Row $rows "gui_web_2d_vulkan_glslang_validator_status" "$glslangStatus"
Add-Row $rows "gui_web_2d_vulkan_glslang_validator_path" (Command-Source "glslangValidator")
Add-Row $rows "gui_web_2d_vulkan_spirv_as_status" "$spirvAsStatus"
Add-Row $rows "gui_web_2d_vulkan_spirv_as_path" (Command-Source "spirv-as")
Add-Row $rows "gui_web_2d_vulkan_dxc_status" "$dxcStatus"
Add-Row $rows "gui_web_2d_vulkan_dxc_path" (Command-Source "dxc")
Add-Row $rows "gui_web_2d_vulkan_chrome_status" "$chromeStatus"
Add-Row $rows "gui_web_2d_vulkan_chrome_path" $(if ((Command-Source "chrome") -ne "") { Command-Source "chrome" } else { Command-Source "chrome.exe" })
Add-Row $rows "gui_web_2d_vulkan_electron_status" "$electronStatus"
Add-Row $rows "gui_web_2d_vulkan_electron_path" $(if ((Command-Source "electron") -ne "") { Command-Source "electron" } else { Command-Source "electron.exe" })
Add-Row $rows "gui_web_2d_vulkan_renderdoc_status" "$renderdocStatus"
Add-Row $rows "gui_web_2d_vulkan_renderdoc_cmd" $(if ((Command-Source "renderdoccmd") -ne "") { Command-Source "renderdoccmd" } else { Command-Source "qrenderdoc" })
Add-Row $rows "gui_web_2d_vulkan_sdk_tools_status" "$sdkToolsStatus"
Add-Row $rows "gui_web_2d_vulkan_host_readiness_status" "$hostReadiness"

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
$rows | ForEach-Object { Write-Output $_ }

if ($hostReadiness -eq "pass" -and $simpleStatus -eq "pass") {
    exit 0
}
exit 1
