param(
    [switch]$Check,
    [switch]$Run,
    [switch]$PrintInstall,
    [string]$BuildDir = "build/gui-web-2d-vulkan-env-windows"
)

$ErrorActionPreference = "Continue"
$Root = (Resolve-Path (Join-Path $PSScriptRoot "..\..")).Path
$OutDir = Join-Path $Root $BuildDir
$Evidence = Join-Path $OutDir "evidence.env"
$HtmlPath = Join-Path $Root "test\fixtures\html_css\generated_gui_vulkan_renderdoc_fixture.html"

if ($PrintInstall) {
@"
Windows setup:
  winget install KhronosGroup.VulkanSDK
  winget install Google.Chrome
  winget install BaldurKarlsson.RenderDoc
  npm --prefix tools/electron-shell install
  .\scripts\setup\setup-gui-web-2d-vulkan-env.ps1 -Check
  .\scripts\setup\setup-gui-web-2d-vulkan-env.ps1 -Run

RenderDoc Vulkan layer:
  renderdoccmd.exe vulkanlayer --register --user
  renderdoccmd.exe vulkanlayer --explain
"@
    exit 0
}

New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
Remove-Item -Force -ErrorAction SilentlyContinue $Evidence

function Add-Kv($Key, $Value) {
    "$Key=$Value" | Out-File -FilePath $Evidence -Encoding utf8 -Append
}

function Find-CommandPath($Name) {
    $cmd = Get-Command $Name -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    return ""
}

function First-Existing($Candidates) {
    foreach ($candidate in $Candidates) {
        if ($candidate -and (Test-Path $candidate)) { return $candidate }
    }
    return ""
}

$Mode = if ($Run) { "run" } else { "check" }
$VulkanInfo = Find-CommandPath "vulkaninfo.exe"
if (-not $VulkanInfo) { $VulkanInfo = Find-CommandPath "vulkaninfo" }
$Chrome = First-Existing @(
    "$env:ProgramFiles\Google\Chrome\Application\chrome.exe",
    "${env:ProgramFiles(x86)}\Google\Chrome\Application\chrome.exe"
)
$Electron = First-Existing @(
    (Join-Path $Root "tools\electron-shell\node_modules\electron\dist\electron.exe"),
    (Join-Path $Root "tools\electron-shell\node_modules\.bin\electron.cmd")
)
$RenderDoc = Find-CommandPath "renderdoccmd.exe"
if (-not $RenderDoc) { $RenderDoc = Find-CommandPath "renderdoccmd" }

Add-Kv "gui_web_2d_vulkan_mode" $Mode
Add-Kv "gui_web_2d_vulkan_root" $Root
Add-Kv "gui_web_2d_vulkan_build_dir" $OutDir
Add-Kv "gui_web_2d_vulkan_platform" "windows"
Add-Kv "gui_web_2d_vulkan_vulkaninfo" $VulkanInfo
Add-Kv "gui_web_2d_vulkan_chrome" $Chrome
Add-Kv "gui_web_2d_vulkan_electron" $Electron
Add-Kv "gui_web_2d_vulkan_renderdoccmd" $RenderDoc
Add-Kv "gui_web_2d_vulkan_html_path" $HtmlPath

if ($VulkanInfo) {
    $VulkanOut = Join-Path $OutDir "vulkaninfo-summary.out"
    & $VulkanInfo --summary *> $VulkanOut
    Add-Kv "gui_web_2d_vulkan_loader_status" $(if ($LASTEXITCODE -eq 0) { "present" } else { "error" })
    Add-Kv "gui_web_2d_vulkan_loader_summary" $VulkanOut
} else {
    Add-Kv "gui_web_2d_vulkan_loader_status" "missing"
}

if ($Run) {
    Add-Kv "gui_web_2d_vulkan_run_note" "Windows direct launch is prepared here; use the POSIX wrapper on macOS/Linux for current automated probes."
    Add-Kv "gui_web_2d_vulkan_electron_vulkan_flags" "--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan"
    Add-Kv "gui_web_2d_vulkan_chrome_vulkan_flags" "--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan"
}

Add-Kv "gui_web_2d_vulkan_evidence_env" $Evidence
Get-Content $Evidence
