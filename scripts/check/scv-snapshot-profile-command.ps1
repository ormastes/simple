# One identical command host for each timed Git or SCV workload. The caller
# owns its collector/RSS session, identity pins, and correctness checks.
param(
    [Parameter(Mandatory=$true)][ValidateSet('git','scv')][string]$Mode,
    [Parameter(Mandatory=$true)][string]$Executable,
    [Parameter(Mandatory=$true)][string]$Root,
    [Parameter(Mandatory=$true)][ValidateSet('cold','warm','nochange','onefilechange','comparison','prepare','check')][string]$Case
)
$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
Set-Location -LiteralPath $Root
if ($Mode -eq 'git') {
    $prefix = @('-c','core.autocrlf=false','-c','core.hooksPath=NUL','-c','commit.gpgsign=false')
    & $Executable @prefix add -- src test
    $addExit = $LASTEXITCODE
    Write-Output "SCV_PROFILE_ADD_EXIT=$addExit"
    if ($addExit -ne 0) { exit $addExit }
    & $Executable @prefix commit -q -m "snapshot $Case"
    $nativeExit = $LASTEXITCODE
} else {
    $arguments = if ($Case -eq 'comparison') { @('--comparison-only') } else { @('--root',$Root) }
    if ($Case -eq 'cold') { $arguments += '--cold' }
    & $Executable @arguments
    $nativeExit = $LASTEXITCODE
}
Write-Output "SCV_PROFILE_NATIVE_EXIT=$nativeExit"
exit $nativeExit
