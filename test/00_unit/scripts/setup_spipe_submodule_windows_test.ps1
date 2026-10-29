$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$Setup = Join-Path $Root 'scripts\setup\setup-spipe-submodule.ps1'
$GitlinkCheck = Join-Path $Root 'scripts\check\check-spipe-submodule-gitlinks.ps1'

# Both scripts derive the repository root from their own nested paths. The
# setup dry run exercises its root, example target, submodule path, and delegate.
$setupOutput = @(& powershell -NoProfile -ExecutionPolicy Bypass -File $Setup -DryRun 2>&1 | ForEach-Object { "$($_)" }) -join "`n"
if ($LASTEXITCODE -ne 0) { throw "SPipe setup dry run failed:`n$setupOutput" }
if ($setupOutput -notmatch [regex]::Escape((Join-Path $Root '.spipe\domain_expert'))) {
    throw "setup paths were not rooted at the repository:`n$setupOutput"
}
if ($setupOutput -notmatch [regex]::Escape((Join-Path $Root 'examples\05_stdlib\spipe\doc\00_llm_process\domain_expert'))) {
    throw "setup did not use the tracked SPipe example tree:`n$setupOutput"
}
if ($setupOutput -match [regex]::Escape((Join-Path $Root 'scripts\examples\spipe'))) {
    throw "setup emitted the stale scripts/examples/spipe path:`n$setupOutput"
}

# The checker must run from its nested scripts/check directory while still
# resolving the parent repository's index and tracked example tree.
$checkOutput = @(& powershell -NoProfile -ExecutionPolicy Bypass -File $GitlinkCheck --check 2>&1 | ForEach-Object { "$($_)" }) -join "`n"
if ($checkOutput -notmatch 'tracked_tree_ok examples/05_stdlib/spipe') {
    throw "SPipe gitlink check did not inspect the repository root:`n$checkOutput"
}

# In an isolated repository with a malformed submodule index entry, setup must
# propagate the read-only check failure without converting the index to a gitlink.
$Fixture = Join-Path ([IO.Path]::GetTempPath()) ('spipe setup fixture ' + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Fixture | Out-Null
try {
    $fixtureDirs = @(
        'scripts\setup', 'scripts\check', '.spipe\spipe\scripts',
        '.spipe\spipe\doc', 'examples\05_stdlib\spipe\doc'
    )
    foreach ($dir in $fixtureDirs) { New-Item -ItemType Directory -Path (Join-Path $Fixture $dir) -Force | Out-Null }
    Copy-Item -LiteralPath $Setup -Destination (Join-Path $Fixture 'scripts\setup\setup-spipe-submodule.ps1')
    Copy-Item -LiteralPath $GitlinkCheck -Destination (Join-Path $Fixture 'scripts\check\check-spipe-submodule-gitlinks.ps1')
    Set-Content -LiteralPath (Join-Path $Fixture '.spipe\spipe\scripts\setup-spipe-links.ps1') -Value 'exit 0'
    Set-Content -LiteralPath (Join-Path $Fixture '.spipe\spipe\doc\fixture.txt') -Value 'ordinary tracked file'
    Set-Content -LiteralPath (Join-Path $Fixture 'examples\05_stdlib\spipe\doc\fixture.txt') -Value 'tracked example tree'
    git -C $Fixture init -q
    git -C $Fixture config user.name 'SPipe setup regression'
    git -C $Fixture config user.email 'spipe-setup@example.invalid'
    git -C $Fixture add .
    git -C $Fixture commit -qm fixture
    $indexBefore = (git -C $Fixture ls-files --stage) -join "`n"

    $previousErrorAction = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $fixtureOutput = @(& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $Fixture 'scripts\setup\setup-spipe-submodule.ps1') 2>&1 | ForEach-Object { "$($_)" }) -join "`n"
    $fixtureExitCode = $LASTEXITCODE
    $ErrorActionPreference = $previousErrorAction
    if ($fixtureExitCode -eq 0) { throw "setup accepted malformed gitlink index:`n$fixtureOutput" }
    if ($fixtureOutput -notmatch 'gitlink check failed') { throw "setup did not report check failure:`n$fixtureOutput" }
    $indexAfter = (git -C $Fixture ls-files --stage) -join "`n"
    if ($indexAfter -ne $indexBefore) { throw 'setup changed the fixture index after gitlink check failure' }
    if (Test-Path -LiteralPath (Join-Path $Fixture '.spipe\spipe_project')) { throw 'setup created links after gitlink check failure' }
} finally {
    if (Test-Path -LiteralPath $Fixture) { Remove-Item -LiteralPath $Fixture -Recurse -Force }
}

# Exercise the successful non-dry-run path against a local-only submodule.
# This keeps setup's git operations isolated from the shared repository and
# verifies both link creation and the delegated PowerShell exit status.
$SuccessFixture = Join-Path ([IO.Path]::GetTempPath()) ('spipe setup success fixture ' + [Guid]::NewGuid().ToString('N'))
$ChildRepo = Join-Path ([IO.Path]::GetTempPath()) ('spipe setup child repo ' + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $SuccessFixture, $ChildRepo | Out-Null
$previousMarker = $env:SPIPE_FIXTURE_MARKER
$previousChildExit = $env:SPIPE_FIXTURE_CHILD_EXIT
$previousAllowProtocol = $env:GIT_ALLOW_PROTOCOL
try {
    $childSetupDir = Join-Path $ChildRepo 'scripts'
    New-Item -ItemType Directory -Path $childSetupDir -Force | Out-Null
    $childScript = @'
if ($env:SPIPE_FIXTURE_CHILD_EXIT) { exit [int]$env:SPIPE_FIXTURE_CHILD_EXIT }
Set-Content -LiteralPath $env:SPIPE_FIXTURE_MARKER -Value 'delegated setup ran'
exit 0
'@
    Set-Content -LiteralPath (Join-Path $childSetupDir 'setup-spipe-links.ps1') -Value $childScript
    git -C $ChildRepo init -q
    git -C $ChildRepo config user.name 'SPipe setup regression'
    git -C $ChildRepo config user.email 'spipe-setup@example.invalid'
    git -C $ChildRepo add .
    git -C $ChildRepo commit -qm 'fixture submodule'
    $childHead = (git -C $ChildRepo rev-parse HEAD).Trim()

    $successDirs = @(
        'scripts\setup', 'scripts\check', 'examples\05_stdlib\spipe\doc\00_llm_process\domain_expert',
        'examples\05_stdlib\spipe\doc\00_llm_process\template',
        'examples\05_stdlib\spipe\doc\00_llm_process\spipe',
        'examples\05_stdlib\spipe\doc\00_llm_process\tool_expert\spipe_submodule',
        'examples\05_stdlib\spipe\doc\00_llm_process\project_expert\simple'
    )
    foreach ($dir in $successDirs) { New-Item -ItemType Directory -Path (Join-Path $SuccessFixture $dir) -Force | Out-Null }
    Copy-Item -LiteralPath $Setup -Destination (Join-Path $SuccessFixture 'scripts\setup\setup-spipe-submodule.ps1')
    Copy-Item -LiteralPath $GitlinkCheck -Destination (Join-Path $SuccessFixture 'scripts\check\check-spipe-submodule-gitlinks.ps1')
    Set-Content -LiteralPath (Join-Path $SuccessFixture 'examples\05_stdlib\spipe\fixture.txt') -Value 'tracked example tree'
    Set-Content -LiteralPath (Join-Path $SuccessFixture 'examples\05_stdlib\spipe\second_fixture.txt') -Value 'second tracked example file'
    Set-Content -LiteralPath (Join-Path $SuccessFixture '.gitmodules') -Value @'
[submodule ".spipe/spipe"]
    path = .spipe/spipe
    url = PLACEHOLDER
'@
    # Git's file protocol is disabled for submodule updates by default; this
    # fixture explicitly allows only its local test URL.
    $gitmodulesPath = Join-Path $SuccessFixture '.gitmodules'
    (Get-Content -LiteralPath $gitmodulesPath -Raw).Replace('PLACEHOLDER', $ChildRepo.Replace('\', '/')) |
        Set-Content -LiteralPath $gitmodulesPath
    git -C $SuccessFixture init -q
    git -C $SuccessFixture config user.name 'SPipe setup regression'
    git -C $SuccessFixture config user.email 'spipe-setup@example.invalid'
    git -C $SuccessFixture add .gitmodules scripts examples
    git -C $SuccessFixture commit -qm 'fixture host'
    git -C $SuccessFixture update-index --add --cacheinfo "160000,$childHead,.spipe/spipe"

    $env:SPIPE_FIXTURE_MARKER = Join-Path $SuccessFixture 'delegated.marker'
    $env:GIT_ALLOW_PROTOCOL = 'file'
    Remove-Item Env:SPIPE_FIXTURE_CHILD_EXIT -ErrorAction SilentlyContinue
    $previousErrorAction = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $successOutput = @(& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $SuccessFixture 'scripts\setup\setup-spipe-submodule.ps1') 2>&1 | ForEach-Object { "$($_)" }) -join "`n"
    $successExitCode = $LASTEXITCODE
    $ErrorActionPreference = $previousErrorAction
    if ($successExitCode -ne 0) { throw "successful setup failed:`n$successOutput" }
    if (-not (Test-Path -LiteralPath $env:SPIPE_FIXTURE_MARKER)) { throw 'setup did not run the delegated child script' }
    foreach ($link in @(
        '.spipe\spipe_project', '.spipe\domain_expert', '.spipe\template', '.spipe\spipe_docs',
        '.spipe\tool_expert\spipe_submodule', '.spipe\project_expert\spipe'
    )) {
        $linkPath = Join-Path $SuccessFixture $link
        if (-not (Test-Path -LiteralPath $linkPath)) { throw "setup did not create expected link $link" }
    }

    $env:SPIPE_FIXTURE_CHILD_EXIT = '7'
    $previousErrorAction = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $failureOutput = @(& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $SuccessFixture 'scripts\setup\setup-spipe-submodule.ps1') 2>&1 | ForEach-Object { "$($_)" }) -join "`n"
    $childFailureCode = $LASTEXITCODE
    $ErrorActionPreference = $previousErrorAction
    if ($childFailureCode -eq 0) { throw "setup swallowed delegated child failure:`n$failureOutput" }
    if ($failureOutput -notmatch 'delegated link setup failed with exit code 7') {
        throw "setup did not report delegated child failure:`n$failureOutput"
    }
} finally {
    if ($null -eq $previousMarker) { Remove-Item Env:SPIPE_FIXTURE_MARKER -ErrorAction SilentlyContinue } else { $env:SPIPE_FIXTURE_MARKER = $previousMarker }
    if ($null -eq $previousChildExit) { Remove-Item Env:SPIPE_FIXTURE_CHILD_EXIT -ErrorAction SilentlyContinue } else { $env:SPIPE_FIXTURE_CHILD_EXIT = $previousChildExit }
    if ($null -eq $previousAllowProtocol) { Remove-Item Env:GIT_ALLOW_PROTOCOL -ErrorAction SilentlyContinue } else { $env:GIT_ALLOW_PROTOCOL = $previousAllowProtocol }
    foreach ($path in @($SuccessFixture, $ChildRepo)) {
        if (Test-Path -LiteralPath $path) { Remove-Item -LiteralPath $path -Recurse -Force }
    }
}

Write-Output 'PASS Windows SPipe setup root, paths, dry-run, checker root, successful setup, delegated failure propagation'
