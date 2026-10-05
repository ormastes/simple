# Lightweight harness-oracle checks only; this never launches a compiler,
# benchmark, Git command, collector, or qualification job.
$ErrorActionPreference = 'Stop'
$harness = Join-Path $PSScriptRoot 'check-scv-snapshot-git-profile.ps1'
$tokens = $null
$parseErrors = $null
$tree = [Management.Automation.Language.Parser]::ParseFile($harness,[ref]$tokens,[ref]$parseErrors)
if ($parseErrors.Count) { throw 'Benchmark harness does not parse.' }
foreach ($name in @('Assert-Pin','Read-Receipt','Assert-Frozen','Assert-GitNoChange')) {
    $definition = @($tree.FindAll({param($node) $node -is [Management.Automation.Language.FunctionDefinitionAst]},$true) | Where-Object Name -eq $name)
    if ($definition.Count -ne 1) { throw "Expected one oracle definition: $name" }
    . ([ScriptBlock]::Create($definition[0].Extent.Text))
}
$root = Join-Path ([IO.Path]::GetTempPath()) ('scv-profile-oracles-'+[Guid]::NewGuid().ToString('N'))
$frozen = Join-Path $root 'snapshot'
[IO.Directory]::CreateDirectory("$root/src") | Out-Null
[IO.Directory]::CreateDirectory("$frozen/src") | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)
$script:checks = 0
function Expect-Refusal([ScriptBlock]$Action,[string]$Message) {
    try { & $Action } catch {
        if (!$_.Exception.Message.Contains($Message)) { throw }
        $script:checks++
        return
    }
    throw "Oracle unexpectedly accepted: $Message"
}
$rows = foreach ($name in @('a','b')) {
    $content = [Text.Encoding]::UTF8.GetBytes("file $name`n")
    [IO.File]::WriteAllBytes("$root/src/$name.spl",$content)
    [IO.File]::WriteAllBytes("$frozen/src/$name.spl",$content)
    "src/$name.spl|sha256_$((Get-FileHash -LiteralPath "$root/src/$name.spl").Hash.ToLowerInvariant())|$($content.Length)"
}
$manifest = "$frozen/SCV_COMPILE_INVENTORY"
$expected = @('src/a.spl','src/b.spl')
[IO.File]::WriteAllLines($manifest,@($rows[1],$rows[0]),$utf8)
Assert-Frozen $root $frozen $expected
$script:checks++
[IO.File]::WriteAllLines($manifest,@($rows[0],$rows[0]),$utf8)
Expect-Refusal { Assert-Frozen $root $frozen $expected } 'unexpected or duplicate path'
[IO.File]::WriteAllLines($manifest,@($rows[0]),$utf8)
Expect-Refusal { Assert-Frozen $root $frozen $expected } 'membership count mismatch'
[IO.File]::WriteAllLines($manifest,@($rows[0],$rows[1].Replace('src/b.spl','src/unexpected.spl')),$utf8)
Expect-Refusal { Assert-Frozen $root $frozen $expected } 'unexpected or duplicate path'
[IO.File]::WriteAllLines($manifest,@($rows[0],$rows[1].Replace('src/b.spl','src/B.spl')),$utf8)
Expect-Refusal { Assert-Frozen $root $frozen $expected } 'unexpected or duplicate path'
[IO.File]::WriteAllLines($manifest,$rows,$utf8)
Expect-Refusal { Assert-Frozen $root $frozen @('src/a.spl','src/a.spl') } 'Duplicate expected fixture path'
[IO.File]::WriteAllText("$frozen/src/a.spl",'changed',$utf8)
Expect-Refusal { Assert-Frozen $root $frozen $expected } 'Stale/corrupt snapshot bytes'
$before = @{head='head';tree='tree';staged='tree'}
Assert-GitNoChange $before @{head='head';tree='tree';staged='tree'} 1
$script:checks++
Expect-Refusal { Assert-GitNoChange $before $before 0 } 'not a verified no-change'
Expect-Refusal { Assert-GitNoChange $before @{head='new-head';tree='tree';staged='tree'} 1 } 'not a verified no-change'
Expect-Refusal { Assert-GitNoChange @{head='head';tree='tree';staged='dirty'} $before 1 } 'not a verified no-change'
Expect-Refusal { Assert-GitNoChange $before @{head='head';tree='tree';staged='dirty'} 1 } 'not a verified no-change'
Expect-Refusal { Assert-GitNoChange $before @{head='head';tree='changed';staged='changed'} 1 } 'not a verified no-change'
$receipt = "$root/receipt.env"
[IO.File]::WriteAllText($receipt,"status=complete`nexit_status=0`n",$utf8)
if ((Read-Receipt $receipt).exit_status -ne '0') { throw 'Receipt oracle lost a valid field.' }
$script:checks++
[IO.File]::WriteAllText($receipt,"status=complete`nstatus=failed`n",$utf8)
Expect-Refusal { Read-Receipt $receipt } 'Malformed/duplicate receipt field'
$pin = @{path=$receipt;sha256=(Get-FileHash -LiteralPath $receipt).Hash.ToLowerInvariant()}
Assert-Pin $pin
$script:checks++
[IO.File]::AppendAllText($receipt,'modified',$utf8)
Expect-Refusal { Assert-Pin $pin } 'input pin is absent or changed'
Write-Output "Harness oracle checks: PASS ($script:checks); native qualification: UNRUN; evidence=$root"
