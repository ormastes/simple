param([Parameter(Mandatory=$true)][string]$EvidenceRoot,[switch]$ConsumerOnly)
$ErrorActionPreference='Stop'
$EvidenceRoot=[IO.Path]::GetFullPath($EvidenceRoot)
if (!$EvidenceRoot.StartsWith('D:\',[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $EvidenceRoot)) { throw 'fresh D evidence required' }
[IO.Directory]::CreateDirectory($EvidenceRoot)|Out-Null
[IO.Directory]::CreateDirectory("$EvidenceRoot/tmp")|Out-Null
$env:TEMP="$EvidenceRoot/tmp"; $env:TMP=$env:TEMP
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$authority=[IO.File]::ReadAllText("$root/scripts/check/lib/bootstrap-stage3/authority.shs")
$helper=[regex]::Match($authority,"(?s)bootstrap_stage3_materialized_native_source\(\)\s*\{\s*cat <<'STAGE3_NATIVE'\r?\n(.*?)\r?\nSTAGE3_NATIVE")
if (!$helper.Success) { throw 'native consumer extraction failed' }
$code=[regex]::Match($helper.Groups[1].Value,"(?s)Add-Type -TypeDefinition @'\r?\n(.*?)\r?\n'@")
if (!$code.Success) { throw 'consumer C# extraction failed' }
Add-Type -TypeDefinition $code.Groups[1].Value
Add-Type -TypeDefinition 'using System; using System.Runtime.InteropServices; public static class SnapshotFixtureLinks { [DllImport("kernel32.dll",CharSet=CharSet.Unicode,SetLastError=true)] public static extern bool CreateHardLinkW(string name,string existing,IntPtr security); }'
$utf8=[Text.UTF8Encoding]::new($false)
function Write-Bytes($path,$text) { [IO.File]::WriteAllText($path,$text,$utf8) }
function Assert-Bytes($path,$text) { if ([IO.File]::ReadAllText($path) -cne $text) { throw "bytes changed: $path" } }
function Refuse($source,$output,$reason) {
    $caught=$null
    try { [Stage3MaterializedConsumer]::PublishSnapshot($source,$output) } catch { $caught=$_.Exception.ToString() }
    if (!$caught -or !$caught.Contains($reason)) { throw "expected refusal $reason; got $caught" }
}
if (!$ConsumerOnly) {
$output="$EvidenceRoot/snapshot.env"
$source="$EvidenceRoot/pending"
Write-Bytes $source 'first snapshot'
[Stage3MaterializedConsumer]::PublishSnapshot($source,$output)
Assert-Bytes $output 'first snapshot'
if (Test-Path -LiteralPath $source) { throw 'absent publication retained source' }
Write-Bytes $source 'replacement snapshot'
[Stage3MaterializedConsumer]::PublishSnapshot($source,$output)
Assert-Bytes $output 'replacement snapshot'
if (Test-Path -LiteralPath $source) { throw 'replacement retained source' }
Write-Bytes $source 'refused snapshot'
$locked=[IO.File]::Open($output,[IO.FileMode]::Open,[IO.FileAccess]::Read,[IO.FileShare]::Read)
try { Refuse $source $output 'publication.rename' } finally { $locked.Dispose() }
Assert-Bytes $output 'replacement snapshot'; Assert-Bytes $source 'refused snapshot'
$hardlink="$EvidenceRoot/hardlink.env"
if (![SnapshotFixtureLinks]::CreateHardLinkW($hardlink,$output,[IntPtr]::Zero)) { throw 'fixture hardlink failed' }
Refuse $source $output 'publication.destination-not-regular'
Assert-Bytes $output 'replacement snapshot'; Assert-Bytes $hardlink 'replacement snapshot'; Assert-Bytes $source 'refused snapshot'
$directory="$EvidenceRoot/directory-output"
[IO.Directory]::CreateDirectory($directory)|Out-Null
Write-Bytes "$directory/sentinel" 'directory preserved'
Refuse $source $directory 'publication.destination-not-regular'
Assert-Bytes "$directory/sentinel" 'directory preserved'; Assert-Bytes $source 'refused snapshot'
$junction="$EvidenceRoot/junction-output"
New-Item -ItemType Junction -Path $junction -Target $directory|Out-Null
Refuse $source $junction 'publication.destination-not-regular'
Assert-Bytes "$directory/sentinel" 'directory preserved'; Assert-Bytes $source 'refused snapshot'
# A source on C is opened read-only (with rename permission) but is never
# renamed: the volume predicate must refuse before the kernel operation.
$crossSource="$env:SystemDrive/Users/$env:USERNAME/dev/simple/AGENTS.md"
if ((Test-Path -LiteralPath $crossSource) -and [IO.Path]::GetPathRoot($crossSource) -ne [IO.Path]::GetPathRoot($EvidenceRoot)) {
    $before=(Get-FileHash -LiteralPath $crossSource).Hash
    Refuse $crossSource "$EvidenceRoot/cross-volume.env" 'publication.parent-or-volume'
    if ((Get-FileHash -LiteralPath $crossSource).Hash -ne $before -or (Test-Path -LiteralPath "$EvidenceRoot/cross-volume.env")) { throw 'cross-volume refusal changed files' }
}
Write-Output 'publisher: absent/replacement/locked/hardlink/directory/reparse preservation PASS'
}

# Reproduce the canonical consumer's repeated-output path using a tiny real
# Git checkout and the canonical materializer/receipt, not fabricated receipt
# fields or a substitute publisher.
$fixture=[IO.Path]::GetFullPath("$EvidenceRoot/repository")
[IO.Directory]::CreateDirectory("$fixture/scripts/setup")|Out-Null
[IO.Directory]::CreateDirectory("$fixture/target")|Out-Null
Copy-Item -LiteralPath "$root/scripts/setup/materialize-symlinks-windows.shs" -Destination "$fixture/scripts/setup/materialize-symlinks-windows.shs"
Copy-Item -LiteralPath "$root/scripts/setup/windows-materialized-pending-policy.tsv" -Destination "$fixture/scripts/setup/windows-materialized-pending-policy.tsv"
Write-Bytes "$fixture/target/payload" 'canonical target'
Write-Bytes "$fixture/alias" 'target'
$env:GIT_CONFIG_NOSYSTEM='1'; $env:GIT_CONFIG_GLOBAL='NUL'
$hooks="$EvidenceRoot/empty-hooks"; [IO.Directory]::CreateDirectory($hooks)|Out-Null
function Git-Fixture([string[]]$Arguments) {
    $answer=& git -c core.hooksPath=$hooks -c core.autocrlf=false -C $fixture @Arguments
    if ($LASTEXITCODE) { throw "fixture git failed: $Arguments" }
    $answer
}
Git-Fixture @('init','-q')|Out-Null
Git-Fixture @('add','--','scripts','target')|Out-Null
$oid=(Git-Fixture @('hash-object','-w','--','alias')).Trim()
Git-Fixture @('update-index','--add','--cacheinfo',"120000,$oid,alias")|Out-Null
Git-Fixture @('-c','user.name=Snapshot Test','-c','user.email=snapshot-test@example.invalid','commit','-qm','snapshot fixture')|Out-Null
$receipt="$EvidenceRoot/materialized.receipt"
$msysFixture=$fixture.Replace('\','/').Replace('D:','/d')
$msysReceipt=$receipt.Replace('\','/').Replace('D:','/d')
$start=[Diagnostics.ProcessStartInfo]::new('C:/msys64/usr/bin/bash.exe')
$start.Arguments="--noprofile --norc `"$msysFixture/scripts/setup/materialize-symlinks-windows.shs`" --strict-missing --receipt `"$msysReceipt`" `"$msysFixture`""
$start.EnvironmentVariables['PATH']='C:\msys64\usr\bin;C:\dev\tool\Git\cmd;'+$env:PATH
$start.UseShellExecute=$false; $start.CreateNoWindow=$true
$start.RedirectStandardOutput=$true; $start.RedirectStandardError=$true
$p=[Diagnostics.Process]::Start($start)
$stdout=$p.StandardOutput.ReadToEndAsync(); $stderr=$p.StandardError.ReadToEndAsync()
if (!$p.WaitForExit(120000)) { $p.Kill(); throw 'materializer timeout' }
[IO.File]::WriteAllText("$EvidenceRoot/materializer.stdout.log",$stdout.Result)
[IO.File]::WriteAllText("$EvidenceRoot/materializer.stderr.log",$stderr.Result)
if ($p.ExitCode) { throw "materializer failed: $($stderr.Result)" }
if (!(Test-Path -LiteralPath $receipt)) { throw 'canonical receipt missing' }
$api="$EvidenceRoot/consumer.ps1"
[IO.File]::WriteAllText($api,$helper.Groups[1].Value,$utf8)
$consumerOutput="$EvidenceRoot/consumer-snapshot.env"
function Run-Consumer($inputReceipt,$expectedExit) {
    $si=[Diagnostics.ProcessStartInfo]::new('powershell.exe',"-NoProfile -NonInteractive -ExecutionPolicy Bypass -File `"$api`"")
    $si.UseShellExecute=$false; $si.CreateNoWindow=$true; $si.RedirectStandardOutput=$true; $si.RedirectStandardError=$true
    $si.EnvironmentVariables['STAGE3_ROOT']=$fixture
    $si.EnvironmentVariables['STAGE3_ROOT_B64']=[Convert]::ToBase64String([Text.Encoding]::UTF8.GetBytes($msysFixture))
    $si.EnvironmentVariables['STAGE3_RECEIPT']=$inputReceipt
    $si.EnvironmentVariables['STAGE3_RESULT']="$EvidenceRoot/consumer-pending"
    $si.EnvironmentVariables['STAGE3_OUTPUT']=$consumerOutput
    $si.EnvironmentVariables['STAGE3_GIT']=(Get-Command git).Source
    $si.EnvironmentVariables['STAGE3_SH']='C:/msys64/usr/bin/sh.exe'
    $child=[Diagnostics.Process]::Start($si)
    $out=$child.StandardOutput.ReadToEndAsync(); $err=$child.StandardError.ReadToEndAsync()
    if (!$child.WaitForExit(120000)) { $child.Kill(); throw 'consumer timeout' }
    [IO.File]::AppendAllText("$EvidenceRoot/consumer.stderr.log",$err.Result)
    if ($child.ExitCode -ne $expectedExit) { throw "consumer exit$($child.ExitCode), expected$expectedExit : $($err.Result)" }
}
Run-Consumer $receipt 0
$original=[IO.File]::ReadAllText($consumerOutput)
Run-Consumer $receipt 0
Assert-Bytes $consumerOutput $original
$bad="$EvidenceRoot/refused.receipt"
Write-Bytes $bad ([IO.File]::ReadAllText($receipt).Replace('result=complete','result=refused'))
Run-Consumer $bad 1
Assert-Bytes $consumerOutput $original
Write-Output 'canonical consumer: repeated output and receipt-refusal preservation PASS'
$publication=if($ConsumerOnly){'not-run-consumer-only'}else{'PASS'}
Write-Bytes "$EvidenceRoot/result.env" "status=PASS`npublication=$publication`ncanonical_consumer_cases=3`n"
