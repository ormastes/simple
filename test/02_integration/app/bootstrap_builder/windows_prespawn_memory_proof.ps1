param(
    [Parameter(Mandatory=$true)][string]$Worker,
    [Parameter(Mandatory=$true)][string]$Child,
    [Parameter(Mandatory=$true)][string]$OutputRoot
)
$ErrorActionPreference='Stop'
$workerDigest=(Get-FileHash -LiteralPath $Worker -Algorithm SHA256).Hash.ToLowerInvariant()
$childDigest=(Get-FileHash -LiteralPath $Child -Algorithm SHA256).Hash.ToLowerInvariant()
[IO.Directory]::CreateDirectory($OutputRoot)|Out-Null
$outcomes=@()
foreach($case in @(
    @{name='sufficient';required='269484032';shouldStart=$true},
    @{name='insufficient';required='1125899906842624';shouldStart=$false},
    @{name='malformed';required='12x';shouldStart=$false},
    @{name='below-cap';required='1';shouldStart=$false},
    @{name='missing';required=$null;shouldStart=$false}
)){
    $attempt=Join-Path $OutputRoot $case.name
    [IO.Directory]::CreateDirectory((Join-Path $attempt 'work'))|Out-Null
    [IO.File]::WriteAllText((Join-Path $attempt 'work/input.txt'),'declared memory proof',[Text.UTF8Encoding]::new($false))
    $inputDigest=(Get-FileHash -LiteralPath (Join-Path $attempt 'work/input.txt') -Algorithm SHA256).Hash.ToLowerInvariant()
    $fields=@('SIMPLE-BUILD-TASK-1',$case.name,'1','bootstrap',$childDigest,$inputDigest,$workerDigest,$Child,$inputDigest,'30000','0','2','baseline-memory',(Join-Path $attempt 'work'),'1','input.txt',$inputDigest,'1','allocation.sdn')
    [IO.File]::WriteAllText((Join-Path $attempt 'request.sdn'),($fields -join "`n")+"`n",[Text.UTF8Encoding]::new($false))
    $start=[Diagnostics.ProcessStartInfo]::new()
    $start.FileName=$Worker;$start.WorkingDirectory=(Join-Path $attempt 'work')
    $start.UseShellExecute=$false;$start.CreateNoWindow=$true
    $start.Environment['SIMPLE_BUILD_STAGED_GIT']='0'
    $start.Environment['SIMPLE_BUILD_COMPILER_MEMORY_BYTES']='268435456'
    $start.Environment.Remove('SIMPLE_BUILD_PRESPAWN_REQUIRED_MEMORY_BYTES')|Out-Null
    if($case.required){$start.Environment['SIMPLE_BUILD_PRESPAWN_REQUIRED_MEMORY_BYTES']=$case.required}
    foreach($arg in @('worker','--request',(Join-Path $attempt 'request.sdn'),'--attempt-root',$attempt,'--host','prespawn-host')){$start.ArgumentList.Add($arg)}
    $process=[Diagnostics.Process]::Start($start)
    if(-not$process.WaitForExit(40000)){$process.Kill($true);throw ('Worker timeout: '+$case.name)}
    $process.Refresh()
    $result=@([IO.File]::ReadAllLines((Join-Path $attempt 'result.sdn')))
    $receipt=Join-Path $attempt 'compiler.not-started.sdn'
    $started=Test-Path -LiteralPath (Join-Path $attempt 'compiler.reaped')
    $noChild=Test-Path -LiteralPath $receipt
    $passed=$false
    if($case.shouldStart){
        $reap=@([IO.File]::ReadAllLines((Join-Path $attempt 'compiler.reaped')))
        $passed=$process.ExitCode-eq0 -and $started -and -not$noChild -and
            (Test-Path -LiteralPath (Join-Path $attempt 'work/allocation.sdn')) -and
            $result[5]-eq'OK' -and $result[3]-eq$reap[0] -and $reap[1]-eq'prespawn-host'
    }else{
        $proof=if($noChild){@([IO.File]::ReadAllLines($receipt))}else{@()}
        $passed=$process.ExitCode-eq2 -and $noChild -and -not$started -and
            -not(Test-Path -LiteralPath (Join-Path $attempt 'stdout.log')) -and
            $result[5]-eq'ERROR' -and $result[3]-eq$proof[1] -and $proof[2]-eq'prespawn-host' -and
            $proof[3]-match'pre-spawn memory requirement|pre-spawn available memory|pre-spawn requirement below'
    }
    $outcomes+=@{case=$case.name;pass=$passed;exit_code=$process.ExitCode;compiler_reaped=$started;no_child_started=$noChild}
}
$allPassed=@($outcomes|Where-Object {-not$_.pass}).Count-eq0
@{pass=$allPassed;worker_sha256=$workerDigest;child_sha256=$childDigest;cases=$outcomes}|
    ConvertTo-Json -Depth 5|Set-Content -LiteralPath (Join-Path $OutputRoot 'result.json')
if(-not$allPassed){throw 'Windows pre-spawn memory proof failed'}
