param(
    [Parameter(Mandatory=$true)][string]$Baseline,
    [Parameter(Mandatory=$true)][string]$Candidate,
    [Parameter(Mandatory=$true)][string]$OutputRoot,
    [Parameter(Mandatory=$true)][string]$OwnerLaunch,
    [Parameter(Mandatory=$true)][string]$Inputs,
    [Parameter(Mandatory=$true)][string]$InputsSha256,
    [int]$Rounds = 5,
    [int]$FileCount = 512
)
$ErrorActionPreference = 'Stop'
if ($Rounds -lt 5 -or $FileCount -lt 16) { throw 'At least five paired samples and sixteen files are required.' }
function Assert-Pin($Pin) {
    if (!$Pin.path -or ![IO.Path]::IsPathRooted($Pin.path) -or $Pin.sha256 -cnotmatch '^[0-9a-f]{64}$' -or
        (Get-FileHash -LiteralPath $Pin.path -Algorithm SHA256).Hash.ToLowerInvariant() -cne $Pin.sha256) { throw 'An immutable input pin is absent or changed.' }
}
function Read-Receipt([string]$Path) {
    $fields = @{}
    foreach ($line in [IO.File]::ReadAllLines($Path)) {
        $parts = $line.Split('=',2)
        if ($parts.Count -ne 2 -or $fields.ContainsKey($parts[0])) { throw "Malformed/duplicate receipt field: $Path" }
        $fields[$parts[0]] = $parts[1]
    }
    $fields
}
Assert-Pin @{path=$Inputs; sha256=$InputsSha256}
$pins = Get-Content -Raw -LiteralPath $Inputs | ConvertFrom-Json
if ($pins.schema -ne 'scv-snapshot-profile-inputs-v1' -or $pins.backend -notin @('cranelift','llvm') -or !$pins.target) { throw 'Invalid benchmark identity manifest.' }
$canonicalCollector = 'C:/Users/user/.simple/worktrees/simple/runtime/windows-native-final-prep/unlimited-log-owner.py'
$canonicalCollectorHash = '79a3fc4d27a08698d684c1bf2d3ce5e8d45dd523654be68a6360b590b6d9bfcd'
$canonicalAdmission = 'C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/downstream-resource-admission'

function Assert-OwnedExecution {
    $launch = Get-Content -Raw -LiteralPath $OwnerLaunch | ConvertFrom-Json
    $reservationPath = [IO.Path]::GetFullPath($launch.reservation)
    if ([IO.Path]::GetDirectoryName($reservationPath) -ne [IO.Path]::GetFullPath($canonicalAdmission)) { throw 'Reservation is outside the canonical coordinator.' }
    $slot = Get-Content -Raw -LiteralPath $reservationPath | ConvertFrom-Json
    if ($slot.schema -ne 'diagnostic-downstream-reservation/1' -or $slot.threads -ne 20 -or $slot.total_job_budget -ne 80 -or
        $slot.owner_pid -ne $launch.owner_pid -or $slot.helper_sha256 -ne $canonicalCollectorHash -or
        $slot.receipt_path -ne (Join-Path (Split-Path -Parent $OwnerLaunch) 'collector.receipt.env')) { throw 'Owner/collector reservation binding differs.' }
    $owner = Get-Process -Id $slot.owner_pid
    if ($owner.StartTime.ToUniversalTime().ToString('o') -cne $slot.owner_start_utc) { throw 'Reservation owner is stale or reused.' }
    Assert-Pin @{path=$launch.request; sha256=$launch.request_sha256}
    Assert-Pin @{path=$canonicalCollector; sha256=$canonicalCollectorHash}
    $request = Get-Content -Raw -LiteralPath $launch.request | ConvertFrom-Json
    if ($request.threads -ne 20 -or $request.schema -ne 'simple-native-worker-debug-command-v1') { throw 'Canonical request resource contract differs.' }
    $commandPaths = @($request.command | ForEach-Object { ([string]$_).Replace('\','/') })
    if ($commandPaths -notcontains $PSCommandPath.Replace('\','/') -or $commandPaths -notcontains $Inputs.Replace('\','/') -or
        $request.command -cnotcontains $InputsSha256) { throw 'Owner request does not pin this benchmark invocation and input manifest.' }
    $ancestor = [uint32]$PID
    $foundCollector = $false
    for ($depth=0; $depth -lt 32 -and $ancestor -gt 0; $depth++) {
        $processRow = Get-CimInstance Win32_Process -Filter "ProcessId=$ancestor"
        if (!$processRow) { throw 'Owner ancestry disappeared.' }
        if ($ancestor -eq $launch.collector_pid) {
            $normalized = $processRow.CommandLine.Replace('\','/')
            if (!$normalized.Contains($canonicalCollector) -or $normalized -notmatch '--timeout-seconds\s+0(?:\s|$)' -or
                $normalized -notmatch '--root-exit-policy\s+terminate-job(?:\s|$)') { throw 'Active collector is not the pinned no-timeout job owner.' }
            $foundCollector = $true
        }
        if ($ancestor -eq $slot.owner_pid) {
            if (!$foundCollector) { throw 'Benchmark is not inside the active collector process tree.' }
            return
        }
        $ancestor = [uint32]$processRow.ParentProcessId
    }
    throw 'Benchmark must be launched by the canonical reserved owner and collector.'
}

function Assert-SourceManifest($Pin) {
    Assert-Pin $Pin
    $manifest = Get-Content -Raw -LiteralPath $Pin.path | ConvertFrom-Json
    if ($manifest.schema -ne 'scv-profile-file-manifest-v1' -or !$manifest.files) { throw 'Source/runtime manifest is empty or malformed.' }
    $seen = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
    foreach ($file in $manifest.files) {
        if (!$seen.Add([IO.Path]::GetFullPath($file.path))) { throw 'Duplicate source/runtime pin.' }
        Assert-Pin $file
    }
}
function Assert-Identities([bool]$IncludeSources) {
    Assert-Pin @{path=$Inputs; sha256=$InputsSha256}
    Assert-Pin $pins.producer
    foreach ($name in @('git','bash','powershell','workload','wrapper','watchdog','sampler_source','sampler_binary','benchmark')) { Assert-Pin $pins.tools.$name }
    $scriptsRoot = Split-Path -Parent (Split-Path -Parent $pins.tools.wrapper.path)
    if ([IO.Path]::GetFullPath($pins.tools.watchdog.path) -ne [IO.Path]::GetFullPath("$scriptsRoot/resource/process-tree-rss-watchdog.pl") -or
        [IO.Path]::GetFullPath($pins.tools.sampler_source.path) -ne [IO.Path]::GetFullPath("$scriptsRoot/bootstrap/bootstrap-session-exec.c") -or
        (Split-Path -Leaf $pins.tools.wrapper.path) -ne 'run-process-group-timeout.shs') { throw 'Sampler pins do not name the wrapper actual dependencies.' }
    if (!$pins.helper_cache -or ![IO.Path]::GetFullPath($pins.tools.sampler_binary.path).StartsWith([IO.Path]::GetFullPath($pins.helper_cache).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)) { throw 'Pinned sampler must belong to the prepared helper cache.' }
    if ([IO.Path]::GetFullPath($pins.tools.benchmark.path) -ne [IO.Path]::GetFullPath($PSCommandPath)) { throw 'Pinned harness is not the running harness.' }
    foreach ($mode in @('baseline','candidate')) {
        $variant = $pins.$mode
        Assert-Pin $variant.binary
        Assert-Pin $variant.build_receipt
        Assert-Pin $variant.source_manifest
        $receipt = Get-Content -Raw -LiteralPath $variant.build_receipt.path | ConvertFrom-Json
        if ($receipt.schema -ne 'scv-snapshot-native-build-v1' -or $receipt.build_exit_status -ne 0 -or
            $receipt.binary_sha256 -cne $variant.binary.sha256 -or $receipt.source_manifest_sha256 -cne $variant.source_manifest.sha256 -or
            $receipt.producer_sha256 -cne $pins.producer.sha256 -or $receipt.backend -cne $pins.backend -or
            $receipt.target -cne $pins.target -or $receipt.runtime_manifest_sha256 -cne $pins.runtime_manifest.sha256) { throw 'Binary/source/producer/backend/runtime build provenance differs.' }
        if ($IncludeSources) { Assert-SourceManifest $variant.source_manifest }
    }
    Assert-Pin $pins.runtime_manifest
    if ($IncludeSources) { Assert-SourceManifest $pins.runtime_manifest }
}
Assert-OwnedExecution
Assert-Identities $true
if ([IO.Path]::GetFullPath($Baseline) -ne [IO.Path]::GetFullPath($pins.baseline.binary.path) -or
    [IO.Path]::GetFullPath($Candidate) -ne [IO.Path]::GetFullPath($pins.candidate.binary.path)) { throw 'Requested binary differs from the pinned build.' }
if (Test-Path -LiteralPath $OutputRoot) { throw 'OutputRoot must be fresh; existing evidence is never overwritten.' }
[IO.Directory]::CreateDirectory($OutputRoot) | Out-Null
$OutputRoot = [IO.Path]::GetFullPath($OutputRoot)
$git = $pins.tools.git.path
$rows = [Collections.Generic.List[object]]::new()
$utf8 = [Text.UTF8Encoding]::new($false)

function Invoke-Measured([string]$Exe, [string[]]$Arguments, [string]$Cwd, [string]$Log, [int[]]$Allowed = @(0)) {
    Assert-OwnedExecution
    Assert-Identities $false
    $measurementRoot = "$Log.measurement"
    if (Test-Path -LiteralPath $measurementRoot) { throw 'Measurement evidence already exists.' }
    [IO.Directory]::CreateDirectory("$measurementRoot/tmp") | Out-Null
    $rssReceipt = "$measurementRoot/tree.rss.env"
    $start = [Diagnostics.ProcessStartInfo]::new($pins.tools.bash.path)
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.WindowStyle = [Diagnostics.ProcessWindowStyle]::Hidden
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.WorkingDirectory = $Cwd
    $start.Environment['SCV_PROFILE_TMP'] = "$measurementRoot/tmp"
    $start.Environment['SCV_PROFILE_HELPER_CACHE'] = $pins.helper_cache
    $start.Environment['SIMPLE_PROCESS_TREE_RSS_RECEIPT'] = $rssReceipt.Replace('\','/')
    $start.Environment['SIMPLE_BOOTSTRAP_RSS_CAP_MODE'] = 'monitor'
    $start.Environment['SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB'] = '5242880'
    $start.Environment.Remove('SIMPLE_BOOTSTRAP_SESSION_ID') | Out-Null
    $start.Environment.Remove('SIMPLE_BOOTSTRAP_SESSION_EXEC') | Out-Null
    # Only positional arguments carry caller paths; the shell program is fixed.
    $program = 'export TMPDIR="$(cygpath -u "$SCV_PROFILE_TMP")"; export TMP="$SCV_PROFILE_TMP" TEMP="$SCV_PROFILE_TMP"; export SIMPLE_BOOTSTRAP_SESSION_HELPER_CACHE="$(cygpath -u "$SCV_PROFILE_HELPER_CACHE")"; exec sh "$1" 0 5 "${@:2}"'
    foreach ($argument in (@('--noprofile','--norc','-c',$program,'scv-profile',$pins.tools.wrapper.path.Replace('\','/'),$Exe.Replace('\','/')) + $Arguments)) { $start.ArgumentList.Add($argument) }
    $outFile = [IO.File]::Open($Log,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::Read)
    $errFile = [IO.File]::Open("$Log.stderr",[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::Read)
    $clock = [Diagnostics.Stopwatch]::StartNew()
    $process = [Diagnostics.Process]::Start($start)
    $stdout = $process.StandardOutput.BaseStream.CopyToAsync($outFile)
    $stderr = $process.StandardError.BaseStream.CopyToAsync($errFile)
    $process.WaitForExit()
    $clock.Stop()
    $stdout.GetAwaiter().GetResult()
    $stderr.GetAwaiter().GetResult()
    $outFile.Flush($true); $errFile.Flush($true)
    $outFile.Dispose(); $errFile.Dispose()
    # Logs are durable before any refusal. The canonical external owner handles
    # cancellation and descendant cleanup; this worker never kills on elapsed time.
    $rss = Read-Receipt $rssReceipt
    if ($rss.status -ne 'complete' -or $rss.quiescent -ne '1' -or $rss.rss_cap_mode -ne 'monitor' -or
        $rss.exit_status -ne [string]$process.ExitCode -or [int64]$rss.samples -le 0 -or [int64]$rss.peak_rss_kib -le 0 -or
        $rss.session_helper_integrity -ne 'verified' -or $rss.session_helper_sha256 -cne $pins.tools.sampler_binary.sha256 -or
        $rss.session_helper_source_sha256 -cne $pins.tools.sampler_source.sha256) { throw "Missing/invalid process-tree sampler evidence: $rssReceipt" }
    Assert-OwnedExecution
    Assert-Identities $false
    $out = [IO.File]::ReadAllText($Log)
    if ($process.ExitCode -notin $Allowed) { throw "Fixture failed ($($process.ExitCode)): $Log" }
    @{ elapsed_ms=$clock.Elapsed.TotalMilliseconds; peak_tree_rss_bytes=([int64]$rss.peak_rss_kib*1024); rss_receipt=$rssReceipt; stdout=$out; exit=$process.ExitCode }
}

function Invoke-Git([string]$Root, [string[]]$Arguments, [string]$Log, [int[]]$Allowed = @(0)) {
    Invoke-Measured $git (@('-c','core.autocrlf=false','-c','core.hooksPath=NUL','-c','commit.gpgsign=false') + $Arguments) $Root $Log $Allowed
}

function Invoke-ProfileWorkload([string]$Mode,[string]$Executable,[string]$Root,[string]$Case,[string]$Log) {
    $allowed = if ($Mode -eq 'git') { @(0,1) } else { @(0) }
    $arguments = @('-NoLogo','-NoProfile','-NonInteractive','-File',$pins.tools.workload.path,
        '-Mode',$Mode,'-Executable',$Executable,'-Root',$Root,'-Case',$Case)
    $result = Invoke-Measured $pins.tools.powershell.path $arguments $Root $Log $allowed
    $nativeStatus = [regex]::Matches($result.stdout,'(?m)^SCV_PROFILE_NATIVE_EXIT=([0-9]+)\r?$')
    if ($nativeStatus.Count -ne 1 -or [int]$nativeStatus[0].Groups[1].Value -ne $result.exit) { throw 'Workload host/native exit mismatch.' }
    if ($Mode -eq 'git') {
        $addStatus = [regex]::Matches($result.stdout,'(?m)^SCV_PROFILE_ADD_EXIT=([0-9]+)\r?$')
        if ($addStatus.Count -ne 1 -or $addStatus[0].Groups[1].Value -ne '0') { throw 'Git add did not complete successfully inside timed workload.' }
    }
    $result
}

function Read-GitIdentity([string]$Root, [string]$Label, [bool]$IncludeStaged = $true) {
    $head = Invoke-Git $Root @('rev-parse','--verify','HEAD') "$Root/$Label-head.log"
    $tree = Invoke-Git $Root @('rev-parse','--verify','HEAD^{tree}') "$Root/$Label-tree.log"
    $stagedTree = ''
    if ($IncludeStaged) { $stagedTree = (Invoke-Git $Root @('write-tree') "$Root/$Label-staged.log").stdout.Trim() }
    foreach ($value in @($head.stdout.Trim(),$tree.stdout.Trim()) + $(if ($IncludeStaged) { @($stagedTree) } else { @() })) {
        if ($value -cnotmatch '^(?:[0-9a-f]{40}|[0-9a-f]{64})$') { throw 'Git identity is malformed.' }
    }
    @{head=$head.stdout.Trim(); tree=$tree.stdout.Trim(); staged=$stagedTree}
}

function Assert-GitNoChange($Before, $After, [int]$ExitCode) {
    if ($ExitCode -ne 1 -or $Before.staged -cne $Before.tree -or $After.staged -cne $After.tree -or
        $Before.head -cne $After.head -or $Before.tree -cne $After.tree) { throw 'Git exit 1 was not a verified no-change commit.' }
}

function New-Fixture([string]$Root) {
    [IO.Directory]::CreateDirectory("$Root/src") | Out-Null
    [IO.Directory]::CreateDirectory("$Root/test") | Out-Null
    [IO.File]::WriteAllText("$Root/.gitignore", "build/`n", $utf8)
    $null = Invoke-Git $Root @('init','-q') "$Root/init.log"
    $null = Invoke-Git $Root @('config','user.email','snapshot-benchmark@example.invalid') "$Root/config-email.log"
    $null = Invoke-Git $Root @('config','user.name','SCV benchmark') "$Root/config-name.log"
    $null = Invoke-Git $Root @('add','.gitignore') "$Root/anchor-add.log"
    $null = Invoke-Git $Root @('commit','-q','-m','fixture anchor') "$Root/anchor-commit.log"
    for ($index=0; $index -lt $FileCount; $index++) {
        $family = if ($index % 8 -eq 0) { 'test' } else { 'src' }
        $lines = [Collections.Generic.List[string]]::new()
        for ($line=0; $line -lt (16 + ($index % 97)); $line++) {
            $lines.Add("fn fixture_${index}_${line}(value: i64) -> i64: value + $line # 한글 —")
        }
        [IO.File]::WriteAllText("$Root/$family/file_$index.spl", [string]::Join("`r`n", $lines)+"`r`n", $utf8)
    }
}

function Assert-Frozen([string]$Root, [string]$Snapshot, [string[]]$ExpectedPaths, [bool]$CompareLive = $true) {
    $manifest = [IO.File]::ReadAllLines("$Snapshot/SCV_COMPILE_INVENTORY")
    $expectedPathsSet = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    foreach ($expectedPath in $ExpectedPaths) {
        if (!$expectedPathsSet.Add($expectedPath)) { throw 'Duplicate expected fixture path.' }
    }
    if ($manifest.Count -ne $expectedPathsSet.Count) { throw 'Snapshot membership count mismatch.' }
    $seen = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    foreach ($line in $manifest) {
        $parts = $line.Split('|')
        if ($parts.Count -ne 3 -or $parts[1] -cnotmatch '^sha256_[0-9a-f]{64}$' -or $parts[2] -cnotmatch '^[0-9]+$') { throw 'Malformed snapshot manifest.' }
        if (!$expectedPathsSet.Contains($parts[0]) -or !$seen.Add($parts[0])) { throw 'Snapshot contains an unexpected or duplicate path.' }
        $live = "$Root/$($parts[0])"
        $frozen = "$Snapshot/$($parts[0])"
        $expected = $parts[1].Substring(7)
        $paths = if ($CompareLive) { @($live,$frozen) } else { @($frozen) }
        foreach ($path in $paths) {
            if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $expected) { throw "Stale/corrupt snapshot bytes: $path" }
            if ((Get-Item -LiteralPath $path).Length -ne [int64]$parts[2]) { throw 'Snapshot byte length mismatch.' }
        }
    }
    if (!$seen.SetEquals($expectedPathsSet)) { throw 'Snapshot omits expected paths.' }
}

$expectedPaths = @(for ($index=0; $index -lt $FileCount; $index++) {
    $family = if ($index % 8 -eq 0) { 'test' } else { 'src' }
    "$family/file_$index.spl"
})

foreach ($mode in @('baseline','candidate')) {
    $binary = if ($mode -eq 'candidate') { $Candidate } else { $Baseline }
    $probe = Invoke-ProfileWorkload 'scv' $binary $OutputRoot 'comparison' "$OutputRoot/comparison-$mode.log"
    if (!$probe.stdout.Contains('SCV_SNAPSHOT_COMPARISON_DONE')) { throw 'Native comparison vectors did not complete.' }
}
for ($round=0; $round -lt $Rounds; $round++) {
    # Alternate order to reduce thermal/filesystem cache order bias.
    $modes = if ($round % 2 -eq 0) { @('baseline','candidate','git') } else { @('git','candidate','baseline') }
    foreach ($mode in $modes) {
        $root = "$OutputRoot/r$round-$mode"
        New-Fixture $root
        $previous = ''
        $coldSnapshot = ''
        foreach ($case in @('cold','warm','nochange','onefilechange')) {
            if ($case -eq 'warm' -and $mode -ne 'git') {
                # Git's timed cold commit made its inputs tracked. Align the
                # SCV fixture's Git HEAD/index before comparing warm cases,
                # then admit that HEAD outside timing. Otherwise SCV alone
                # would rehash every untracked file on every warm refresh.
                $null = Invoke-Git $root @('add','--','src','test') "$root/prepare-warm-add.log"
                $null = Invoke-Git $root @('commit','-q','-m','align warm index') "$root/prepare-warm-commit.log"
                $binary = if ($mode -eq 'candidate') { $Candidate } else { $Baseline }
                $null = Invoke-ProfileWorkload 'scv' $binary $root 'prepare' "$root/prepare-warm-admission.log"
            }
            if ($case -eq 'nochange') {
                # Identical bytes with a changed timestamp cannot change identity.
                [IO.File]::SetLastWriteTimeUtc("$root/src/file_1.spl", [DateTime]::UtcNow.AddSeconds(2))
            }
            if ($case -eq 'onefilechange') { [IO.File]::AppendAllText("$root/src/file_1.spl", "# one changed file`n", $utf8) }
            if ($mode -eq 'git') {
                # Do not precompute a changed staged tree outside the timed
                # commit. The extra staged-tree oracle is needed only for no-op.
                $before = Read-GitIdentity $root "$case-before" ($case -in @('warm','nochange'))
                # No-change commit's exit 1 is its normal result, not an empty commit.
                $commit = Invoke-ProfileWorkload 'git' $git $root $case "$root/$case.log"
                if ($case -in @('cold','onefilechange') -and $commit.exit -ne 0) { throw 'Expected Git commit was not created.' }
                $after = Read-GitIdentity $root "$case-after"
                if ($case -in @('warm','nochange')) { Assert-GitNoChange $before $after $commit.exit }
                elseif ($after.head -ceq $before.head -or $after.staged -cne $after.tree) { throw 'Git commit did not publish the staged tree.' }
                $rows.Add(@{mode=$mode; case=$case; round=$round; elapsed_ms=$commit.elapsed_ms; peak_tree_rss_bytes=$commit.peak_tree_rss_bytes; rss_receipt=$commit.rss_receipt; before=$before; after=$after})
            } else {
                $binary = if ($mode -eq 'candidate') { $Candidate } else { $Baseline }
                $result = Invoke-ProfileWorkload 'scv' $binary $root $case "$root/$case.log"
                $fields = @{}
                foreach ($line in $result.stdout.Split("`n")) {
                    $parts = $line.Trim().Split('=',2)
                    if ($parts.Count -eq 2) { $fields[$parts[0]]=$parts[1] }
                }
                if (!$result.stdout.Contains('SCV_SNAPSHOT_GIT_PROFILE_DONE')) { throw 'Snapshot evidence incomplete.' }
                Assert-Frozen $root $fields.snapshot_root $expectedPaths
                if ($case -eq 'cold') { $coldSnapshot = $fields.snapshot_root }
                if ($case -in @('warm','nochange') -and $fields.revision -ne $previous) { throw 'Unchanged bytes changed snapshot identity.' }
                if ($case -eq 'onefilechange' -and $fields.revision -eq $previous) { throw 'Changed bytes reused stale snapshot identity.' }
                $previous = $fields.revision
                $rows.Add(@{mode=$mode; case=$case; round=$round; elapsed_ms=$result.elapsed_ms; peak_tree_rss_bytes=$result.peak_tree_rss_bytes; rss_receipt=$result.rss_receipt; fields=$fields})
            }
            $rows | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath "$OutputRoot/samples.json" -Encoding utf8
        }
        if ($mode -ne 'git') {
            # A new snapshot must not modify the old snapshot or its manifest.
            Assert-Frozen $root $coldSnapshot $expectedPaths $false
            $added = "$root/src/added.spl"
            [IO.File]::WriteAllText($added, "fn newly_visible(): 42`n", $utf8)
            $created = Invoke-ProfileWorkload 'scv' $binary $root 'check' "$root/check-untracked-create.log"
            $createdPath = [regex]::Match($created.stdout, '(?m)^snapshot_root=(.+)\r?$').Groups[1].Value.Trim()
            Assert-Frozen $root $createdPath ($expectedPaths + @('src/added.spl'))
            # Verify deletion is confined to this task's explicitly owned fixture.
            if (![IO.Path]::GetFullPath($added).StartsWith($OutputRoot+[IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) { throw 'Fixture delete escaped evidence root.' }
            Remove-Item -LiteralPath $added
            $deleted = Invoke-ProfileWorkload 'scv' $binary $root 'check' "$root/check-untracked-delete.log"
            $deletedRevision = [regex]::Match($deleted.stdout, '(?m)^revision=(.+)\r?$').Groups[1].Value.Trim()
            if ($deletedRevision -ne $previous) { throw 'Deleted untracked member left a stale snapshot.' }
            $deletedPath = [regex]::Match($deleted.stdout, '(?m)^snapshot_root=(.+)\r?$').Groups[1].Value.Trim()
            Assert-Frozen $root $deletedPath $expectedPaths
        }
    }
}
$summary = foreach ($case in @('cold','warm','nochange','onefilechange')) {
    foreach ($mode in @('baseline','candidate','git')) {
        $group = @($rows | Where-Object { $_.case -eq $case -and $_.mode -eq $mode })
        $times = @($group.elapsed_ms | Sort-Object)
        @{case=$case; mode=$mode; samples=$times.Count; p50_ms=$times[[Math]::Ceiling($times.Count*0.50)-1]; p95_ms=$times[[Math]::Ceiling($times.Count*0.95)-1]; peak_tree_rss_bytes=($group.peak_tree_rss_bytes | Measure-Object -Maximum).Maximum}
    }
}
$comparisons = foreach ($case in @('cold','warm','nochange','onefilechange')) {
    $before = $summary | Where-Object { $_.case -eq $case -and $_.mode -eq 'baseline' }
    $after = $summary | Where-Object { $_.case -eq $case -and $_.mode -eq 'candidate' }
    $gitRow = $summary | Where-Object { $_.case -eq $case -and $_.mode -eq 'git' }
    $timeRatio = $after.p95_ms / $before.p95_ms
    $memoryRatio = $after.peak_tree_rss_bytes / $before.peak_tree_rss_bytes
    @{case=$case; time_ratio=$timeRatio; tree_memory_ratio=$memoryRatio; ratio_sum=$timeRatio+$memoryRatio; git_p95_target_met=($after.p95_ms -le $gitRow.p95_ms)}
}
Assert-OwnedExecution
Assert-Identities $true
@{schema='scv-snapshot-git-profile-v2'; qualification='diagnostic-only'; input_manifest_sha256=$InputsSha256; baseline_sha256=$pins.baseline.binary.sha256; candidate_sha256=$pins.candidate.binary.sha256; baseline_source_manifest_sha256=$pins.baseline.source_manifest.sha256; candidate_source_manifest_sha256=$pins.candidate.source_manifest.sha256; producer_sha256=$pins.producer.sha256; backend=$pins.backend; target=$pins.target; runtime_manifest_sha256=$pins.runtime_manifest.sha256; file_count=$FileCount; memory_kind='external canonical process-tree RSS sampler; steady RSS unavailable'; timing_kind='external invocation including sampler transport; qualification must assess transport overhead'; owner_final_receipt='pending outer owner completion; required before admission'; summary=@($summary); comparisons=@($comparisons)} | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath "$OutputRoot/summary.json" -Encoding utf8
Write-Output "$OutputRoot/summary.json"
