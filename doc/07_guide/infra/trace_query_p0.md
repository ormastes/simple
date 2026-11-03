# P0 trace query candidate

Status: source implementation candidate, 2026-11-01; runtime acceptance and
deployment are blocked on an admitted source-matched Stage4 CLI. These commands
describe the candidate, not a claim that the installed binary supports it.

```text
simple trace list features
simple trace list requirements --snapshot=git:HEAD --limit=20 --format=sdn
simple trace show feature feature:traceability --snapshot=index
simple trace list requirements --prefix=req:REQ-TRC-01 --format=table
simple trace list features --declaration=doc/my-trace.sdn --path=src/my-file.spl
```

The default is a worktree developer preview of the canonical registered
`doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn` declaration.
The captured declaration's locators add the required file closure. This is an
explicit registered scope, not all legacy feature/bug DB rows. Repeated
`--declaration` replaces the default; `--path` adds files. Run from repository
root. Worktree inputs must be real files with observed non-symlink ancestors;
directories and unsafe/absolute paths are rejected. The closure is at most 256
files, each <=1 MiB and <=2 MiB total.

Worktree bytes are read once into an immutable in-memory bundle. Metadata
checks reject detectable changes, but coarse timestamps and hostile races mean
this is not an atomic repository snapshot. Output labels that limitation.
Each new CLI invocation captures anew; unchanged bytes reproduce identity,
changed bytes invalidate cursors. Git refs and index are frozen once before
locator expansion; continuation reads the same tree. Index freezing can add an
immutable Git tree object, without editing source/index/worktree contents.

`features`, `requirements` and explicitly declared `bugs` support list/show.
Groups and automatic legacy database ingestion remain unavailable. All output
is structural/unverified/admission-ineligible. An empty selected-kind page says
only that no matching authored nodes exist within this captured registry scope.
It does not prove no bugs or requirements exist elsewhere.

Paging sorts canonical IDs; `--limit` is 1..200. Pass the returned cursor with
the same snapshot, kind, prefix and limit. Scope/content changes invalidate it.
`show` requires a canonical identity and accepts neither prefix nor cursor.
Its canonical kind names are singular (`feature`, `requirement`, `bug`), with
plural aliases. List kind names are plural. Options accept both `--name=value`
and `--name value`, including `--limit 50` and `--cursor TOKEN`.
Node pages contain no edge export; page exhaustion is separate from graph
completeness. Table escapes control characters; structured output uses SDN.
Native JSON is unsupported. Diagnostics retain their snapshot/rule/entity.

Exit 0: complete scoped query (not qualified evidence). Exit 1: captured graph
is incomplete or a requested identity/kind is absent. Exit 2: invalid request,
unavailable group/provider, capture failure, stale cursor or exhausted budget.
Original `traceability-check` remains a separate SDN structural checker.

The current canonical manifest contains authored claims without independent
authority registration in this preview policy. Its nodes remain inspectable,
but it reports `TRACE-AUTHORITY-CONFLICT`, `graph_complete: false` and exit 1.
The command does not authorize those claims merely to obtain a successful exit.

Execution plan: run the focused unit and
`test/03_system/app/traceability/feature/trace_query_p0_spec.spl` scenarios with
the admitted candidate selected by `SIMPLE_TRACE_QUERY_TEST_BINARY`; then
generate/review its mirrored manual and maintain scores. No generated manual
is fabricated while execution is blocked. Current evidence/state:
`.spipe/extreme_typing_traceability/p0_state.md`.

The system index scenario also requires a harness-owned alternate
`GIT_INDEX_FILE` under `build/test-artifacts/trace_query_p0/`. Prepare it with a
staged tree different from HEAD while preserving the canonical declaration.
The scenario checks that difference and compares actual CLI subject against
independent Git object output; it never stages or edits the user's real index.

After an external reviewer admits the exact source-matched Stage4 binary and
its lineage/ToolingLinkReceiptV1, run this PowerShell setup from the repository
root. Set `SIMPLE_TRACE_QUERY_TEST_BINARY` to that admitted absolute path first.
Record its SHA-256, the admission receipt path and receipt SHA-256, and the
candidate commit (`git rev-parse HEAD`) with the test result. A binary hash alone
does not grant admission. No runner is selected automatically here.

```powershell
$traceCli = $env:SIMPLE_TRACE_QUERY_TEST_BINARY
if (-not $traceCli -or -not (Test-Path -LiteralPath $traceCli -PathType Leaf)) {
    throw 'Set SIMPLE_TRACE_QUERY_TEST_BINARY to the independently admitted Stage4 CLI'
}
Get-FileHash -LiteralPath $traceCli -Algorithm SHA256
git rev-parse HEAD
$traceCase = Join-Path (Get-Location) ('build/test-artifacts/trace_query_p0/' + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $traceCase | Out-Null
$traceIndex = Join-Path $traceCase 'index'
$tracePreviousIndex = $env:GIT_INDEX_FILE
try {
    $env:GIT_INDEX_FILE = [IO.Path]::GetFullPath($traceIndex)
    git read-tree HEAD
    if ($LASTEXITCODE -ne 0) { throw 'Could not prepare the alternate index' }
    $traceManifest = 'doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn'
    $traceOriginal = git show ('HEAD:' + $traceManifest)
    if ($LASTEXITCODE -ne 0) { throw 'Could not read the committed declaration' }
    $traceText = $traceOriginal -join "`n"
    $traceOldTitle = 'Simple traceability, SDN evidence and Slop'
    if (($traceText.Split([string[]]@($traceOldTitle), [StringSplitOptions]::None).Length - 1) -ne 1) {
        throw 'Expected exactly one canonical feature title before staging'
    }
    $traceStaged = $traceText.Replace($traceOldTitle, 'P0 staged feature title')
    $traceFixtureFile = Join-Path $traceCase 'staged-declaration.sdn'
    [IO.File]::WriteAllText($traceFixtureFile, $traceStaged, [Text.UTF8Encoding]::new($false))
    $traceBlob = git hash-object -w -- $traceFixtureFile
    if ($LASTEXITCODE -ne 0) { throw 'Could not create the staged declaration blob' }
    git update-index --add --cacheinfo ('100644,' + $traceBlob.Trim() + ',' + $traceManifest)
    if ($LASTEXITCODE -ne 0) { throw 'Could not stage the alternate-index fixture' }
    & $traceCli test test/01_unit/app/traceability/trace_node_query_spec.spl --mode=interpreter
    if ($LASTEXITCODE -ne 0) { throw 'Focused unit specifications failed' }
    & $traceCli test test/03_system/app/traceability/feature/trace_query_p0_spec.spl --mode=interpreter
    if ($LASTEXITCODE -ne 0) { throw 'P0 system specifications failed' }
} finally {
    if ($null -eq $tracePreviousIndex) {
        Remove-Item Env:GIT_INDEX_FILE -ErrorAction SilentlyContinue
    } else {
        $env:GIT_INDEX_FILE = $tracePreviousIndex
    }
}
```

Only `SIMPLE_TRACE_QUERY_TEST_BINARY` and the temporary `GIT_INDEX_FILE` are
required by these specs. Preserve the unique fixture and command output for
review; do not clean another session's artifacts. For a failed-case resume,
reuse that same alternate index and admitted binary identity, then run only
the changed/previously failing criterion. Do not repeat passing checks. The
native CLI called by the system spec must be rebuilt/admitted for this source;
running the spec interpreter on new source does not update an old CLI binary.

The alternate index changes the captured declaration's exact feature title to
`P0 staged feature title`; HEAD and worktree remain unchanged. The system oracle
asserts both that independent title and the expected Git tree, so an
implementation returning HEAD bytes with index metadata cannot pass.
