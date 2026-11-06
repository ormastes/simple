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

Authority for the canonical declaration's authored claims is owned by the
query policy, not by the declaration: `trace_query_registered_authorities_v1`
(`src/app/traceability/snapshot/query_scope_v1.spl`) grants origin
`intent:traceability`, owner path = the registered declaration, scope
`feature:traceability`, add-only, exactly the relations it authors
(`specifies`, `decomposes_to`, `implemented_by`, `described_by`,
`motivated_by`). The default preview therefore resolves with
`graph_complete: true` and exit 0. A claim with any other relation, origin,
owner or scope (including any `--declaration` file not in the registry) still
raises `TRACE-AUTHORITY-CONFLICT` and exits 1. A new registered declaration
needs its own registry rows in the same change.

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

## Running it today on the seed (agent quick start, 2026-11-06)

No Stage4 CLI is needed to *query*. The query entry is an ordinary Simple
program; run it from the repository root with any `simple` binary that can
`run` (the Rust seed included). The seed's own CLI does **not** dispatch
`simple trace` (it prints main help or `file not found: trace`), and the full
pure-Simple CLI (`run src/app/cli/main.spl trace ...`) takes ~60 s and writes
nothing on the seed, so use the direct module route. Its arguments are the
words after `simple trace`; a pasted leading `trace` word is also accepted, so
`... query_main.spl trace list features` and `... query_main.spl list features`
are identical:

```sh
S=D:/dev/wt/seed/simple.exe          # any simple binary that can `run`
$S run src/app/traceability/query_main.spl list features        2>/dev/null
$S run src/app/traceability/query_main.spl list requirements    2>/dev/null
$S run src/app/traceability/query_main.spl list bugs            2>/dev/null
$S run src/app/traceability/query_main.spl show feature feature:traceability 2>/dev/null
$S run src/app/traceability/query_main.spl list requirements --prefix=req:REQ-TRC-01 --limit 5 2>/dev/null
$S run src/app/traceability/query_main.spl list features --format=sdn 2>/dev/null
```

Measured on the Windows seed: ~4 s per call. **Always redirect stderr**: the
seed prints several hundred lines of JIT/collision warnings there; the query
document is stdout only.

How to read the output:

- **Exit status 0** is the normal result for the default worktree preview:
  the page rendered and the graph is `complete: true`. It is still
  `admission eligible: false` / `unverified` (a worktree preview is never
  admission evidence). Status 1 means the page rendered over an incomplete
  graph (diagnostics listed).
  Status 2 is a real error (`TRACE-QUERY-INVALID`, `-UNAVAILABLE`,
  `-DECLARATION`, `-INFRASTRUCTURE`); status 1 with `code:
  TRACE-QUERY-NOT-FOUND` means the snapshot was fine but the id/kind did not
  match.
- Table format: 7 header lines (`Snapshot:`, `Capture:`, `Ingestion:`,
  `Graph complete:`, `Qualification:`, `Generation:`, `Input manifest:`), then
  `KIND<TAB>ID<TAB>TITLE` rows, `Total selected: N`, optional `Next cursor:`,
  then diagnostics (none for the default preview; a
  `TRACE-AUTHORITY-CONFLICT` line means a claim outside the authority
  registry and is a real finding). Grep the rows out with `grep -P '^\w+\t'`.
- `--format=sdn`: one inline SDN dictionary on one line. Keys agents use:
  `nodes: [{id, kind, title}]`, `total_count`, `next_cursor`, `page_complete`,
  `graph_complete`, `snapshot_kind` (`worktree_preview` | `git_commit` |
  `git_index`), `revision`, `tree`, `locators: [{entity, path, blob,
  locator_kind, locator}]` (where each selected node is declared),
  `diagnostics` (capped at 200, `diagnostics_truncated`). Parse with
  `std.common.sdn.parser.parse_with_spans_and_issues`.
- Scope today is **the registered declaration only**
  (`doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn`: 1
  feature, 20 requirements, 0 bugs). `list bugs` returning `Total selected: 0`
  means no bug is *declared* there, not that `bug_db.sdn` is empty; legacy DB
  ingestion is a later WP. To query another declaration file pass
  `--declaration=<path>`.
- `--snapshot=git:<rev>` and `--snapshot index` need the owned-process v3
  adapter (`OwnedProcessLease`), which the seed interpreter does not provide
  (`TRACE-QUERY-INFRASTRUCTURE: owned process start: invalid 4-word receipt`).
  Those two routes verify only on a native/self-hosted binary. The worktree
  preview (default) has no such dependency.

Spec: `sh scripts/check/check-trace-query-p0.shs <simple-binary>` builds the
alternate-index fixture under `build/test-artifacts/trace_query_p0/` (never the
real index) and runs `test/03_system/app/traceability/feature/trace_query_p0_spec.spl`.
On the seed the 5 worktree scenarios pass; the 3 git/index scenarios need the
native process adapter (see above).

### Reverse references: `refs <kind> <id>` (slice 2, 2026-11-06)

"What points at this requirement, and what does it point to?" -- every authored
claim whose from/to is the selected identity, plus the declared file paths of
the other endpoint (the bug/requirement <-> file link):

```sh
$S run src/app/traceability/query_main.spl refs requirement req:REQ-TRC-001 2>/dev/null
$S run src/app/traceability/query_main.spl refs feature feature:traceability --format=sdn 2>/dev/null
```

Table: header, `Selected: <kind> <id> <title>`, then
`DIRECTION<TAB>RELATION<TAB>ID<TAB>KIND<TAB>TITLE<TAB>AUTHORITY<TAB>PATHS` rows
sorted by claim id, `Total references: N`, `LOCATOR` rows for the selected
node's own declaration sites, then diagnostics. `incoming specifies
feature:traceability` answers "which feature specifies this requirement";
`outgoing decomposes_to criterion:AC-TRC-001` lists its acceptance criteria;
`outgoing implemented_by source:trace-cli ... src/app/traceability/main.spl`
is the file link. SDN adds `selected: {id, kind, title}`, `references:
[{claim, direction, relation, from, to, other, other_kind, other_title,
other_paths, operation, origin, authority}]`, `reference_count`.

Read `authority` honestly: `authored-claim` means the relation is only
asserted in the declaration (no registered authority admitted it);
`registered-edge` means the graph also carries it as an edge (today: all 101
default claims). The declaration has no
`verified_by`/`accepted_by` claims, so "which spec verifies X" is not yet
answerable through `refs`; "which feature specifies X", decomposition and
implemented_by/described_by are. `--prefix` is rejected; `--limit`/`--cursor`
page exactly like `list`. Exit codes as for `show`.
