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
- Scope is **the registered declaration**
  (`doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn`: 1
  feature, 20 requirements, 0 declared bugs) **plus the legacy bug DB
  sidecar** (below). With `--bug-db=none`, `list bugs` returns `Total
  selected: 0` because no bug is *declared* in the registry. To query another
  declaration file pass `--declaration=<path>`.
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

### Legacy bug DB sidecar: `list|show|refs bug` (slice 3, 2026-11-06)

`doc/08_tracking/bug/bug_db.sdn` (2,687 rows: `bugs_active` wins over its
archived twin in `bugs`) is ingested **read-only** on every worktree-preview
query as a *sidecar*: bug nodes join the graph, the row attributes travel
beside them, and nothing becomes a graph claim, edge or locator (the file is
3.67 MB, over the capture caps, and its `file` column cannot be pinned or
authorized). Design: `doc/05_design/app/traceability_cli_sdn_v1.md` slice 3.

```sh
S=D:/dev/wt/seed/simple.exe
$S run src/app/traceability/query_main.spl list bugs --limit 20 2>/dev/null
$S run src/app/traceability/query_main.spl list bugs --status=open --severity=P1 --file-prefix=src/compiler/ 2>/dev/null
$S run src/app/traceability/query_main.spl show bug bug:2998 --format=sdn 2>/dev/null
$S run src/app/traceability/query_main.spl refs bug bug:2998 2>/dev/null
$S run src/app/traceability/query_main.spl list bugs --bug-db=build/other_db.sdn 2>/dev/null
$S run src/app/traceability/query_main.spl list features --bug-db=none 2>/dev/null
```

How to read it:

- Bug ids are `bug:<db id>` (the `id` column verbatim). `list bugs` rows carry
  three extra columns: `bug<TAB>ID<TAB>TITLE<TAB>STATUS<TAB>SEVERITY<TAB>LOCATION`
  where LOCATION is `file:line` from the row (often the bug's own `.md`
  record, sometimes a source file -- the row is reported as written). Other
  kinds keep `KIND<TAB>ID<TAB>TITLE`.
- Filters `--status=<exact>`, `--severity=<exact>`, `--file-prefix=<path or
  dir/>` are accepted only with `list bugs`, narrow *before* paging (so
  `Total selected` is the filtered count) and are bound into the cursor; a
  cursor from a filtered page is rejected without the same filters. Status
  values are whatever the DB holds (`open`, `fixed`, `fixing`,
  `fix-implemented-verification-pending`, `resolved-disappeared`, ...).
- "Which bugs touch file X": `list bugs --file-prefix=<exact path>` (the
  `file` column) -- `refs file <path>` is the planned one-command summary
  (design slice 5). "What does this bug point at": `refs bug <id>` prints
  `SIDECAR<TAB>located_in<TAB><file><TAB>line:N<TAB>legacy-row` and
  `SIDECAR<TAB>reproducible_by<TAB><path><TAB><TAB>legacy-row` after the
  `LOCATOR` rows; `Total references` still counts graph claims only (0 for a
  bug no declaration mentions).
- Header: `Ingestion: registered declarations + sidecar bug-db/v1 <path>
  rows=<n> sha256:<hex>`. SDN: `legacy_database_ingestion: bug-db/v1`,
  `sidecar_sources: [{kind, path, sha256, rows}]`, and each bug node has
  `legacy: {table, status, severity, file, line, reproducible_by, valid,
  created_at, updated_at}`; `refs` adds `sidecar_references: [{source_kind,
  relation, path, locator, authority}]`. The source sha is part of the input
  manifest, so every cursor invalidates when the DB changes.
- `TRACE-LEGACY-ROW:` diagnostics (severity `warning`, 8 today -- rows with
  11+ fields from unescaped commas) do not affect `Graph complete`.
- Default is on when the default path exists; `--bug-db=none` turns it off and
  restores the exact pre-slice-3 output; an explicit `--bug-db=<path>` that
  cannot be read is `TRACE-LEGACY-CAPTURE` (exit 2). `git:`/`index` snapshots
  never ingest it (`legacy_database_ingestion: unavailable-for-snapshot-kind`).
- Cost on the seed: ~1 s on top of the ~4 s query (bytes via the no-follow
  reader, runtime-backed decode; the std text codec would add ~21 s).

### Which spec claims a requirement: `--spec-root` (slice 4, 2026-11-06)

The registered declaration has no `verified_by` claims, but 7,041 spec files
carry `# @req REQ-X ...` header lines. Scanning all of them per query is not
viable on the seed, so the scan is **opt-in and bounded** to the roots you
name (`--spec-root=<dir>`, repeat up to 8, <=4,096 spec files, worktree
preview only; `@cover`/`@ac` lines are ignored):

```sh
S=D:/dev/wt/seed/simple.exe
$S run src/app/traceability/query_main.spl refs requirement req:REQ-TRC-015 --spec-root=test/01_unit/app/traceability 2>/dev/null
$S run src/app/traceability/query_main.spl refs requirement req:REQ-TRC-021 --spec-root=test/01_unit/app/traceability --format=sdn 2>/dev/null
$S run src/app/traceability/query_main.spl refs requirement req:REQ-TRC-015 --spec-root=test/01_unit/app --spec-root=test/03_system/app 2>/dev/null
```

- Rows: `SIDECAR<TAB>verified_by<TAB><spec path><TAB>header<TAB>annotation-claim`
  after the `LOCATOR` rows (SDN `sidecar_references`). `annotation-claim`
  means the spec header *declares* it; nothing here ran or verified the spec.
- Only the leading header is read (`#` comment lines and a leading `"""`
  docstring); an `@req` in a test body or a string is prose.
- A requirement that no declaration registers (today `REQ-TRC-021/023`)
  still renders: `Selected: requirement req:X (undeclared; sidecar references
  only)`, `Total references: 0`, exit 0, SIDECAR rows. Without a matching
  sidecar row it stays `TRACE-QUERY-NOT-FOUND`. No node is invented.
- Header shows one `+ sidecar annotation-req/v1 <root> rows=<files>
  sha256:...` per root; the digest covers every scanned file's content, so
  cursors invalidate when any header changes. `TRACE-ANNOTATION-SCAN`
  warnings name skipped files (unsafe path, >1 MiB, not UTF-8).
- Cost on the seed: `test/01_unit/app` (2,171 specs) walks in ~30 ms; reads
  are runtime-backed. `--spec-root=test` (7k files) exceeds the 4,096 budget
  by design -- name the area.

### One-command file summary: `refs file <path>` (slice 5, 2026-11-06)

"What touches this file?" -- graph claims on the file's node, entities
declared at the path, and every sidecar row at the path (bugs
`located_in`/`reproducible_by`, requirements `verified_by`), in one page:

```sh
S=D:/dev/wt/seed/simple.exe
$S run src/app/traceability/query_main.spl refs file src/app/traceability/main.spl 2>/dev/null
$S run src/app/traceability/query_main.spl refs file src/compiler/40.mono/monomorphize/cycle_detector.spl 2>/dev/null
$S run src/app/traceability/query_main.spl refs file test/01_unit/app/traceability/legacy_bugs_sidecar_spec.spl --spec-root=test/01_unit/app/traceability --format=sdn 2>/dev/null
```

- `Selected: <kind> <node id> <path>`: the declared file node (`source:trace-cli`)
  or the captured artifact node (`artifact:<hex>`); a path that is neither
  captured nor declared but has sidecar rows shows `(not captured; sidecar
  references only)`. Nothing at all -> `TRACE-QUERY-NOT-FOUND`, exit 1.
- Claim rows are exactly `refs` rows (`incoming implemented_by
  feature:traceability ...`); `LOCATOR` rows now end with the declaring entity
  id; `SIDECAR` rows now end with the referring id (`bug:2998`,
  `req:REQ-TRC-015`). SDN adds `from` to each `sidecar_references` entry.
- No cursor: `--limit` caps claim rows (`page complete: false` when capped).
  Bugs use the exact `file` column, so pass the file path, not a directory;
  for an area use `list bugs --file-prefix=<dir>/`.
