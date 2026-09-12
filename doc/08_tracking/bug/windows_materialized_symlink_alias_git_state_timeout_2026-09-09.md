# Windows materialized symlink aliases make the Stage 3 Git-state receipt time out

- **ID:** `windows_materialized_symlink_alias_git_state_timeout_2026-09-09`
- **Date:** 2026-09-09
- **Status:** OPEN
- **Severity:** P1
- **Owner:** bootstrap provenance / Windows checkout materialization
- **Component:** `scripts/check/lib/bootstrap-stage3/authority.shs`

## Current evidence

The Windows bootstrap wrapper runs
`scripts/setup/materialize-symlinks-windows.shs` before the staged pipeline.
The materialized junction/hardlink aliases are usable by the Simple loader, but
the current `bootstrap_stage3_git_state` consumer inventories their expanded
surface as Git/untracked state.

Read-only reconnaissance on the failing checkout found 116 mode-120000 entries
at HEAD. `git ls-files --others --exclude-standard` produced 42,357 paths, and
the helper's `.files-only.1800` work queue contained 24,801 regular files. The
external oracle ran from epoch 1788959100 through 1788959130 and exited 124 at
the 30-second bound. It left no final Git-state receipt and seven temporary
residues. Bootstrap session 91580 consequently exited 1 with the generic
diagnostic `could not bind Stage 3 git HEAD/dirty state`, so Stage 2 was not
admitted.

These counts are reconnaissance/oracle evidence, not a retained per-path
receipt. This is not evidence that Stage 2 compilation failed: the refusal is
at the post-build provenance boundary, and fail-closed non-admission is correct
when the Git-state receipt is incomplete.

## Distinction and related bugs

- `windows_git_symlinks_materialize_as_path_text_2026-09-02.md` establishes why
  Windows checkouts require materialization and verifies that materialized
  sources load. Removing materialization would regress that fix.
- `bootstrap_reads_transiently_broken_shared_working_copy_2026-09-05.md` covers
  torn source reads caused by concurrent writers. This failure is at the
  Git-state inventory boundary even without a torn `.spl` read.
- `stage2_admission_source_quiescence_unsatisfiable_in_shared_tree_2026-08-31.md`
  covers real source changes across a long build. Here one Git-state snapshot
  cannot complete, so the before/after equality is never reached.
- `bootstrap_stage3_untracked_fingerprint_process_storm_2026-08-11.md` removed
  per-file hashing processes for large ordinary untracked sets. Materialized
  aliases remain an input-policy and canonicalization gap.

## Required two-part remediation

### 1. Receipt producer

The Windows materializer must emit a deterministic, bounded receipt before the
bootstrap starts. It must bind repository-relative alias path, original Git
mode-120000 target bytes, materialization kind (junction or hardlink), resolved
in-checkout target, and materializer policy digest/version. It must reject
missing, escaping, cyclic, nested-repository, and unexpected aliases. Bind the
receipt to the same source snapshot and planner admission used by Stage 2; a
caller-supplied exclusion list is not authority.

### 2. Git-state consumer

`bootstrap_stage3_git_state` must verify that receipt, collapse every admitted
materialized alias to its canonical Git symlink identity, and not recursively
inventory the target again through the alias. Every other tracked, untracked,
nested-repository, executable-bit, and content binding remains fail-closed. A
typed terminal record must retain path count, collapsed-alias count, elapsed
time, and first rejected path, and cleanup must remove bounded temp residues.

## Closure oracle

### v2 producer receipt contract (2026-09-10)

The receipt is strict UTF-8, LF-terminated, with headers before one
`records_begin` / `records_end` block and no trailing data. The unique exact
header set is `schema`, `root`, `head`, `producer_sha256`, `policy_sha256`,
`tracked_mode120000`, `created`, `already_ok`, `skipped_pending`, `failed`,
`pending_untracked`, `record_count`, `records_sha256`, `pending_count`,
`pending_requires_consumer_revalidation`, and `result`. Snapshot bindings must
match the producer invocation. `schema=simple-windows-materialized-links-v2`,
`result=complete`, `failed=0`, `skipped_pending=0`, and
`pending_requires_consumer_revalidation=1` are mandatory. Counts use canonical
nonnegative decimal (no sign or leading zero), bounded by 2147483647.
`created + already_ok + pending_untracked = record_count = tracked_mode120000`;
`pending_untracked = pending_count`. Row states must reproduce those counts.

Every row has exactly twelve ordered fields: `path_len`, `path_hex`,
`target_len`, `target_hex`, `target_resolved_len`, `target_resolved_hex`,
`target_volume`, `target_file_id`, `target_size`, `target_sha256`, `kind`,
`state`. Path and target hex is lowercase, even, strict UTF-8, at most 131068
decoded bytes, with exact byte lengths. Paths are unique repository-relative
normalized Windows-safe components using `/`. Targets may begin with `../`
but otherwise use normalized components; resolving from the alias parent must
stay strictly inside the repository and differ from the alias. Absolute,
empty, dot, internal parent, backslash, reserved-device and invalid components
are rejected. Materialized rows allow only `file` or `directory` with `created`
or `already`; all native metadata must match a fresh held-handle capture.
Native volume and each ID half are uint32, size is uint64, resolved length is
bounded by 131068 with strict UTF-8 extended-DOS drive namespace. File SHA is
64 hex digits; directory SHA is `-` (no tree digest).

Pending rows require `kind=unknown`, `state=pending-untracked`,
`target_resolved_len=0`, and exactly `-` in every remaining native metadata
field. Publication opens the policy once, hashes and tests exact membership
from the same captured bytes, and retains its identity, read handle and
ancestor handles through the no-replace receipt rename. Earlier shell policy
checks are preliminary; this held snapshot is publication authority.

Producer post-publication invalidation is best effort: absence cannot be
locked against future creation. Every future consumer **MUST** revalidate
target absence, exact placeholder bytes, and exact policy membership
immediately before alias use. Pending records are **never** excluded from
this requirement, including when this receipt is otherwise valid. Consumer
implementation and end-to-end admission remain separate, unfinished work.

### Part 2 consumer implementation (2026-09-10)

`bootstrap_stage3_git_state ROOT OUTPUT RECEIPT` now routes a nonempty receipt
to a read-only Windows native consumer in the existing Stage3 authority.
Omitted/empty third arguments inherit `SIMPLE_WINDOWS_MATERIALIZED_LINKS_RECEIPT`,
so existing bootstrap, recovery, and resume calls consume the wrapper binding.
The receipt path is mandatory for this branch; receipt refusal never falls back
to ordinary inventory. The existing non-receipt branch is unchanged.

Admission verifies the exact v2 header/field set, canonical counts, row digest,
producer/policy bytes, root, HEAD, and one exact path/target row per HEAD symlink
blob. Every alias and target is revalidated through native handles. Policy,
placeholder, alias, target, and scanned ordinary filesystem handles deny
write/delete sharing through Git inventory. Pending policy membership and
placeholder bytes are checked from held bytes, with absence checked immediately
before inventory and again before publication. Blocked-dirty inventory is not
an authorizing receipt.

Only verified directory junctions contribute `:(top,literal,exclude)PATH`
pathspecs to `git ls-files --others --exclude-standard -z`. A bounded preliminary
walk inspects immediate entries and skips those aliases without traversing them;
unreceipted reparses, nested repositories, unsafe paths and case collisions fail
closed. It also inspects ignored ordinary directories, conservatively refusing
unsupported topology there. File and pending rows never create exclusions.
Tracked diff bytes remain Git's normal binary HEAD diff. Ordinary untracked
records use UTF-8 byte lengths, C byte ordering, MSYS executable flags and raw
file SHA-256, preserving the existing fingerprint format.

The output additionally contains `alias_collapse_count`,
`alias_collapse_sha256`, and C-byte-sorted records
`alias-collapse-directory:UTF8_BYTE_LENGTH:LOWERCASE_PATH_HEX`. The collapse
digest hashes those exact LF-terminated records. It is separate from the dirty
fingerprint and excludes producer-created/already distinctions. This retains
normal dirty tracked evidence; it does **not** claim equality to a native-symlink
checkout's tracked diff.

Hard ceilings: 30-second native process timeout (2-second forced termination
grace), 28-second internal operation budget, 100,000 cumulative HEAD/tree
entries, 4,096 aliases, 512 MiB cumulative input bytes, 8 MiB receipt,
1 MiB policy/producer, and 16 MiB per Git/child output stream. The environment
variables `BOOTSTRAP_STAGE3_GIT_MAX_ENTRIES`, `BOOTSTRAP_STAGE3_GIT_MAX_BYTES`,
and `BOOTSTRAP_STAGE3_GIT_MAX_MILLISECONDS` may only lower their ceilings.
Private temporary files are removed on refusal/signals. Success publishes with
a native same-volume, no-replace rename; an existing output is preserved and
refused. No partial stdout or destination is emitted.

Focused oracle:
`test/02_integration/bootstrap_stage3_git_state_materialized_test.shs`.
It creates only a disposable synthetic Git repository, invokes the existing
producer there, checks directory-only collapse, exact untracked bytes and dirty
tracked preservation, and exercises receipt/identity/pending/topology/budget
refusals. Runtime outcome is recorded below after its single authorized run.

Remaining limitations: pending absence cannot be locked against creation;
directory handles do not establish an immutable subtree snapshot. Quiescent
source capture remains a separate admission requirement. The conservative
ignored-tree audit may exhaust bounds on large checkouts. Receipt and source
hashes are local integrity bindings, not cryptographic producer signatures.
Real-checkout performance, full bootstrap, and end-to-end admission are untested.

#### Single authorized consumer test attempt

Executed once, from `C:/Users/ormas/dev/simple`, with this PowerShell command:

```powershell
$ErrorActionPreference = 'Stop'
$stage3ConsumerTemp = Join-Path 'C:/Users/ormas/AppData/Local/Temp' ('simple-stage3-consumer-' + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $stage3ConsumerTemp | Out-Null
$env:STAGE3_TEST_TMP_WINDOWS = $stage3ConsumerTemp
Write-Output ('TMP_ROOT=' + $stage3ConsumerTemp)
& 'C:/dev/tool/msys2/usr/bin/sh.exe' -c '. ./scripts/setup/host-env.shs && host_env_apply_path && TMPDIR=$(cygpath -u $STAGE3_TEST_TMP_WINDOWS) && export TMPDIR && /usr/bin/sh test/02_integration/bootstrap_stage3_git_state_materialized_test.shs'
$stage3ConsumerExit = $LASTEXITCODE
Write-Output ('FOCUSED_TEST_EXIT=' + $stage3ConsumerExit)
exit $stage3ConsumerExit
```

PowerShell created
`C:/Users/ormas/AppData/Local/Temp/simple-stage3-consumer-8ffae3fa055d4705bd4e94d7fd3638e3`.
The focused script then exited **1** during setup, reporting three
`mkdir: cannot create directory ‘/c/Users/ormas’: Permission denied` messages
and `FAIL case=setup line=22 exit=1`. Consumer assertions were not reached.
No retry, additional test, bootstrap, real checkout materialization, fetch,
commit, or push was performed. Implementation and fixtures remain
runtime-unverified; this report is **not** a verification PASS. No implementation
edits were made after the failed run.

On a `core.symlinks=false` Windows checkout, strict materialization followed by
the Git-state snapshot must complete within 30 seconds, produce the same
logical digest as an equivalent native-symlink checkout, name zero unreceipted
aliases, and permit Stage 2 admission when every other sanity, receiver,
source, tool, and runtime receipt is unchanged. Ablations for a changed target,
escaped target, missing receipt row, and extra junction must each refuse Stage
2 admission.
