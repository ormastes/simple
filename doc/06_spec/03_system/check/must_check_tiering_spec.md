# Must-Check Tiering Operator Manual

Requirements: REQ-MCT-001 through REQ-MCT-009. Executable source:
`test/03_system/check/must_check_tiering_spec.spl`.

## Run the lightweight push must-check

The push hook delegates to the lightweight driver. It executes only the
registry's `push` rows, committed-tree structure, quick rules, and the textual
ledger. It does not compile native
artifacts, boot QEMU, contact hardware, or run benchmark/full-test campaigns.
Identical ref updates are deduplicated and more than two unique updates fail
closed with a split-push diagnostic. The structural tree row checks only the
committed tip and its count-only parent reference; the exhaustive 24-fixture
detector campaign belongs to bootstrap. Production evidence must resolve under
the repository root and fit the 64 MiB aggregate hashing budget.
Quick rule commands and floors are loaded from the same committed revision, not
the working tree; the fixture replaces the latter with a hostile sleep command
and requires committed policy to pass promptly.

## Run the bootstrap must-check

The bootstrap tier owns expensive checks. On successful compiler bootstrap it
validates Stage 1 authority, Stage 2 and Stage 3 admission/sanity, and the exact
Stage 4 binary plus provenance before writing any phase PASS. It then executes
every automated bootstrap row, retaining its log under the source fingerprint;
only an explicit final PASS line is accepted, so incidental earlier PASS text
cannot hide a final failure.
Every automated row receives the canonical validated Stage 4 candidate as
`SIMPLE_BINARY` and `SIMPLE_BIN`; conflicting ambient values are overridden and cannot redirect
evidence to a stale deployment.

The separate Stage-4 tooling receipt must bind a committed
`Stage4ToolingMatrixSummaryV1`. The recorder independently rejects scoped,
partial, failed, blocked, nonterminal, compiler-rebuilding, malformed, or
duplicate-field summaries; a receipt claiming PASS cannot override them.

## Validate the must-check ledger

The push tier rejects missing, stale, malformed, duplicate, unknown, failed, or
non-passing push-blocking rows. Manifest and ledger commands must agree. A PASS
needs its own UTC pass timestamp plus an existing evidence file whose SHA-256
matches the ledger's blob in the exact pushed revision; live-worktree bytes are
not evidence. A TODO
or blocked row must say `never`. TODO and blocked non-push rows remain visible
and are not reported as PASS.

An unfinished receipt row becomes PASS only through
`--record-gate-pass <id> --evidence <repo-relative-committed-receipt>`. Repeating
the same receipt preserves the first PASS time. The committed receipt uses
`simple.must-check-gate-receipt/v1`, names the exact gate and source
fingerprint, states a final PASS, and hash-binds a separate committed artifact;
plain text and mismatched receipts fail closed. Later fingerprints carry it
only while the exact committed blob/hash remains. Automated results remain
source-fingerprint scoped. Bootstrap recording refuses dirty fingerprinted
inputs, and automated/phase evidence is retained under
`doc/08_tracking/check/evidence/<source-fingerprint>/` for the ledger commit.
A bare recorder invocation cannot run automated rows or mutate the ledger;
promotion requires exact Stage 1–4 admission through
`--record-bootstrap-success`. Ledger completion remains `never` while any row
is unfinished and otherwise records the latest first-PASS timestamp.

Every ledger v3 row also names its owner and unblock condition. Unowned rows,
unfinished rows without actionable unblock text, and PASS rows that retain a
pending unblock condition fail closed. The focused fixture obtains its PASS
ledger from the bootstrap producer and then feeds that committed result through
the real pre-push ref-input path. It also creates two linked worktrees with one
shared Git hooks directory, installs from the first, and validates hook
freshness and wiring from the second. The installed payload is a stable
worktree-resolving launcher, not an absolute symlink to whichever checkout ran
setup last. Exact legacy guard or dispatcher payloads are replaced without
being preserved recursively; unrelated local hooks remain chained.
The Unix behavior is executable in the focused fixture. Native Windows
linked-worktree installation remains the visible `windows-hook-installation`
TODO and is not inferred from PowerShell source parity.

Focused evidence: `sh test/01_unit/scripts/must_check_tiering_test.shs` produced
`selftest=5s ref-path=0s two-ref=0s installed-hook=0s` on 2026-08-22 after
adding bounded ref/evidence handling and moving exhaustive tree fixtures to
bootstrap. The complete fixture took 11.18s with 59,136 KiB peak RSS; that
total includes temporary Git repositories and linked-worktree setup outside
the individually bounded NFR paths.
The real committed-tree path over the 118,074-file repository then passed all
five production gates for commit `4686d81b3bd` in 5.40s at 211,932 KiB peak
RSS, scanning the 33 changed files and retaining every visible bootstrap TODO.

The executable scenario invokes the push self-test, bootstrap self-test,
Sdoctest bootstrap structural self-test, and the real bootstrap-produced-ledger
to committed-ref push transition fixture. Its assertions require explicit PASS
markers, exact Stage 4 binding, and timing fields. This manual was
reviewed against that source; regeneration remains pending until an admitted
Stage-4 CLI is available in the worktree.

The Sdoctest bootstrap row first executes the named Markdown fixture
`test/fixtures/doctest/green.md` and named source-comment fixture
`test/fixtures/doctest/green.spl`, then runs the whole tree.
Both `Sdoctest:` and `SPL Doctest:` summaries must report at least one passing
case with zero failures and zero skips; the aggregate `Results:` count alone is
insufficient.

## Bootstrap Caret suite

Bootstrap separately gates Claude/Codex/Gemini/Kimi process wrappers,
messaging primitives, and the bounded injected-command batch adapter. Those
fixture gates do not prove the separate production agent-runtime or sustained
multi-manager rows. Installed providers, both production runtime rows, and the
production `os.apps.smux` adapter remain TODO. The
Slang-through-Caret local inference row also remains TODO until a real
generation request passes; `local_torch` is a distinct provider and cannot
satisfy that row.

Stage 4 compiler admission does not promote the separate 49-row CLI/MCP/LSP
tooling matrix. Web and database handlers do not promote their real configurable
listener-port rows. GPU admission decisions do not promote output parity:
retained evidence must prove identical CPU/device results, real device hits,
and equivalent nginx or PostgreSQL/MySQL fixtures.
