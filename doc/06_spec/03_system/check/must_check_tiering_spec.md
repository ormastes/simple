# Must-Check Tiering Operator Manual

Requirements: REQ-MCT-001 through REQ-MCT-006. Executable source:
`test/03_system/check/must_check_tiering_spec.spl`.

## Run the lightweight push must-check

The push hook delegates to the lightweight driver. It executes only the
registry's `push` rows, committed-tree structure, quick rules, and the textual
ledger. It does not compile native
artifacts, boot QEMU, contact hardware, or run benchmark/full-test campaigns.

## Run the bootstrap must-check

The bootstrap tier owns expensive checks. On successful compiler bootstrap it
validates Stage 1 authority, Stage 2 and Stage 3 admission/sanity, and the exact
Stage 4 binary plus provenance before writing any phase PASS. It then executes
every automated bootstrap row, retaining its log under the source fingerprint;
only an explicit final PASS line is accepted, so incidental earlier PASS text
cannot hide a final failure.

## Validate the must-check ledger

The push tier rejects missing, stale, malformed, duplicate, unknown, failed, or
non-passing push-blocking rows. Manifest and ledger commands must agree. A PASS
needs its own UTC pass timestamp plus an existing evidence file whose SHA-256
matches the ledger; a TODO
or blocked row must say `never`. TODO and blocked non-push rows remain visible
and are not reported as PASS.

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
`selftest=5s ref-path=0s installed-hook=0s` on 2026-08-22 after adding the
Windows TODO row.

The executable scenario invokes the push self-test, bootstrap self-test, and
the real bootstrap-produced-ledger to committed-ref push transition fixture.
Its assertions require explicit PASS markers and timing fields. This manual was
reviewed against that source; regeneration remains pending until an admitted
Stage-4 CLI is available in the worktree.

The Sdoctest bootstrap row additionally requires both the Markdown `Sdoctest:`
and source-comment `SPL Doctest:` summaries to report at least one passing case
and zero failures; the aggregate `Results:` count alone is insufficient.

## Bootstrap Caret suite

Bootstrap separately gates Claude/Codex/Gemini/Kimi process wrappers,
agent-manager messaging primitives, and the bounded multi-Caret manager. The
separate production `os.apps.smux` adapter row remains TODO. The
Slang-through-Caret local inference row also remains TODO until a real
generation request passes; `local_torch` is a distinct provider and cannot
satisfy that row.
