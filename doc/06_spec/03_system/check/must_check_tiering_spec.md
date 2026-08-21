# Must-Check Tiering Operator Manual

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

Focused evidence: `sh test/01_unit/scripts/must_check_tiering_test.shs`.

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
