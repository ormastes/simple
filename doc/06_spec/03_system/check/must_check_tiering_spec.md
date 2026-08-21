# Must-Check Tiering Operator Manual

## Run the lightweight push must-check

The push hook delegates to the lightweight driver. It checks only committed
tree structure, quick rules, and the textual ledger. It does not compile native
artifacts, boot QEMU, contact hardware, or run benchmark/full-test campaigns.

## Run the bootstrap must-check

The bootstrap tier owns expensive checks. On successful compiler bootstrap it
validates Stage 1 authority, Stage 2 and Stage 3 admission/sanity, and the exact
Stage 4 binary plus provenance before writing any phase PASS. It then executes
every automated bootstrap row, retaining its log under the source fingerprint;
any failed or verdict-less gate fails the bootstrap.

## Validate the must-check ledger

The push tier rejects missing, stale, malformed, duplicate, unknown, failed, or
non-passing push-blocking rows. A PASS needs its own UTC pass timestamp; a TODO
or blocked row must say `never`. TODO and blocked non-push rows remain visible
and are not reported as PASS.

Focused evidence: `sh test/01_unit/scripts/must_check_tiering_test.shs`.

## Bootstrap Caret suite

Bootstrap separately gates Claude/Codex/Gemini/Kimi process wrappers,
agent-manager messaging primitives, and the bounded multi-Caret manager. The
separate production `os.apps.smux` adapter row remains TODO. The
Slang-through-Caret local inference row also remains TODO until a real
generation request passes; `local_torch` is a distinct provider and cannot
satisfy that row.
