# Interpreter extern gap push ratchet attributed mainline debt to topics

## Symptom

A SciLib topic based directly on current `origin/main` failed the blocking
interpreter-extern registry gate with 11 new and 3 stale symbols, although its
commit changed neither compiler extern declarations nor the Rust registry.

## Root cause

Push admission compared the topic tree with an older frozen baseline. Current
mainline drift was therefore reported as topic debt.

## Fix and evidence

The checker accepts `--baseline-rev` with `--rev` and derives the comparison
gap set from that committed base. Push dispatch supplies the outgoing range
base. New topic gaps fail; unchanged or removed gaps pass. Standalone scans
retain strict frozen-baseline and stale-row enforcement.

- Checker selftest: PASS, 9 numbered fixtures.
- SciLib tip versus its parent: PASS, 220 declarations and zero new gaps.
