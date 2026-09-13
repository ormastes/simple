# Native enum text payload becomes a decimal pointer

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Status (2026-07-15 -> CLOSED-STALE 2026-09-12):** Pure-Simple enum payload typing fix landed. Strict
default-LLVM + explicit-Cranelift callback/match/field-assignment regression added to
`scripts/check/check-native-seed-parity.shs`; execution awaits a fresh
pure-Simple compiler binary.

## Symptom

In the compiled UI access checker, `UIEvent.Action(name: "run")` reaches
`UISession.dispatch` with a value that serializes as a decimal pointer (for
example `679740705`) instead of `run`. Interpreter-focused tests hang and do
not provide contrary evidence.

## Reproducer

Build `scripts/check/check-ui-cli-access.spl` with the canonical Cranelift
entry-closure command recorded in `.spipe/ui-cli-llm-access/state.md`, then run:

```sh
build/bootstrap/ui-cli-access-link-root-20260712/check-ui-cli-access-final --scenario live-tui-loop
```

The retained snapshot contains an `action` event whose payload is numeric,
while the adjacent request/result events retain their text correctly.

## Expected

Text stored in an enum variant must remain tagged text across construction,
callback delivery, pattern binding, and assignment to another text field.

## Owner and constraints

Owner: native enum construction/pattern-binding lowering. Fix once in the
compiler; do not add UI-local pointer formatting, runtime aliases, or fake
history events. Add a minimal native regression that constructs a text-bearing
enum, passes it through a callback, pattern-matches it, and asserts the text.

## Triage 2026-09-12
The 2026-07-15 status already noted execution awaits a fresh pure-Simple compiler binary; still unexecuted 2 months later. Older than 45 days with no cheap repro re-run; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
