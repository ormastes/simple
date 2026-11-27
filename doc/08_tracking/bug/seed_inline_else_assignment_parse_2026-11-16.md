# Seed parser rejects assignment as inline `else:` body

Status: verification-pending (source workaround landed; parser itself not fixed)

Repro (Rust seed, Windows `bin/simple.exe`):

```
if index == a.len(): a.push(2)
else: a[index] = 3
```

Error: `parse: Unexpected token: expected expression, found Assign at line N, column M`.
The seed parses the inline `else:` body as an expression, not a statement, so an
assignment fails. Inline `if x: stmt` with assignment is not affected the same way
in the cases tried; only the `else:` arm was reproduced.

Impact: `src/lib/nogc_sync_mut/io/host_identity_store_windows_v1.spl:355` failed to
parse, so every spec importing it (e.g. `test/01_unit/app/llm_caret/observer/codex_skill_signal_spec.spl`)
reported outcome=ERROR executed=0.

Workaround (tagged `WORKAROUND(seed-inline-else-assign)` in that file): block-form `if/else`.
Real fix: seed parser should parse an inline `else:` body as a statement.
Regression spec: `test/01_unit/lib/nogc_sync_mut/io/host_identity_store_windows_v1_parse_spec.spl`.
