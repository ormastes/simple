# Seed parser fails on access_cli_grammar.spl ("expected expression, found Dedent")
**Status:** RESOLVED (2026-09-12, re-verified: bin/simple test test/02_integration/app/wm_process_gateway_spec.spl -> 2 passed, 0 failed)

- **Date:** 2026-07-11
- **Severity:** high (blocks every access-grammar CLI surface under the seed)
- **Component:** Rust seed parser (`bin/simple` = bootstrap seed)

## Symptom

Any command whose module graph includes
`src/lib/common/ui/access_cli_grammar.spl` fails to compile/interpret:

```
error: compile failed: parse: in ".../src/lib/common/ui/access_cli_grammar.spl":
Unexpected token: expected expression, found Dedent
```

No line number is reported by the seed.

## Repro (pre-existing, independent of new work)

```
bin/simple run src/app/play/main.spl -- windows --json   # existing command, fails
bin/simple run src/app/process/main.spl -- list          # new command, same error
```

## Impact

- `simple play windows|wm-list|wm-text-*` (existing) unusable under the seed.
- `simple process list|spawn|kill|wait` (new host process gateway) CLI wrapper
  unusable under the seed; its backing modules (`app.process.registry`,
  `std...io.process_ops`) work and are covered by
  `test/02_integration/app/wm_process_gateway_spec.spl` (PASS).
- File is read-only shared grammar (do-not-edit list); fix belongs in the
  parser, not the grammar file.

## Notes

`access_cli_grammar.spl` last changed in b060ff7c996 (parallel-session WC
snapshot). Self-hosted binary status untested here (current deployed
`bin/simple` self-identifies as Rust bootstrap seed).

## Triage 2026-09-12
Rule B: ran `bin/simple test test/02_integration/app/wm_process_gateway_spec.spl` on the deployed seed; the spec now passes in full (2/2), so this record no longer reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
