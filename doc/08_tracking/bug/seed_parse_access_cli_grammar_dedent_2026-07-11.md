# Seed parser fails on access_cli_grammar.spl ("expected expression, found Dedent")

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
