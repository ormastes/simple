# Stage 4 duplicate checker uses unresolved `float` conversion

## Status

Resolved in source on 2026-08-04; the next x86 Phase 4 blocker is tracked
separately in `stage4_db_atomic_physical_owner_2026_08_04.md`.

## Symptom

The final bounded Phase 4 cycle parsed all 1,351 surfaces and crossed the CLI
lint, CLI handler, and leak-check repairs. HIR lowering then reported four
`unresolved name: float` diagnostics in
`src/compiler/tools/duplicate_check/main.spl`.

## Exact sites

- similarity threshold positional option;
- similarity threshold `--name=value` option;
- semantic threshold positional option;
- semantic threshold `--name=value` option.

## Repair and evidence

The four legacy constructors now use the canonical optional
`text.parse_float()` method. A failed parse becomes the existing out-of-range
sentinel and is rejected by `config_validation_error`; malformed CLI values
therefore retain exit 2 instead of becoming a valid zero threshold.

`test/03_system/native/stage4_duplicate_check_hir_contract.spl` retains both
malformed split/equal forms. The focused native shard crossed parsing, HIR, and
object generation, then stopped only at the deliberately narrow core bundle's
unrelated `rt_http_request` link boundary. Production Phase 4 cycle 1 crossed
all four sites and advanced to `test_runner_main.spl`.
