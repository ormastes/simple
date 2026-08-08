# Rust checker rejected valid repeated-field tuple returns

**Status:** FIXED 2026-07-17

**Scope:** Rust seed type checker and `std.io_runtime.process_run`

**Severity:** bootstrap blocking

## Symptom

The Rust seed rejected a standalone compile of
`src/app/mcp/main_lazy_json.spl` with:

```text
anonymous multi-return tuple contains repeated field types; add labels to disambiguate
```

The reported declaration was:

```simple
pub fn process_run(cmd: text, args: [text]) -> (text, text, i64)
```

Changing it to a labeled tuple cleared the Rust check, but then the
pure-Simple bootstrap parser failed at the first label with `expected ), got
:`. The workaround therefore made the default self-hosted toolchain unable
to build itself.

## Root cause

`simple-type` had a special function-return check that rejected any anonymous
tuple containing two equal field types. Tuple positions already disambiguate
those fields, and repeated types are common in process, geometry, and result
APIs. The restriction was not a language rule and was absent from the
pure-Simple checker/parser.

The labeled signature was therefore an incompatible workaround, not the root
fix.

## Resolution

- Removed the repeated-field rejection from
  `src/compiler_rust/type/src/checker_check.rs`.
- Replaced its negative Rust test with a positive regression proving a
  process-shaped `(text, text, i64)` return type-checks.
- Restored `std.io_runtime.process_run` to its established positional return
  type `(text, text, i64)`.
- Kept the Simple regression coverage for indexed access, three-way
  destructuring, stdout, and nonzero exit codes.

No caller migration or parallel result API is needed. Existing `.0/.1/.2`
access and tuple destructuring keep their original ABI and behavior.

## Evidence

The focused Rust inference regression is the immediate executable gate. The
next fresh bootstrap session must also rerun the self-hosted native-build
cycle; this session stopped after its mandatory three-cycle cap, with the
labeled tuple parse error recorded in
`build/bootstrap-current/logs/stage4-native-build-cycle3.log`.
