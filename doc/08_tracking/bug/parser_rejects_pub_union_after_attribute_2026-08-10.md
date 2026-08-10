# Parser rejects `pub union` after an attribute (`pub enum` works)

**Status:** OPEN
**Found:** 2026-08-10 by stream J4 (duplicate-test-tree merge, step 1)
**Component:** `src/compiler/10.frontend/core/_ParserDecls/`
**Binary:** `src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, mtime 2026-08-09 23:10)

## Symptom

An attribute immediately preceding a `pub union` declaration is a hard parse error:

```
error: compile failed: parse: ...: Unexpected token: expected Fn, found Union
error: test-runner: no examples executed
```

The attribute path evidently accepts `pub enum` (that case is covered and green)
but never learned `pub union`, so it falls through to the function parser.

## Repro

```simple
@doc("Parser regression tagged union")
pub union Tagged:
    Int(i64)
    Text(text)
```

## Why this was invisible

`test/unit/compiler/parser/pub_enum_with_attribute_spec.spl` (legacy tree)
carries exactly this case. Its numbered twin,
`test/01_unit/compiler/parser/pub_enum_with_attribute_spec.spl`, has the `union`
block and its header sentence removed — the coverage was deleted rather than the
bug fixed, and because the legacy tree also executes, nobody saw a failure: the
legacy file must already have been failing silently in the full-suite noise.

## Blast radius note

The failure is a *file-level parse error*, so restoring the union case into the
numbered spec zeroes the other 6 examples in that file (exit 1, `no examples
executed`, no `SPEC FILE VERDICT` line) rather than producing one RED example.
For that reason step 1 left the numbered file at its origin content and filed
this bug instead of landing a spec that executes nothing. Re-add the union block
to the numbered spec as part of the fix.
