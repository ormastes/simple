# Stage 2 multiline `if` continuation divergence

Date: 2026-08-14
Status: OPEN
Owner: compiler frontend

The freshly rebuilt bootstrap seed accepts the parenthesized multiline
condition in
`src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl`, while the
Stage 2 self-host parser rejected the unparenthesized equivalent at the newline
before `and` with `expected :, got Newline`.  The compact form is intended to
remain valid language syntax; bootstrap recovery uses explicit grouping until
the Stage 2 parser's continuation handling is brought into parity.

Reproducer:

```text
if first
    and second:
    return true
```

Expected: the continued boolean condition parses identically across seed and
self-hosted stages.  Actual: Stage 2 terminates the condition after `first`.

Regression gate needed: parse the reproducer through both the core/bootstrap
parser and the deployed self-hosted parser, then remove the explicit grouping
workaround only after both accept it.
