# Self-host optional-presence continuation rejected during Stage 3

## Failure

An exact `fd6770081b5` full bootstrap admitted Stage 2, then Stage 2 rejected
`typed_storage_view_producer.spl` at a condition shaped as:

```simple
if predicate and optional_value.?
    and another_predicate:
```

The parser emitted `expected :, got Newline`, then the Stage-3 native build
segfaulted (exit 139) instead of stopping with a normal parse-error status.

## Root cause

The self-host lexer suppresses a newline before a deeper leading binary
operator only when the prior token passes `token_can_end_expr`.  The postfix
`value.?` spelling is tokenized as `TOK_DOT_QUESTION`, but that terminal was
missing from the predicate.  The Rust seed already accepted the form, which
allowed Stage 2 to build and exposed the frontend parity defect only at Stage 3.

## Repair and evidence

`TOK_DOT_QUESTION` is now an expression terminal.  The focused leading-operator
spec parses and evaluates true, false, and nil optional values across the exact
postfix-presence plus leading-`and` boundary.  A fresh full bootstrap remains
the release gate because the previous failure occurred only under self-host.

The secondary crash-after-parser-error is retained as a distinct hardening gap;
this grammar repair must not be cited as proof that malformed input exits
without a signal.
