# `auto` is a hard keyword: rejected as a named-argument label

**Date:** 2026-09-05 · **Status:** OPEN · **Class:** reserved token rejected at the USE site
(same family as `examples`/`and_then` 2026-08-10, `move` 2026-08-15, `admit`/`assume` 2026-08-21).

## Symptom

`auto` lexes as `TokenKind::Auto` (`src/compiler_rust/parser/src/lexer/identifiers.rs:184`).
A struct field named `auto` declares, reads (`.auto`), binds (`val auto`), and constructs
positionally without error, but the named-argument constructor form fails:

```text
error: compile failed: parse: in "...": function arguments: expected Comma, found Colon
```

Minimal repro (7 lines):

```simple
struct P:
    auto: bool
    n: i64

fn main():
    val p = P(auto: true, n: 1)   # <- parse error; P(true, 1) works
    print(p.n)
```

Found while implementing `FrontendOffloadSwitch.auto` in
`src/compiler/00.common/structural_contracts/frontend_offload_switch.spl`
(lane `gpu_frontend_offload`, Wave 0). Binary:
`bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed).

## Workaround in place

Both construction sites use positional arguments with a one-line comment naming
this record. The frozen field name was kept deliberately; renaming would hide
the defect instead of tracking it.

## Fix

Make `auto` contextual in the named-argument position, exactly as
`src/compiler_rust/parser/src/expressions/helpers.rs` already does for
`examples`/`and_then` and the other soft keywords. Requires a rebuilt seed.

## Unblock condition

Regression spec `test/01_unit/compiler/parser_auto_contextual_keyword_spec.spl`
(to add with the fix) parses `P(auto: true)`; then drop the positional
workaround in `frontend_offload_switch.spl`.
