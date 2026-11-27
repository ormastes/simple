# Simple grammar: struct field named like a reserved word breaks named-argument construction

Status: WORKED AROUND 2026-11-10; language fix owned by the compiler team.

## Symptom

`parse: ... function arguments: expected Comma, found Colon` with NO line
number, reported against the importing file, whenever a struct whose field is
named `spawn` is constructed with named arguments:

```spl
struct ProbeRet:
    a: i64
    spawn: i64

val r = ProbeRet(a: 1, spawn: 3)   # parse error: expected Comma, found Colon
val r = ProbeRet(1, 3)             # positional: parses, and r.spawn reads fine
```

Minimal repro verified 2026-11-10 on the Windows interpreter lane. The parser
treats the `spawn:` label as foreign syntax inside the argument list, i.e. the
callee is parsed as an ordinary function call, not a struct constructor.

## Blast radius on release/1.0.0

Blocked 8 caret unit specs (agent_workspace, agent_worktree_release,
cs_dashboard, cs_main, main, multimodal_proxy, pane_backend,
pane_backend_windows) plus the `host_helper_settlement_v1` system spec through
two structs:

- `HostHelperStreamRetainedV1.spawn` (src/lib/nogc_sync_mut/orchestration/host_helper_stream_owner_v1.spl)
- `ContainerOutputTurnV2.spawn` (src/lib/nogc_async_mut/container/stream_v2.spl)

Field DECLARATION and `.spawn` field ACCESS both parse; only named-argument
construction is rejected. Other files declare `spawn:` fields without
constructing them by name and were unaffected.

## Workaround applied

Renamed both fields to `child_spawn` (definition, all named-argument
construction sites, and the one `.spawn` accessor in
host_helper_settlement_v1.spl). Named-argument construction is the house
style; positional construction would have been a fragile workaround.

## Suggested language fix

Either reserve `spawn` (and friends) as illegal struct field names with a
clear diagnostic at the declaration site, or make named-argument parsing
context-aware so a known struct type's field labels parse regardless of
keyword overlap. The current failure mode (line-number-less parse error at
every importer) costs far more to diagnose than either option.

## Addendum 2026-11-12 — compiler-lane investigation (work/compiler-ctor-field-bugs-20261112)

The doc filename says `ctor`; the body and workaround describe `spawn`. Both
were investigated on release/1.0.0 (HEAD 35e7682892a). Findings:

### `ctor` is not reserved anywhere (title premise does not hold)

- Pure-Simple lexer: `keyword_lookup` (src/compiler/10.frontend/core/tokens.spl:369)
  has no `ctor` entry; `ctor` lexes as an ordinary identifier (TOK_IDENT).
- Rust seed lexer: `src/compiler_rust/parser/src/lexer/identifiers.rs` has no
  `ctor` keyword arm.
- Empirical: `struct Foo:\n    ctor: i64` with `Foo(ctor: 42)` and `.ctor`
  access parses AND runs on the seed binary, and parses through the canonical
  pure-Simple frontend (`parse_full_frontend` / `parse_module`). No fix exists
  to make; no parser change was needed.

### Reproducible defect is the doc body's `spawn` case, seed-side only

- Seed: `ProbeRet(a: 1, spawn: 3)` fails with the documented
  "function arguments: expected Comma, found Colon" (no line number), because
  the seed reserves `spawn` (`"spawn" => TokenKind::Spawn`,
  identifiers.rs:227) and its call-argument parser rejects keyword tokens as
  labels.
- Canonical pure-Simple parser already accepts keywords as named-argument
  labels: `parse_call_arg_raw` (src/compiler/10.frontend/core/parser_expr.spl:758-771)
  does a snapshot lookahead (`ident:` / `ident =`) for any `keyword_lookup`
  token before keyword-specific primary parsing, and struct-field parsing
  (`fn_struct_decls.spl`, `use_kw_segment_text`) already accepts keyword-named
  fields. The `spawn:`/`ctor:`/`type:` named-argument forms all parse with
  labels intact.

### Consequence

This is a seed-vs-canonical divergence, not a canonical-parser bug. Per lane
ownership, the seed-side fix (context-aware named-argument labels in
src/compiler_rust) belongs to the seed lane; the canonical behavior is pinned
by test/01_unit/compiler/frontend/reserved_word_struct_field_named_ctor_spec.spl.
The single-line form `struct Foo: ctor: i64` fails with "expected Indent" for
ANY field name (verified with plain `bar`) — that is generic indentation
syntax, not keyword-related.
