# `examples` is an undocumented contextual keyword: rejected as a named argument (2026-08-10)

**Status: FIXED 2026-08-17.** Resolution 1 (make them contextual everywhere)
was taken, for both members of the census family:

- `examples` — `TokenKind::Examples` added to the named-arg label match in
  `src/compiler_rust/parser/src/expressions/helpers.rs`.
- `and_then` — `TokenKind::AndThen` added at the same site (commit
  `5f8ddf3b7aa`), plus every soft keyword the label match accepts is now
  listed in `is_likely_named_arg` so a *missing comma* before one produces the
  specific "expected comma before argument '<name>'" diagnostic rather than the
  generic `expected Comma, found Colon`.

Parameter-name and field-name positions were already fine: `expect_identifier`
(`parser_helpers.rs:882`) has accepted both tokens all along — only the
named-arg path was missing them, which is why declare/read worked and
construct did not.

Regression spec: `test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl`
(mirrored to `test/unit/compiler/...`). It asserts the whole census table:
`examples`, `and_then`, `feature`/`scenario`/`given`/`when`/`then`,
`describe`/`it`/`context`, `grid`.

**A rebuilt seed is required** — any `bin/simple` older than 2026-08-17 still
reproduces the original error, so a red run of that spec on a stale binary is
binary provenance, not a live defect.

## Observation

A struct field named `examples` **declares** fine and **reads** fine, but
constructing the struct with `Foo(examples: xs)` is a **parse error**.

## Minimal repro (verified 2026-08-10)

```simple
struct K:
    examples: text

fn main():
    val k = K(examples: "ok")
    print(k.examples)
```

```
$ bin/simple run kx.spl
[INFO] JIT compilation failed, falling back to interpreter: module load error:
  parse: in ".../kx.spl": function arguments: expected Comma, found Colon
error: compile failed: parse: in ".../kx.spl":
  function arguments: expected Comma, found Colon
```

Exit code is **0** (the known "runtime/compile error exits 0" fail-open — see
`unknown_field_silent_phantom_write_fail_open_2026-08-10.md`), so a script that
only checks `$?` sees this as success.

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
**29,577,536 bytes, mtime 2026-08-09 04:50** — self-reports as the Rust
bootstrap seed ("this Rust-built Simple binary is a bootstrap seed only").

## Evidence it is specific to this identifier

Same file shape with the field renamed passes and prints `ok`. Verified
directly for `params`; the SAML lane additionally exercised, without error,
every one of: `params`, `prompt`, `attributes`, `doc`, `client`, `asserts`,
`evidence_source`, `name`, `line`, `values`, `fields`, `return_type`,
`functions`. Only `examples` fails.

Control run:

```
$ bin/simple run ky.spl      # struct K: params: text ; K(params: "ok")
ok
```

## Mechanism (seed parser)

`examples` is lexed as a dedicated keyword token, not an identifier:

- `src/compiler_rust/parser/src/lexer/identifiers.rs:290` — `"examples" => TokenKind::Examples`
- `src/compiler_rust/parser/src/token.rs:316` — `Examples, // examples name: (data table with two-space delimiter)`

It exists for the Gherkin/SPipe `examples name:` data-table block
(`src/compiler_rust/parser/src/stmt_parsing/gherkin.rs`). The field-declaration
and field-access paths tolerate a keyword in name position; the **named-argument**
path in `function arguments` does not — it sees `TokenKind::Examples` where it
requires `Identifier`, then demands `Comma` and reports the following `Colon`.
So this is a contextual-keyword leak, not a deliberate reservation: the error
message never mentions `examples`, which is what makes it hard to diagnose.

It is also **undocumented** — `.claude/rules/language.md` lists the reserved
keywords (`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`,
`pass_todo`, `pass_do_nothing`, `pass_dn`) and does not include `examples`.
That list is updated by this bug.

## Workaround applied

In the SAML slice the field `SamlFunction.examples: [SamlExample]` was renamed
to **`example_cases`** (`src/lib/common/saml/ir.spl:73`, and its uses in
`parser.spl` / `analysis.spl`). No other change was needed.

## Unblock condition

Either:

1. **Preferred** — make `examples` a *contextual* keyword everywhere: accept
   `TokenKind::Examples` (and the other Gherkin-only tokens) as a plain
   identifier in named-argument position, field position, and parameter name
   position. Then the SAML rename can be reverted.
2. Or, if it must stay reserved, make the parser say so: emit
   `` `examples` is a reserved keyword and cannot be used as an argument name ``
   instead of `expected Comma, found Colon`, and list it in
   `.claude/rules/language.md` (done) plus the syntax quick reference.

## Family census — RUN 2026-08-10, second defect found

The census was run over every identifier in the same lexer keyword block
(`src/compiler_rust/parser/src/lexer/identifiers.rs:280-300`). Each was probed
with the identical minimal program (`struct K: <kw>: text` constructed as
`K(<kw>: "ok")`) against the same seed binary.

| identifier | named-arg position |
|---|---|
| `admit`, `calc`, `calculator`, `to`, `not_to` | ok |
| `feature`, `scenario`, `outline`, `given`, `when`, `then` | ok |
| `handle_pool`, `grid`, `tensor` | ok |
| **`examples`** | **BROKEN** — `expected Comma, found Colon` |
| **`and_then`** | **BROKEN** — `expected Comma, found Colon` |

So the family is exactly two identifiers, not the whole Gherkin block: most
Gherkin tokens (`scenario`, `given`, `when`, `then`, `feature`, `outline`)
round-trip fine in named-argument position. Any fix must cover `and_then` as
well as `examples`, and a regression test should assert the whole table above
rather than the single reported case.

## Not verified here

- Behavior under the pure-Simple self-hosted compiler (`src/compiler`) — the
  measurement above is the Rust seed only. The seed is the binary users
  currently run, so the defect is user-visible regardless.
- Whether `examples` also fails as a *parameter* name or as a `class` field
  constructor argument (only `struct` was probed).
