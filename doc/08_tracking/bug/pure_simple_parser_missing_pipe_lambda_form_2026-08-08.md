# Pure-Simple parser does not implement the pipe-lambda form `|x| ...` at all — latent Stage-3 self-host blocker

- **Date:** 2026-08-08
- **Status:** OPEN — filed, not fixed (porting is a feature-sized change, see Scope). Parser gap EMPIRICALLY CONFIRMED via `bin/simple lint` discriminating pair.
- **Area:** compiler / pure-Simple frontend parser (`src/compiler/10.frontend/**`)
- **Severity:** blocker-class for self-host (obligation "USED"), latent behind
  earlier Stage-3 blockers
- **Rule context:** `rust is seed and pure simple must impl and verified and used`

## Summary

Commit `150a24e0fdb` ("fix(parser): support typed pipe-lambda params
`|x: i64| ...`") fixed the **Rust seed parser only**. The spec that shipped with
it, `test/01_unit/language/typed_pipe_lambda_param_spec.spl`, says so in its own
header ("STATUS AT WRITE TIME: fixed only in the seed parser source
(`src/compiler_rust/parser/**`)").

Nobody checked the pure-Simple side. On inspection the pure-Simple parser is not
merely missing the `: Type` annotation that the seed fix added — **it does not
implement the pipe-lambda form at all**, neither `|x: i64| x + 1` nor the
untyped `|x| x + 1`.

This is the reverse of the usual seed/pure-Simple gap: the seed is ahead by a
whole grammar production, and the deliverable implementation cannot parse a form
that the language spec defines and that the pure-Simple compiler's own source
already uses.

## Evidence

**1. No PIPE-token entry point in the pure-Simple primary-expression dispatcher.**

`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` never tests for
token kind `121` (`TOK_PIPE`):

```
$ /usr/bin/grep -n '121' src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl
(no output)
```

The only lambda forms that dispatcher accepts are:
- `\params: body` (backslash lambda) — `primary_expr.spl:671`
- `fn(...)` (inline fn lambda) — `primary_expr.spl:877` → `parse_fn_lambda_after_kw`
- `&:method` (method reference) — `primary_expr.spl:650`

**2. Every `|` site in the pure-Simple parser is a non-lambda use.**

- `10.frontend/core/lexer_struct.spl:1473-1481` — lexer emits `|>` (175), `||`
  (56), else plain `|` (121). No `|params|` handling.
- `10.frontend/core/parser_expr.spl:421-424`, `:508-511` — binary bitwise-or
  only (`expr_binary(121, ...)`).
- `10.frontend/core/parser.spl:953,958`; `parser_stmts.spl:1417,1477,1609` —
  match-arm pattern alternation (`case A | B:`).
- `_ParserPrimary/asm_match_suffix.spl:67`, `parser_asm.spl:33`,
  `_ParserDecls/enum_module_body.spl:376` — asm/enum syntax.

**3. The seed has the production; pure-Simple does not.**

```
$ /usr/bin/grep -rn 'parse_pipe_lambda_params' src/compiler_rust/parser/src/expressions/postfix.rs
975:    pub(crate) fn parse_pipe_lambda_params(&mut self) -> Result<Vec<LambdaParam>, ParseError> {
```

**4. The form is already load-bearing in pure-Simple source.**

```
$ /usr/bin/grep -rEn '\.(map|filter|fold|each|any|all|find|sort_by)\(\|[a-zA-Z_]' src/compiler --include=*.spl | wc -l
29
$ ... src/lib --include=*.spl | wc -l
3
```

Concrete sites in `src/compiler/35.semantics/error_formatter.spl`:

```
:442        val type_strs = elements.map(|e| self.format_type(e))
:465        val param_strs = params.map(|p| self.format_type(p))
:475        val arg_strs = args.map(|a| self.format_type(a))
```

**5. The language spec has the form the hand-written parser lacks.**

`src/compiler/90.tools/verify/verify_treesitter_grammar.spl:90` lists a
`pipe_lambda` grammar node.

**6. Even if the production were added, the flat-AST bridge would drop the types.**

`10.frontend/_FlatAstBridge/convert_nodes.spl:948-953` stores lambda params with
`has_type_: false, type_: Type(kind: TypeKind.Infer, ...)` hard-coded. Repo-wide,
`has_type_: true` never appears on a `LambdaParam`. `expr_lambda` carries only
`[i64]` ident indices, with no parallel type vector.

## Why this has not surfaced as a Stage-3 failure yet

Stage 3 (the stage2 pure-Simple compiler recompiling `bootstrap_main.spl`)
currently fails earlier, on module-resolution blockers — `unresolved type:
ByteOrder` in `cache_validator.spl`, then the `Effect` facade collision in
`src/compiler/50.mir/__init__.spl` (see
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
Those fire before compilation reaches `src/compiler/35.semantics/`, so the
parser gap is **latent**: it is not the current Stage-3 error, but it sits on the
path and will become the error once the resolution blockers clear.

This matters for planning: the sibling lane attacking the materialization walk
should expect a *parse* failure on `|e|` after the resolution failures are
resolved, not a clean Stage 3.

## Scope — why this is filed, not fixed here

Porting is not the small "add optional `: Type`" tweak that the seed fix was.
It requires:
1. A new pipe-lambda production in the pure-Simple primary-expression parser,
   disambiguated from binary bitwise-or (`a | b`) and from match-arm alternation
   (`case A | B:`) — the `|` token is already overloaded three ways.
2. Per-param type storage in the flat AST: `expr_lambda` currently carries only
   `[i64]` ident indices and has no slot for types.
3. Un-hard-coding `has_type_: false` in the flat-AST bridge, plus the downstream
   HIR/MIR consumers that have never seen a typed lambda param from this parser.

That is a feature-sized change to a fenced, self-host-critical file, and doing it
blind (with no way to run Stage 3 to completion) risks breaking the backslash- and
`fn`-lambda forms that Stage 2 currently depends on. The seed fix's own author
hit exactly this trap: an unguarded first revision broke `\x, y: x + y`.

## Verification status — EMPIRICALLY CONFIRMED on the pure-Simple frontend

`bin/simple lint` is the pure-Simple source linter: it loads and runs the
pure-Simple frontend (`src/compiler/10.frontend/**`), so its parse verdict is a
direct observation of the parser under audit — unlike `bin/simple run` /
`bin/simple test`, which parse with the Rust seed and therefore cannot exhibit
this gap.

**Discriminating pair.** Two probe files differing ONLY in the lambda form:

`build/parity_probe/pipelam.spl` — pipe lambda:
```
    val ys = xs.map(|e| e + 1)
```
`build/parity_probe/nopipelam.spl` — backslash lambda (control):
```
    val ys = xs.map(\e: e + 1)
```

Result:

```
$ bin/simple lint build/parity_probe/pipelam.spl
build/parity_probe/pipelam.spl:3:21: error[PARSE001]: NOT LINTED: source did not
  parse - every AST-based lint was skipped for this file
  (unexpected token in expression: | '|')
NOT LINTED: build/parity_probe/pipelam.spl - source did not parse, so no
  AST-based lint ran on it
LINT_PIPE_RC=1

$ bin/simple lint build/parity_probe/nopipelam.spl
LINT_BS_RC=0
```

The pure-Simple parser rejects `|e|` with `unexpected token in expression: |`
at the exact column of the opening `|` (3:21), while the backslash form on the
otherwise-identical file parses clean (rc 0). The control rules out "lint fails
on everything" — the failure is specific to the pipe-lambda production.

This confirms the untyped form `|x| ...` is unsupported, not merely the `: Type`
annotation the seed fix added. It is therefore a strictly larger gap than
`150a24e0fdb` closed on the seed side.

**Still inferred, not observed:** the downstream *consequence* — that Stage 3
will fail on `|e|` in `error_formatter.spl` — follows from this parse failure
plus the 29 in-tree call sites, but has not been reached in a Stage-3 run
because earlier module-resolution blockers fire first (see section above).

## Fix direction

Implement the pipe-lambda production in the pure-Simple parser, mirroring
`parse_pipe_lambda_params` / `parse_remaining_lambda_params` in
`src/compiler_rust/parser/src/expressions/{postfix,helpers}.rs`, including the
seed's disambiguation lesson: use the single-type parse, not the union-type
parse, or the lambda's own closing `|` gets swallowed by union-type continuation.
Then widen the flat AST to carry per-param types and drop the hard-coded
`has_type_: false`.

Regression coverage already exists and is currently RED for the pure-Simple
lane: `test/01_unit/language/typed_pipe_lambda_param_spec.spl` (3 examples).
Its third example (`|x| x + 1`, untyped) is the discriminator that shows the gap
is the whole form and not just the annotation.

## Related

- `150a24e0fdb` — the seed-only fix that prompted this audit.
- `doc/08_tracking/bug/pipe_lambda_typed_param_parser_gap_2026-08-07.md` — the
  seed-side bug doc; it scopes itself to the seed and does not mention the
  pure-Simple parser.
- `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
  — the Stage-3 blockers that currently mask this one.
