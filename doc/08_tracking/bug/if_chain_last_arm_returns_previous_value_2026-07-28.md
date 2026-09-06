# A statement-leading `-`/`+` at the same indent is silently glued to the previous line

**Filed:** 2026-07-28 · **Lane:** IFCHAIN · **Severity:** critical (silent wrong arithmetic)
**Status:** OPEN (parser fix deferred) — **interim guard LANDED**: lint `LEADOP001`
(`src/compiler/35.semantics/lint/leading_operator.spl`, Warn) flags the same-indent
shape. 276 existing sites inventoried in `build/leadop_sites.txt`; escalate the rule
to Deny once they are converted. Lane state: `.spipe/leading_operator_lint/state.md`.
**Component:** Rust seed parser (`src/compiler_rust/parser`) — **not** the pure-Simple parser
**Reported as:** "the last arm of a long single-line `if`-chain returns the PREVIOUS arm's value"

## Summary

The reported framing is **wrong, and the wrong diagnosis is dangerous** because it
points at `if`-chains, which are innocent. The real rule is much broader:

> Under the Rust seed, a line that **begins with `-` or `+`** and sits at the
> **same indentation** as the previous statement is parsed as a **binary**
> operator continuing that statement's trailing expression.

So `return 15` followed by a bare `-1` sentinel line parses as `return (15 - 1)`
→ **14**, and the function is left with no tail expression at all, so the
fall-through path returns **nil** instead of `-1`.

There is no `if` involved. `15` ⏎ `-1` in a bare function body yields `14`.
Chain length is irrelevant — a one-arm `if` reproduces it identically.

## Minimal repro

```simple
fn f() -> i64:
    15
    -1

fn main():
    print(f().to_text())   # prints 14, must print -1
```

The originally-reported form:

```simple
fn hex_digit(c: text) -> i64:
    if c == "f" or c == "F": return 15
    -1
```
`hex_digit("f")` → **14**. `hex_digit("z")` → **nil** (crashes on `.to_text()`).

Repro tree: `build/ifchain_repro/` (`case_*.spl`, one case per file; `matrix.txt`).

## Truth table

Produced with `bin/release/x86_64-unknown-linux-gnu/simple` (the Rust bootstrap
seed — it prints the "bootstrap seed only" banner). **JIT and interpreter agree
on every row**, which is itself the tell: the corruption happens in the shared
*parser*, upstream of both engines.

| # | Shape (previous line ⏎ next line) | JIT | Interp | Want | Verdict |
|---|---|---|---|---|---|
| J | `15` ⏎ `-1` | 14 | 14 | -1 | **BUG** — pure form, no `if` |
| A | `val x = 15` ⏎ `-1` | core dump | nil | -1 | **BUG** |
| B | `if c=="f": return 15` ⏎ `-1`, hit | 14 | 14 | 15 | **BUG** |
| B′ | same, miss | core dump | nil | -1 | **BUG** |
| E | `if c=="f": return 15` ⏎ `+1`, hit | 16 | 16 | 15 | **BUG** — `+` too |
| H | 16-arm chain ⏎ `-1`, hit `"f"` | 14 | 14 | 15 | **BUG** — same as 1 arm |
| I | `if c=="f": r = 15` ⏎ `-1` ⏎ `return r` | 14 | 14 | 15 | **BUG** — assignment too |
| K | `if` / `elif` ⏎ `-1`, hit | 14 | 14 | 15 | **BUG** |
| N | `if c=="f": return 15` ⏎ *blank* ⏎ `-1` | 14 | 14 | 15 | **BUG** — blank line does not stop it |
| C | `if c=="f": return 15` ⏎ `return -1` | 15 / -1 | 15 / -1 | — | OK |
| D | block-form `if` ⏎ `-1` | 15 / -1 | 15 / -1 | — | OK — **dedent** breaks it |
| M | `while` block ⏎ `-1` | -1 | -1 | — | OK — dedent |
| F | `if c=="f": return 15` ⏎ `99` | 15 / 99 | 15 / 99 | — | OK — no leading sign |
| G | `if c=="f": return 15` ⏎ `(-1)` | 15 / -1 | 15 / -1 | — | OK — parens |
| L | `if c=="f": return 15` ⏎ `val z = -1` | 15 | 15 | — | OK — line does not *start* with the sign |
| P | `val s = 10` ⏎ ␣␣␣␣`+ 5` | 15 | 15 | 15 | OK — **intended** feature |
| Q | `val s = 10` ⏎ ␣␣␣␣`- 5` | 5 | 5 | 5 | OK — **intended** feature |

### Trigger boundary

Gluing happens **iff** all of:
1. the next line's first token is `+` or `-` (or another affected binary op — see below), **and**
2. no `DEDENT` is emitted between the two lines, i.e. the next line is at the
   **same or greater** indentation, **and**
3. the previous statement ends in a value-producing expression.

Irrelevant: presence of `if`, chain length, `elif` vs separate `if`s, `return`
vs assignment vs bare expression, text vs int comparison, intervening blank lines.

Not affected (parser-verified, see below): `==`, `!=`, `is`, `in`, `**`, `@`.
Affected operator set: `+ - * / % << >> & | ^` and `and`/`or`/`&&`/`||`/`|>`/`~>`/`//`.

## Mechanism (file:line)

`src/compiler_rust/parser/src/expressions/binary.rs:68-90` — the `parse_binary_multi!`
macro, "Case 2: operator on next line (leading continuation)":

```rust
if matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent) {
    let found_op = { match self.peek_through_newlines_and_indents() { ... } };
    if let Some(op) = found_op {
        self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
        self.advance(); // consume the operator
```

The same "Case 2" is duplicated in `parse_binary_single!` at `binary.rs:21-25`
and hand-written in `parse_bitwise_or` at `binary.rs:142-146`.
`+`/`-` are wired in at `binary.rs:361-364`:

```rust
parse_binary_multi!(parse_term, parse_factor, Plus => BinOp::Add, Minus => BinOp::Sub,);
```

The lookahead is `src/compiler_rust/parser/src/parser_helpers.rs:408-438`:

```rust
TokenKind::Newline | TokenKind::Indent => { lookahead_pos += 1; }
TokenKind::Dedent  | TokenKind::Eof    => { return None; }
```

**It never consults indentation.** It walks over any number of `Newline`/`Indent`
tokens and only stops at `Dedent`/`Eof`. A same-indent next line emits a bare
`Newline` (no `Indent`, no `Dedent`), so the lookahead sails straight through and
finds the `-`. That exactly explains every row of the truth table: the block-form
`if` and the `while` produce a `Dedent` (rows D/M → OK); `(-1)` is consumed as a
primary before the operator check (row G → OK); `99` is not an operator token so
`found_op` is `None` (row F → OK).

Note `binary.rs:338-359` already carves out `@` (`parse_matmul` is hand-written
with the comment "must NOT peek through newlines") — so the hazard of this
lookahead was already understood for one operator and never generalised.

### The pure-Simple parser does NOT have this bug

`src/compiler/10.frontend/core/parser_expr.spl:377-391` (`parse_addition`, and the
addition level of `parse_binary_from` at `:509-521`) only tests `par_kind_get()`
on the *current* token — no newline peeking. The only continuation mechanism on
the pure-Simple side is lexer-level and far narrower:
`src/compiler/10.frontend/core/lexer_struct.spl:994-1002` and `:891-894` allow a
**leading** `.` or `|` only, and `:990-992` / `:908-911` allow a **trailing**
operator via `token_requires_rhs` (`src/compiler/10.frontend/core/tokens.spl:525-544`).

**This is therefore a seed-vs-self-hosted semantic divergence**: the same `.spl`
source means different things depending on which compiler reads it. Every hazard
site below is currently mis-compiled by the seed and correctly compiled by the
pure-Simple compiler. That is a bootstrap-correctness problem in its own right.

## Fix sketch (not applied — see Coordination)

Add an indent-aware variant of the lookahead and use it for the arithmetic /
shift / bitwise levels:

```rust
// parser_helpers.rs — new fn alongside peek_through_newlines_and_indents
pub(crate) fn peek_leading_operator_continuation(&mut self) -> Option<TokenKind> {
    // identical walk, but track whether any TokenKind::Indent was crossed;
    // return None unless saw_indent == true.
}
```

then in `binary.rs` Case 2 (all three copies: `:21-25`, `:68-90`, `:142-146`)
call the new fn instead of `peek_through_newlines_and_indents`.

Rationale: rows P/Q show the *intended* multi-line-expression feature is always a
**deeper-indented** continuation, which emits an `Indent` token and is preserved.
Rows J/B/E/N are all same-indent, which emits no `Indent` and would now correctly
terminate the statement. The existing `binary_indent_count` / `Dedent` balancing
(`binary.rs` ↔ `expressions/core.rs:92-97`) is unchanged because the fix only ever
*declines* a continuation that would previously have been taken.

Leading-`.` method chaining is a different call path
(`skip_newlines_and_indents_for_method_chain` reached via the postfix parser) and
must keep the permissive behaviour — do not change it.

Gate: `test/01_unit/compiler/if_chain_arm_value_spec.spl`.

### Coordination — why it was not applied

`src/compiler_rust/parser/` has a live lane at the time of filing
(`src/compiler_rust/parser/src/lexer/strings.rs` and `src/fstring_bug_tests.rs`
both modified in the working copy). Landing a `binary.rs` change would require
rebuilding the seed on top of another lane's in-flight lexer work. Handing over
the sketch instead.

## Blast radius

Scan: every tracked `.spl` under `src/` and `test/` (vendored paths excluded),
looking for a line whose first token is `+`/`-` followed by a literal or simple
identifier, at the **same** indent as the preceding non-blank non-comment code
line, where that preceding line does not itself end in an operator. Docstring
bodies excluded.

**156 sites**, of which **142** are the `-` (sentinel) form. Raw output:
`build/ifchain_repro/hazard2.txt`, `build/ifchain_repro/hazard_minus.txt`.

A subset of the `+` hits are the intentional `+ RB()` JSON-builder chains in
`src/app/mcpgdb/**` and `src/app/serial_mcp/main.spl`; those are genuine
continuations and are *not* defects — but they are load-bearing on the very
behaviour being removed, so the fix must be checked against them (they are
same-indent, so the sketch above **will** change them and they need re-indenting
or parenthesising in the same change).

### Worst instances — hex-nibble decoders returning `e` for every `f`

Every one of these has the exact reported shape (`if c == "f"...: return 15`
immediately followed by a bare `-1`), so **every `f`/`F` nibble decodes as 14**:

| File:line | Context |
|---|---|
| `src/os/kernel/net/embedded_certs.spl:32` | kernel's built-in TLS trust anchors |
| `src/lib/nogc_sync_mut/io/tls_common_hooks.spl:103` | TLS hook fixture decoding |
| `src/lib/gc_async_mut/web/browser_session_loading.spl:72` | browser session state |
| `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/buffer/utilities.spl:276` | three copies of a shared buffer hex helper |
| `src/compiler/70.backend/linker/linker_script.spl:247` | linker script address parsing |
| `src/app/ui.ipc/protocol.spl:445` | UI IPC wire protocol |
| `src/lib/nogc_sync_mut/web_framework/{auth_middleware.spl:493,password_reset.spl:284,tracing.spl:82}` | auth / password-reset / trace-id decoding |
| `src/lib/common/js/builtins/{json.spl:326,number.spl:418,number.spl:432}` | JS `JSON.parse` escapes and `parseInt` radix |
| `src/lib/common/js/engine/{interpreter_types.spl:151,vm_object_store.spl:20}` | JS engine internals |
| `src/lib/nogc_sync_mut/database/vector/codec.spl:36` | vector-DB codec |
| `src/compiler/85.mdsoc/cross_query.spl:137`, `src/compiler/70.backend/backend/llvm_version.spl:141`, `src/app/llm_caret/json_helpers.spl:191` | compiler/tooling helpers |
| `test/03_system/os/os_tls_cert_chain_spec.spl:22` + siblings | the fixtures lane TLSVER originally reported |

`number.spl:432` is the nastiest of the set: the previous line is
`if lower == "f" and radix > 15: return 15`, so the glue lands on a
radix-dependent path.

### Second cluster — pure-Simple interpreter error paths (13 + 8 + 7 + 5 + 4 + 3 + 3 sites)

`src/compiler/10.frontend/core/interpreter/ops.spl` (13),
`.../_EvalOps/access_literal_assign_eval.spl` (8), `.../eval_access.spl` (7),
`.../eval_stmts.spl` (5), `.../_EvalOps/call_method_eval.spl` (4),
`.../eval.spl` (3), `.../eval_methods.spl` (3) — all of the form
`eval_set_error("...")` ⏎ `-1`, i.e. the error-sentinel return of the
self-hosted interpreter becomes `eval_set_error(...) - 1`. Under the seed these
error paths do not return `-1`.

### Third cluster — OS/kernel

`src/os/kernel/net/tls_shim.spl` (11), `src/os/kernel/loader/segment_mapper.spl` (10),
`src/os/services/netstack/netstack_init.spl` (3),
`src/os/kernel/scheduler/process_isolation.spl` (2), and
`src/os/kernel/arch/{x86_64,x86_32,riscv64,riscv32,arm64,arm32}/cstart.spl` (2 each).

## Recommended interim guard

Until `binary.rs` is fixed, a lint rule ("statement-leading `+`/`-` at the same
indent as the previous statement") would catch all 156 sites cheaply and is
independent of the seed rebuild. The safe rewrite at every site is either
`return -1` (row C) or `(-1)` (row G).

## Also worth noting

Row A / B′ show the seed's **JIT dumps core** when the function falls through
with no tail expression, while the interpreter reports
`method 'to_text' not found on type 'nil'`. The nil-return is the shared bug; the
core dump is a separate JIT robustness defect on nil-returning `i64` functions.
