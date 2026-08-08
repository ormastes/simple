# Self-hosted parser reads `true_*` / `false_*` call arguments as bool literals

**Date:** 2026-08-01
**Status:** FIXED (pending bootstrap verification)
**Severity:** CRITICAL — blocked Stage 3 self-host; silently miscompiles otherwise-valid code
**Fix:** `src/compiler/10.frontend/core/parser_expr.spl` — `parse_call_arg_raw`
**Regression spec:** `test/01_unit/compiler/parser_true_false_prefixed_call_arg_spec.spl`

## Symptom

Stage 3 (`stage2` recompiling the tree) failed with 21 parser errors, 16 of them
on one file:

```
[parser_error] src/compiler/70.backend/backend/vulkan_backend.spl line 1109:55: expected ), got . '.'
[parser_error] src/compiler/70.backend/backend/vulkan_backend.spl line 1109:99: expected ), got . '.'
```

Line 1109 is:

```simple
if not block_positions.has(true_target.id) or not block_positions.has(false_target.id):
```

Columns 55 and 99 are exactly the two `.` characters. `true_target` and
`false_target` are match-arm bindings from `case If(cond, true_target, false_target):`.

## Root cause

`parse_call_arg_raw` (`parser_expr.spl`) carried a "bool-suffixed identifier"
production. For any call argument whose identifier began with `true_` or
`false_`, it consumed the identifier and returned
`expr_suffixed_bool(<1|0>, <text after the prefix>, 0)` — the remainder of the
name being taken as a **type suffix**, by analogy with `1_i64` / `1.0_f32`.

It returned immediately, so the postfix parser never ran, and `true_target.id`
left the `.` unconsumed → `expected ), got .`.

## The louder bug was not the worse one

The parse error only fires when the identifier is *followed* by postfix syntax.
When the argument ends normally the code parses and is silently rewritten:

```simple
val true_value: i64 = 42
print(ident(true_value).to_text())
```

Under the stage2 (pre-fix) compiler this is not a parse error — it becomes the
literal `true` carrying the type suffix `value`:

```
error: in-process native-build: HIR lowering error: unresolved type: value
```

That is very likely a contributor to the **3,350 `unresolved type`** errors seen
in the earlier whole-tree stage-3 attempt, which were previously attributed
wholly to match-arm scope handling. Where a suffix happens to name a real type
(`true_bool`, `false_i64`), there would be no diagnostic at all — just a wrong
value.

## Why this is a divergence, not a feature

- `expr_suffixed_bool` had exactly **one** construction site in the entire
  compiler: this one. (`_ParserPrimary/asm_match_suffix.spl` and
  `asm_raw_parsing.spl` import it but never call it.)
- The Rust seed has **no** such production — `grep -rl 'suffixed_bool\|SuffixedBool'`
  matches zero `.rs` files. The seed compiles `vulkan_backend.spl` clean.
- The syntax is undocumented: no match in `doc/` or in
  `doc/07_guide/quick_reference/syntax_quick_reference.md`.
- It is not merely unused, it is *actively harmful*: ordinary `true_*`/`false_*`
  locals, parameters and match-arm bindings are common in this tree.

So the production was removed rather than narrowed. Narrowing it (e.g. only
firing when the next token ends the argument) would have fixed the parse error
while leaving the silent-rewrite path intact.

## Blast radius

**Loud mode:** the failing stage-3 log names exactly **one** file —
`vulkan_backend.spl`, 21 errors, all of them there. Note `native-build` aborts
phase 2 on the first file that fails to parse, so this is the *first* blocker,
not provably the only one; later files were never reached.

**Silent mode (upper bound):** `rg '[(,]\s*(true|false)_[A-Za-z0-9_]+\s*[,)]'`
over `src/` and `test/` matches **68 sites in 25 files**. This is an upper
bound, not a count of corrupted call sites — the same shape appears in `case`
patterns (e.g. `case If(cond, true_target, false_target):`), which go through the
pattern parser, not `parse_call_arg_raw`. It has not been narrowed further
because the fix makes every one of them correct regardless of which parser
consumed it.

## Reproduction (no bootstrap needed)

The stage2 binary from a previous run reproduces it directly in ~2 seconds:

```sh
S=build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
cat > /tmp/v.spl <<'EOF'
struct Node:
    id: i64

fn probe(d: Dict<i64,i64>, true_x: Node) -> bool:
    return d.has(true_x.id)

fn main():
    print("ok")
EOF
SIMPLE_BOOTSTRAP=1 $S native-build --target x86_64-unknown-linux-gnu \
    --backend llvm -o /tmp/v.out /tmp/v.spl
```

Discriminator table (all other shapes parse clean):

| identifier | in `f(x.id)` | note |
|---|---|---|
| `a_target`, `tru_target`, `truex`, `truexyz` | ok | prefix must be exactly `true`/`false` + `_` |
| `match_x`, `val_x`, `nil_x`, `if_x`, `me_x` | ok | no other keyword is affected |
| `TRUE_x`, `True_x` | ok | case-sensitive |
| `true_x`, `false_x`, `true_target` | **fail** | |

`return true_x.id` outside a call argument is fine — the rule lived only in
`parse_call_arg_raw`.

## Sibling sweep (the family, enumerated)

`rg 'par_text_get\(\) ==' src/compiler/10.frontend/` lists every place the parser
interprets identifier *text* as syntax. All the others are **exact** matches —
`todo`, `mut`, `with`, `mod`, `from`, `iso`, `print`, `assert`, `volatile`,
`bits`, `pri`, `pc`, `priority`, `cli`, `comptime`, `candidates`, `generic`,
`limits`. This was the only **prefix** match, which is why it was the only one
that captured unrelated names.

Each was differentially tested as an ordinary local passed to a function
(stage2 vs the Rust seed oracle). **No divergence in the blocking direction** —
nothing else makes the self-hosted compiler reject what the seed accepts.

Two diverge the *other* way, and are recorded here rather than filed separately
because neither can block a bootstrap: `with` and `generic` are **hard keywords
in the seed** (`Unexpected token: expected pattern, found With`) but ordinary
identifiers in the pure-Simple parser. The tree compiles under the seed today,
so nothing uses them as identifiers; the risk is only that new pure-Simple code
could adopt a name the seed will later reject.

## Correction to the earlier diagnosis

This defect was tracked as a *whole-tree parse-state* problem ("parses clean
alone, fails only in whole-tree build"). That framing was wrong: it reproduces
in a 9-line standalone file. The earlier standalone probes must have used a
different identifier spelling.
