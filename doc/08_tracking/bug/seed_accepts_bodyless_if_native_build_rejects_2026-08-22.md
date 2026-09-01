# Seed accepts a bodyless `if` block that native-build rejects (front-end divergence)

- **Filed:** 2026-08-22
- **Status:** OPEN — evidence complete, fix proposed but NOT landed (seed change, see "Why not fixed here")
- **Class:** seed-lenient / stage1-strict front-end divergence. Same family as
  `hir_unresolved_name_import_reachability_2026-08-22.md` and the
  function-body-local `use` case: source that the seed's Rust parser accepts is
  rejected by the pure-Simple front end, so a green interpreter run is **not**
  evidence that the tree builds.

## Symptom

A block header (`if`/`elif`/`else`/`while`/`for`) whose body is missing, and
whose next non-blank line DEDENTS to a lower column, is silently accepted by the
seed as an **empty block** (a no-op) and hard-rejected by native-build:

```
[parser_error] line 9:1: unexpected token in expression: Dedent ''
error: parse error in .../shapeA.spl (see [parser_error] output above)
```

## How it was found

Not by review. While instrumenting HIR lowering for the MirType lane
(`hir_unresolved_type_owner_missing_import_2026-08-22.md`), a script that
stripped probe `eprint`s left their `if` guards behind with no body:

```
             self.symbols.bind_qualified_type(
                 imported_mod.module_name, dependency, terminal_symbol)
+        if hir_module_env_get("SIMPLE_HIR_UNRESOLVED_TYPE_TRACE") == "1":

     me cached_surface_package_name(module_name: text) -> text:
```

The in-process reproducer spec ran **green on that exact tree** and fired 1153
probe lines, so the tree looked validated. The full `native-build` then died 21
minutes later with `parse error in .../module_reexport_materialization.spl` and
produced ZERO probe output. The interpreter run was worthless as a parse gate
and actively misleading — that is the cost this record exists to prevent.

## Reproduce (minimal, both paths)

`shapeA.spl` — bodyless `if` as the last statement of a method:

```
class Probe:
    n: i64

impl Probe:
    me first():
        self.n = 1
        if self.n > 0:

    me second() -> i64:
        self.n

fn main() -> i64:
    var p = Probe(n: 0)
    p.first()
    print p.second()
    0
```

| shape | `bin/simple run` (seed Rust parser) | `bin/simple native-build` (pure-Simple front end) |
|---|---|---|
| **A** — bodyless `if`, next line DEDENTS (end of method) | **ACCEPTS**, body is a no-op, prints `1` | **parse error**, `line 9:1: unexpected token in expression: Dedent ''` |
| **B** — bodyless `if`, next line is a same-column `if` | ACCEPTS, prints `7` | ACCEPTS, prints `7` (agree — see below) |
| **bodyless** — bodyless `if`, next line is a same-column integer expression | rejects: `Unexpected token: expected Indent, found Integer(7)` | not yet measured (run still in flight at filing time; the seed side is what matters here — it shows the seed is INCONSISTENT with itself) |
| **control** — same file with a real body | accepts, prints `2` | accepts |

Shape B agrees between the two paths and is **not** the divergence: the seed's
deliberate *flat-body* feature (body at the SAME column as the header) parses the
following `if not flag:` AS the body. Verified semantically, not just by exit
code — the native binary and the interpreter both print `7`.

## Mechanism (seed side)

`src/compiler_rust/parser/src/parser_impl/core.rs`, `parse_block_after_newline`
(reached for `if`/`elif`/`else`/`while`/`for` via `parse_condition_block`):

1. If the next token is not `Indent`, skip blank lines.
2. If it `is_statement_start()` → parse exactly ONE statement as a *flat body*.
   `is_statement_start` includes `If`, which is why shape B is swallowed.
3. **Otherwise, if it is `Dedent` or `Eof` → return an EMPTY `Block` with no
   error.** The in-code comment says this exists for `case nil:` match arms —
   but the path is shared, so it also legalises an empty `if`/`while`/`for` body.
4. Only if none of the above → `expect(&TokenKind::Indent)` → the error that
   shape `bodyless` gets.

So the leniency is step 3 leaking from match arms into conditionals.

## Which parser is right

**Both should reject a bodyless `if`.** An empty conditional body is never
intentional; Simple has `pass` for a deliberate no-op. The pure-Simple front end
is correct here and the seed is wrong. (Its diagnostic is still poor —
`unexpected token in expression: Dedent ''` names neither the construct nor the
missing body; a follow-up should say "block body expected after `if ...:`".)

## Blast radius of making the seed strict: ZERO in owned code

Scanned **15,190** owned `.spl` files under `src/` (vendored excluded per
CLAUDE.md Owned-Code Scope), skipping docstring bodies:

```
EMPTY-BODY sites in owned .spl (docstrings excluded): 0
```

The only apparent hit before docstrings were excluded was
`src/os/crypto/nacl.spl:175`, `if plain.len() == 0: # auth failed` — which is
**inside a `"""` docstring** (an `Example:` block), not code. So no owned source
depends on the lenient behaviour, and tightening the seed breaks nothing here.

## Proposed fix (not landed)

Thread a `allow_empty_body: bool` through `parse_block_after_newline` (or split
the empty-block arm into a `parse_arm_block` used only by match arms):
`parse_condition_block` passes `false`, match-arm parsing passes `true`. With
`false`, the `Dedent`/`Eof` arm errors with a message naming the header.

## Why not fixed here

It is a **Rust seed** change (`src/compiler_rust`), which needs a seed rebuild to
verify, and the shared empty-block arm is load-bearing for `case nil:` match arms
— so it needs its own regression pass over match-arm parsing, not a drive-by edit
inside an unrelated HIR-lowering lane. Landing an unverified seed parser change
mid-session is exactly the kind of clobber `.claude/rules/vcs.md` warns about.
Evidence, fixtures and the patch shape are recorded here so the fix is a small,
self-contained follow-up.

## Fixtures

`.../scratchpad/mt/bodyless/{shapeA,shapeB,bodyless,control}.spl` — promote to
`test/01_unit/language/` when the fix lands, as a parity spec that asserts BOTH
paths reject shape A.
