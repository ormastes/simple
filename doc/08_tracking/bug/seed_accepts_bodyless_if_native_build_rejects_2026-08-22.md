# Bodyless `if` block: the two front ends disagree in BOTH directions, and one silently miscompiles

- **Filed:** 2026-08-22
- **Status:** OPEN — evidence complete, fix proposed but NOT landed (parser changes on both sides; see "Why not fixed here")
- **Class:** front-end divergence between the seed's Rust parser (`run`/`test`/interpreter)
  and the pure-Simple front end (`native-build`, `src/compiler/10.frontend`).
  Related but NOT the same shape as `hir_unresolved_name_import_reachability_2026-08-22.md`
  and the function-body-local `use` case: those are "seed lenient, stage1 strict".
  **This one is not a one-way leniency gap — neither parser is a superset of the
  other, and the pure-Simple side additionally MISCOMPILES one accepted shape.**

## Symptom

A block header (`if`/`elif`/`else`/`while`/`for`) with no body. What happens
depends on what FOLLOWS the header, and the two front ends disagree in opposite
directions on two of the three shapes.

## Measured truth table

All four fixtures were run end to end on both paths. Native rows are the
**program's output**, not just the exit code.

| # | shape | `bin/simple run` (seed Rust parser) | `bin/simple native-build` (pure-Simple front end) |
|---|---|---|---|
| A | bodyless `if`, next line **DEDENTS** (last stmt of a method) | **ACCEPTS** — empty block, no-op, prints `1` | **parse error**: `line 9:1: unexpected token in expression: Dedent ''` |
| B | bodyless `if`, next line is a **same-column `if`** | ACCEPTS, prints `7` | ACCEPTS, prints `7` — **agree** |
| C | bodyless `if`, next line is a **same-column integer expression** | **REJECTS**: `Unexpected token: expected Indent, found Integer(7)` | **ACCEPTS — and prints `2147483652`, where `7` is correct** |
| — | control (same file, real body) | prints `2` | prints `2` — agree, so the harness is non-vacuous |

Row **A** is seed-lenient / native-strict. Row **C** is the exact opposite —
native-lenient / seed-strict — **and the accepted program is wrong**:
`2147483652` (`0x80000004`) is garbage, not the `7` the function returns.
That is a silent miscompile of malformed source, which is worse than either
parser's rejection.

## Reproduce

`shapeA.spl` (row A):

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

`bodyless.spl` (row C):

```
fn probe(flag: bool) -> i64:
    if flag:

    7

fn main() -> i64:
    print probe(true)
    0
```

Row **B** is *not* a divergence and is explained by the seed's deliberate
**flat-body** feature (a body at the SAME column as the header): the following
`if not flag:` is parsed AS the body. Verified semantically, not by exit code —
both paths print `7`.

## Mechanism (seed side, row A)

`src/compiler_rust/parser/src/parser_impl/core.rs`, `parse_block_after_newline`
(reached for `if`/`elif`/`else`/`while`/`for` via `parse_condition_block`):

1. Next token is not `Indent` → skip blank lines.
2. `is_statement_start()` → parse exactly ONE statement as a *flat body*.
   `is_statement_start` includes `If`, which is why row B is swallowed.
3. **Otherwise `Dedent`/`Eof` → return an EMPTY `Block`, no error.** The in-code
   comment says this arm exists for `case nil:` match arms, but the function is
   shared with `parse_condition_block`, so match-arm leniency leaks into
   conditionals. This is row A.
4. Otherwise → `expect(&TokenKind::Indent)` → the error in row C.

So the seed is already inconsistent with itself: the same empty `if` body is
accepted before a DEDENT and rejected before an integer.

The pure-Simple side of row C (accept + miscompile) is **not yet root-caused** —
it needs its own dig through `src/compiler/10.frontend` block parsing. Stated
here rather than guessed.

## Which parser is right

**Neither, fully.** A bodyless `if` should be a parse error in BOTH — Simple has
`pass` for a deliberate no-op. The pure-Simple side is right on row A, the seed
is right on row C, and row C's native behaviour (accept + emit garbage) is the
single worst cell in the table and should be fixed first.

## Blast radius of making both strict: ZERO in owned code

Scanned **15,190** owned `.spl` files under `src/` (vendored excluded per
CLAUDE.md Owned-Code Scope), skipping docstring bodies:

```
EMPTY-BODY sites in owned .spl (docstrings excluded): 0
```

The only apparent hit before docstrings were excluded was
`src/os/crypto/nacl.spl:175`, `if plain.len() == 0: # auth failed` — which is
**inside a `"""` docstring** (an `Example:` block), not code. So this is not a
latent auth bug, and no owned source depends on either lenient behaviour.

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
probe lines, so the tree looked validated. `native-build` then died 21 minutes
later with `parse error in .../module_reexport_materialization.spl` and zero
probe output. **A green interpreter run is not a parse gate for native-build.**

## Proposed fix (not landed)

- Seed (row A): thread `allow_empty_body: bool` through
  `parse_block_after_newline`, or split the empty-block arm into a
  `parse_arm_block` used only by match arms. `parse_condition_block` passes
  `false` and errors naming the header; match arms keep the empty arm.
- Pure-Simple (row C): root-cause the accept-and-miscompile first; the fix is
  to reject, matching the seed.

## Why not fixed here

The seed half is a Rust change (`src/compiler_rust`) needing a seed rebuild to
verify, and the shared empty-block arm is load-bearing for `case nil:` match
arms, so it needs its own match-arm regression pass. The native half is not root
caused yet. Neither belongs as a drive-by inside an unrelated HIR-lowering lane;
landing an unverified parser change mid-session is the clobber pattern
`.claude/rules/vcs.md` warns about.

## Fixtures

`.../scratchpad/mt/bodyless/{shapeA,shapeB,bodyless,control}.spl` — promote to
`test/01_unit/language/` when the fix lands, as a parity spec asserting that
BOTH paths reject rows A and C and agree on B and the control.
