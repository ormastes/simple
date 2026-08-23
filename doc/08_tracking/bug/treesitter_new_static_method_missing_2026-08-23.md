# `TreeSitter.new(...)` — unknown static method, aborts every `--source src/compiler` closure

- Date: 2026-08-23
- Status: FIXED (this change)
- Severity: blocker for the `--source src/compiler` semantic oracle
- Introduced by: `b9f1be59f8c` (2026-08-22, "feat(simpleos): seal visibility and streaming owners")

## Symptom

```
error: semantic: unknown static method new on class TreeSitter
```

`native-build --entry-closure` over any entry reaching `src/compiler/10.frontend`
died in semantic analysis before lowering, so a run reports **zero**
`[hir-fatal]` lines. That is "never got there", not "clean" — a false-clearance
trap. Stage 1 itself (`--source src/app --entry src/app/cli/bootstrap_main.spl`)
is NOT affected; the blast radius is measurement harnesses that use
`--source src/compiler`.

## Root cause (mechanism (b): caller landed against an API that does not exist)

`src/compiler/10.frontend/frontend.spl:134` called

```
var authority_tree = TreeSitter.new(authority_source)
```

`TreeSitter` is `struct TreeSitter:`
(`src/compiler/10.frontend/treesitter/outline_lexer.spl:19`) with **15** fields
and no hand-written static `new`. The synthesized struct constructor therefore
takes all 15 fields; a 1-argument `TreeSitter.new(source)` matches no candidate,
`constructor_overload_score` returns `None` for every candidate, and the seed's
dispatcher (`src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:376`)
emits `unknown static method new on class TreeSitter`.

The real 1-argument constructor is the free function
`treesitter_new(source: text) -> TreeSitter` (`outline_lexer.spl:45`), which
fills all 15 fields itself. `frontend.spl` never imported it.

## Hypotheses ruled out BY MEASUREMENT (not inspection)

1. **Re-export / provenance gap** (`use` where `export use` is needed at
   `outline.spl:23`). Disproven: changing that line to `export use` left the
   error unchanged, and importing `TreeSitter` **directly from its declaring
   module** `compiler.frontend.treesitter.outline_lexer` in the repro entry
   *still* failed identically. Provenance was never the issue.
2. **Half-landed optional-field desugar** at the three `TreeSitter(...)` literal
   sites in `outline_lexer.spl` (which omit the `has_*` companion flags).
   Disproven: supplying all 15 fields explicitly at all three sites left the
   error unchanged. Those sites are latent debt, not this defect.
3. **Missing class.** Disproven: `struct TreeSitter:` exists, single declaration.

## Fix

`src/compiler/10.frontend/frontend.spl`: call `treesitter_new(authority_source)`
and import it from the declaring module. Two lines, semantics-preserving —
`treesitter_new` is exactly the constructor the call site intended.

## Reproduce

`test/01_unit/compiler/frontend/treesitter_constructor_call_shape_spec.spl`
(source-shape guard: the defect only manifests on the semantic/native-build
path, not under the permissive interpreter `run`). Measured RED pre-fix
(`2 examples, 1 failure`), GREEN post-fix (`2 examples, 0 failures`).

Full-path reproduce (~15 min, not 72):

```
simple native-build --entry <entry importing compiler.frontend.treesitter.*> \
  --entry-closure --output /tmp/x
```

Pre-fix: `unknown static method new on class TreeSitter`.
Post-fix: that error is gone.

## Next abort uncovered (same blocker class, still open)

```
error: semantic: method `is_at_end` not found on type `TreeSitter`
```

`treesitter_is_at_end(self: TreeSitter)` is declared `fn` (not `me`) at
`outline_lexer.spl:178` and is called as `self.is_at_end()` from 20+ sites
across `outline.spl`, `outline_decls.spl`, `outline_members.spl` and
`outline_lexer.spl` itself. Sibling read-only helpers `treesitter_peek` /
`treesitter_check` share the exact same `fn ...(self: T)` shape; `is_at_end` is
simply the first one the semantic phase reaches in file order, so the whole
family is likely unresolved. This still blocks the `--source src/compiler`
oracle and needs its own record.

### RESOLVED 2026-08-23 — `d6fce96e530` (spec `7dd1fafaae8`)

The "whole family is likely unresolved" read above was correct, and the class is
wider than the treesitter package. Two facts were established BY MEASUREMENT,
and they point opposite ways to how the error message reads:

1. **UFCS is real.** A free `fn f(self: T)` IS callable as `x.f()`. It resolves
   ACROSS modules *without importing `f`* — the type carries the method. So the
   sibling files' bare `use ...outline_lexer.{TreeSitter}` was never the
   problem, and the fix needed no new `use` lines. (Fixture: a two-module
   `Box`/`box_get` pair, called as `b.box_get()` from a module importing only
   `{Box}` — prints `7`.)
2. **There is no type-prefix stripping.** `x.get()` against
   `box_get(self: Box)` fails with the identical
   `method `get` not found on type `Box`` for BOTH `me` and `fn`
   declarations. `me` vs `fn` is irrelevant to method-call resolution — the
   earlier framing that `fn` (not `me`) was the suspicious part is a red
   herring, killed here so nobody re-runs it.

So the declared name IS the method name, the language is right, and the call
sites were wrong: every site wrote the *stripped* name (`self.is_at_end()`)
against a declaration that carries the type prefix (`treesitter_is_at_end`).
Someone authored these files expecting a lowercased-type-prefix-stripping rule
that the language does not have.

**Fix:** call the declared names. Declarations were deliberately NOT renamed to
the stripped forms: they are module-scope free functions, and the type prefix is
exactly what keeps `parse_identifier`, `advance`, `error`, `check` etc. from
colliding across the treesitter package and with the real parser. Renaming decls
would trade a resolution defect for a namespace collision.

**Class sweep (tree-wide).** Of 18,828 `me` declarations in `src/`, only 86 take
an explicit `self:` first parameter — the normal style is `me name(args)` inside
a type body with implicit self. 39 files use the explicit-self shape. Exactly 7
of them called the stripped name, totalling **579 call sites**:

| file | sites | type prefix |
|---|---|---|
| `10.frontend/treesitter/outline.spl` | 185 | `treesitter_` |
| `10.frontend/treesitter/outline_members.spl` | 159 | `treesitter_` |
| `10.frontend/treesitter/outline_decls.spl` | 151 | `treesitter_` |
| `10.frontend/treesitter/outline_types.spl` | 48 | `treesitter_` |
| `10.frontend/treesitter/outline_lexer.spl` | 20 | `treesitter_` |
| `60.mir_opt/mir_opt/copy_prop.spl` | 15 | `copypropagation_` |
| `70.backend/linker/lazy_instantiator.spl` | 1 | `lazyinstantiator_` |

The rewrite is type-scoped — the prefix must be the lowercased name of that
file's *sole* `self:` type, and the target must actually be declared with
`self: T` — so it is 1:1 and line-count neutral (568 insertions, 568 deletions).
A first, looser heuristic (any global name ending `_<call>`) produced 114 hits
including a false positive at `35.semantics/safety_checker_transfer.spl`
(`self.error()` matching `treesitter_error`); that is why the applied rule is
type-scoped and not suffix-only. Four files with multiple `self:` types
(`15.blocks/blocks/registry.spl`, `35.semantics/macro_check/hygiene.spl`,
`40.mono/monomorphize/engine.spl`, `os/kernel/ipc/syscall_scheduler.spl`) were
skipped by that rule and inspected as non-offenders.

**Reproduce:** `test/01_unit/compiler/frontend/treesitter_self_method_resolution_spec.spl`
— RED pre-fix (4 examples, 3 failures), GREEN post-fix (4/4). The single example
that passes on both sides is the behavioural one, deliberately: it is the
positive evidence that UFCS works, not a reproducer, and says so in its own
docstring.

## Follow-up

Arity-aware sweep for other `Struct.new(...)` call sites whose argument count
does not match the synthesized all-fields constructor. A naive name-only scan
produces hundreds of false positives (most structs DO get a usable synthesized
`new`), so the sweep must compare arity, not existence.
