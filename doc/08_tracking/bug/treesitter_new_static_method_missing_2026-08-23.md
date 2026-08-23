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

## Follow-up

Arity-aware sweep for other `Struct.new(...)` call sites whose argument count
does not match the synthesized all-fields constructor. A naive name-only scan
produces hundreds of false positives (most structs DO get a usable synthesized
`new`), so the sweep must compare arity, not existence.
