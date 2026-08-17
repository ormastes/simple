# `check-no-jit-module-drop.shs` DROP: `primitive_api.spl` struct 'String' field 'ty'

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
workaround; guard correctly stays red. Live re-compile verification blocked by
an unrelated environment breakage (see "Environment blocker" below).

## The guard hit

```
scripts/check/check-no-jit-module-drop.shs --candidates
...
DROP  src/compiler/35.semantics/lint/primitive_api.spl  struct 'String' field 'ty'
```

Reproduction command (per the guard's `compile_one()`):

```
timeout 120 bin/simple compile src/compiler/35.semantics/lint/primitive_api.spl -o <tmp>/out.smf
```

Expected diagnostic (per the guard's `DROP_RE`):

```
cannot infer field type while lowering <fn>: struct 'String' field 'ty'
```

## Root cause (static analysis, code reading only)

`src/compiler/35.semantics/lint/primitive_api.spl` imports two DIFFERENT AST
type families and conflates them:

```spl
use compiler.frontend.ast.{Node, FunctionDef, StructDef, ClassDef}
use compiler.frontend.parser_types_expr.{Type}
use compiler.frontend.parser_types.{Param, ParserField}
```

`check_function`/`check_struct`/`check_class`/`is_pure_math_function` operate
on `func: FunctionDef`, `struct_def: StructDef`, `class_def: ClassDef` — which
come from `compiler.frontend.ast` (`src/compiler/10.frontend/ast.spl`). But
that module is explicitly a **flat, placeholder AST** (see its own comment at
line 61: "Flat AST module ({name, items}) — distinct from the rich
`parser_types.Module`"). Every field on it is `text`:

```spl
struct FunctionDef:
    name: text
    generic_params: [text]
    params: [text]              # <-- NOT [Param]
    has_return_type: bool
    return_type: text           # <-- NOT Option<Type>
    ...

struct StructDef:
    name: text
    generic_params: [text]
    fields: [text]               # <-- NOT [ParserField]
    ...
```

`primitive_api.spl`'s code, however, was written as if `func.params` were
`[Param]` and `struct_def.fields`/`class_def.fields` were `[ParserField]` —
the RICH types from `compiler.frontend.parser_types` (which it also imports,
but never actually uses as the loop-element type):

```spl
for param in func.params:              # param : text, not Param
    val ty = match param.ty:            # <-- .ty accessed on a `text` value
        ...
```//lines 65, 88; same pattern at 120/139 for `field.ty`

Neither `Param` (`src/compiler/10.frontend/parser_types.spl:161`) nor
`ParserField` (same file, line 261) has a field literally named `ty` either —
they have `type_: Type` (desugared with a `has_type_: bool` companion). So
even in the world where `param`/`field` really were `Param`/`ParserField`
objects, `.ty` would still be the wrong name (`.type_` is correct there).

Because `FunctionDef.params` is declared `[text]`, the HIR lowerer correctly
infers each loop-bound `param` as `text`/`String`, then hits `param.ty` — a
field access for a field that does not exist on `String` — and cannot infer a
type for it. Hence the compiler's own diagnostic: `struct 'String' field
'ty'`. The guard's oracle is doing exactly what it's designed to do; the
detection is correct.

## Why this is NOT a narrow call-site fix

1. **The bug is not one field name.** It's not just `.ty` vs `.type_`; the
   element TYPE itself is wrong (`text` vs the real `Param`/`ParserField`
   struct type is 100% unavailable at this call site — `ast.FunctionDef` never
   carries it). Renaming `.ty` to `.type_` would just move the same
   "cannot infer field type" error to `.type_` on a `text` receiver.
2. **`func.return_type`** (used via `if not func.return_type.?`) has the same
   problem: `ast.FunctionDef.return_type` is `text`, not
   `Option<Type>`/`Type`, so `.?`/`Some(value)`/`nil` matching against it is
   equally nonsensical against the real declared shape.
3. **No safe working analog exists elsewhere in the repo to mirror.** The only
   other implementation of a primitive_api lint —
   `src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl`
   (`check_primitive_api`) — deliberately does NOT use any AST/struct types at
   all; it is a pure text/regex scan over source lines (see its own header
   comment: "Text-based detection ... it does not try to prove full AST-level
   correctness"). It cannot be used as a drop-in shape to mirror without
   discarding all of `primitive_api.spl`'s AST-based logic and duplicating the
   already-existing text-scanner.
4. **A real fix requires plumbing**, either:
   - Rewiring `check_function`/`check_struct`/`check_class` onto whichever
     module actually produces `[Param]`/`[ParserField]`-typed function/struct
     definitions in the real semantic pipeline (i.e., feed them
     `parser_types.ParserFunction`/`ParserStruct`/`ParserClass` — or whatever
     downstream representation genuinely carries typed params/fields — instead
     of the flat `compiler.frontend.ast.Node`), which means first finding
     where such a richer, uniformly-available representation exists in the
     semantics/lint pipeline, or
   - Adding real typed fields to `compiler.frontend.ast.FunctionDef` /
     `StructDef` / `ClassDef`, which is explicitly documented as an
     intentionally flat/placeholder AST distinct from the rich one — changing
     that shape has broader blast radius across every other consumer of
     `compiler.frontend.ast` (checked: also imported by
     `10.frontend/__init__.spl`, `35.semantics/lint/semantic_api/checker.spl`,
     `35.semantics/lint/semantic_api/type_walk.spl`,
     `80.driver/smf_serialization.spl`, `80.driver/smf_writer_test.spl`,
     `99.loader/module_resolver/{resolution,manifest}.spl`,
     `40.mono/monomorphize/{deferred,deferred_subst,deferred_deserialize,partition,table}.spl`).

Both directions require understanding/touching pipeline-wide data flow, which
is exactly the "broad/deep, don't attempt" case this task was scoped to avoid.

## Is this actually reachable / live?

`src/compiler/35.semantics/lint/primitive_api.spl`'s `check_function` /
`check_struct` / `check_class` / `check_module_items` / `check_call_site` /
`is_pure_math_function` have **no callers anywhere in the tree**:

```
grep -rn "semantics\.lint\.primitive_api\|semantics/lint/primitive_api" src/compiler/
# (no output)
```

The only things that reference "primitive_api" as a live, wired-in lint are
`compiler.tools.fix.rules.impl_.lint_primitive_api.check_primitive_api` (the
text-scanner above), consumed from `90.tools/fix/main.spl`,
`90.tools/fix/rules/registry.spl`, `90.tools/lint/_LintMain/lint_checks.spl`,
and `90.tools/fix/rules/__init__.spl`. So this file at
`35.semantics/lint/primitive_api.spl` is dead/orphaned code today — it is
still a documented DROP source (the guard compiles it standalone, as it does
every tracked file), but nothing in the running compiler currently reaches
this HIR-lowering failure through normal execution.

## Environment blocker (this session)

Could not re-run the guard's oracle live to confirm the diagnostic text
in-session: every locally available `simple` binary in this shared,
concurrently-clobbered working copy crashes (SIGSEGV, `timeout: the monitored
command dumped core`) on `compile`, even for a trivial one-line
`fn main(): print "hi"` fixture — not specific to this file. Tried:

- `bin/release/simple` (wrapper) — its own bounded ABI probe (`simple test
  --help`) fails: "deployed Simple runtime failed its bounded test ABI probe"
- `release/x86_64-unknown-linux-gnu/simple` directly — `--version` OK, but
  `compile` prints "compile bridge exited early before reporting diagnostics"
- `bootstrap/stage1/simple`, `bootstrap/stage2/simple`,
  `bootstrap/stage3/simple` — `--version` OK, but `compile <anything>`
  segfaults (`timeout: the monitored command dumped core`)
- `bin/simple` itself does not exist in this checkout (no symlink); `sh
  scripts/setup/setup.shs` reports `bin/release/x86_64-unknown-linux-gnu/simple
  not found — run bootstrap first`

This matches this session's briefed environment facts (shared WC under
aggressive concurrent clobbering; stale/corrupt deployed binaries are a known
recurring failure mode here). The root cause above was therefore established
by static code reading (struct declarations + import/caller graph), not by a
live compiler run. Re-verification should be done from a freshly rebuilt
`bin/release/x86_64-unknown-linux-gnu/simple` (`bin/simple build bootstrap`)
in an uncontested checkout.

## What would need to change in the compiler / this file

Not attempted (out of scope per task guidance — "if it looks deep/broad,
STOP"). Concretely, either:
1. Find or introduce a properly-typed function/struct/class item
   representation (real `[Param]` / `[ParserField]` with real `Type` fields)
   that's actually populated for whatever `Node`s `check_module_items` is
   meant to walk, and repoint `35.semantics/lint/primitive_api.spl` at it
   instead of `compiler.frontend.ast`; or
2. Confirm this file is genuinely obsolete/superseded by
   `90.tools/fix/rules/impl_/lint_primitive_api.spl` and remove it (a product
   decision, not something to do silently as a "guard fix").

No source files were changed for this task.

## Verification 2026-08-17 (w02/s4 lane) — ALREADY FIXED, closing on content

Classified by CONTENT of current source, not SHA ancestry (per session brief
CORRECTION 1 — the cited commits are not reachable from `origin/main`).

`grep -n '\.ty\b' src/compiler/35.semantics/lint/primitive_api.spl` returns
**exactly one line, and it is a comment** (line 21). There is no remaining
field access of `.ty` on a flat-text entry anywhere in the file.

The in-source NOTE at `src/compiler/35.semantics/lint/primitive_api.spl:18-27`
records the fix and its mechanism: `FunctionDef.params` and
`StructDef/ClassDef.fields` are `[text]` ("name: Type" entries, per the
`# DESUGARED` markers in `ast.spl`), not `[Param]`/`[ParserField]` objects. The
file previously field-accessed `.ty`/`.name` on them, which parses but cannot be
lowered ("cannot infer field type ... struct 'String' field 'ty'") — the exact
error in this bug's title. It now parses the flat-text shape with local
`_pf_name_of` / `_pf_type_of` helpers instead of enum-typed field access,
matching sibling `semantic_api/checker.spl`.

The tracking-row evidence "root-caused NOT fixed, needs redesign" is **stale**;
the redesign it asked for is the one that landed. `scripts/check/check-no-jit-module-drop.shs`
remains in tree as the standing gate.

**Verdict: ALREADY FIXED (stale doc). No patch applied.**
Not proven: this lane did not execute `check-no-jit-module-drop.shs` end-to-end
(host at 164 concurrent `simple` processes under a live bootstrap); the close
rests on source content, which is decisive for the named defect.
