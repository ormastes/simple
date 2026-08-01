# Self-hosted stage3 "unresolved name": names that have NO import path at all, masked by the Rust seed's flat resolution

Status: FIXED for the 6 files below (this commit). Census/attribution recorded for the rest.
Date: 2026-08-01
Area: compiler / name resolution (HIR lowering), compiler source hygiene

## Summary

The residual stage3 `unresolved name` class is not one defect. It splits into two,
and only one of them is a resolver defect:

- **(A) glob re-export propagation** — the name IS reachable, through a glob
  (`use X.*`) whose target reaches it via its own named or glob imports. This half
  was closed by `GLB1` (unconditional named-item half) and by `3226faaf9eb`
  (memoized + ungated nested-glob recursion). Verified fixed here — see
  "Repro 1" below.
- **(B) no import path at all** — the name is declared in exactly one module,
  and *no* module on the importer's import graph names it or globs its declaring
  module. Under the self-hosted resolver this can never resolve. It compiles
  through the Rust seed only because the seed resolves flat over the whole loaded
  closure. No resolver change can fix (B); the source is genuinely missing an
  import.

This document records (B), its proof, and the fix.

## Class (B) instances fixed here

| file | name | count in census |
|---|---|---|
| `src/compiler/70.backend/backend/vulkan_backend.spl` | `compileerror_backend_error` | 89 |
| `src/compiler/10.frontend/treesitter/outline.spl` | `span_new` | 5 |
| `src/compiler/10.frontend/treesitter/outline_decls.spl` | `span_new` | 5 |
| `src/compiler/10.frontend/treesitter/outline_members.spl` | `span_new` | 3 |
| `src/compiler/10.frontend/desugar/desugar_async.spl` | `span_new` | 1 |
| `src/compiler/10.frontend/desugar/poll_generator.spl` | `span_new` | 1 |

Fix: add the missing named import. Each addition mirrors an existing in-tree
idiom, adds exactly one name, and points at the sole declaring module — so it
cannot swap an import winner (there was no winner: the name was unresolved).

## Proof that these have no import path

`compileerror_backend_error`
- Declared in exactly one module: `src/compiler/70.backend/backend/backend_types.spl:379`.
- `vulkan_backend.spl` has three globs — `compiler.mir.mir_data.*`,
  `compiler.backend.backend_api.*`, `compiler.backend.vulkan_type_mapper.*` —
  and **none of the three source files contains the string
  `compileerror_backend_error` at all**, so no glob hop of any depth can reach it.
  (`backend_api.spl` named-imports `compileerror_target_unsupported`, a different
  symbol.)
- `use compiler.backend.backend_types.*` elsewhere in the tree resolves to
  `src/compiler/70.backend/backend_types.spl`, a *different* module that does not
  declare this function.
- **In-tree control:** its sibling `cuda_backend.spl:9` carries
  `use compiler.backend.backend.backend_types.{compileerror_backend_error}`
  explicitly — and `cuda_backend.spl` has **zero**
  `unresolved name: compileerror_backend_error` in the same census that gives
  `vulkan_backend.spl` 89. Same directory, same globs, one has the import and
  passes, the other does not and fails.

`span_new`
- Declared in exactly one module: `src/compiler/10.frontend/block_types.spl:258`.
- `/usr/bin/grep -rn "use .*{[^}]*span_new" --include=*.spl src/compiler/` → **0 hits**:
  no module anywhere in the compiler names it in an import list.
- `/usr/bin/grep -rn "^use .*block_types\.\*" --include=*.spl src/compiler/` → **0 hits**:
  no module globs its declaring module either.
- The near-miss names that *are* imported (`flat_span_new`, `lex_span_new`) are
  different functions in different modules.

## Minimal repros (12 lines, both run against a stage2 built at the tip)

Build: seed → stage2 at the current tip
(`728 compiled, 0 cached, 0 failed`, 204.8 s). Invocation must be a **bare
positional `.spl`**; `native-build --entry X` delegates to the Rust seed codegen
and is therefore not a valid probe of the self-hosted resolver.

Repro 1 — second-hop glob (class A). **RESOLVES at the tip.**

```
# probe/defs.spl
enum MyEnumX:
    A
    B
fn my_free_fn() -> i64:
    7

# probe/mid.spl        (declares its own symbol AND globs defs)
use probe.defs.*
struct MidOwn:
    v: i64

# leaf.spl
use probe.mid.*
fn main() -> i64:
    val e = MyEnumX.A
    my_free_fn()
```

`SIMPLE_BOOTSTRAP=1 <stage2> native-build --mode dynload -o out leaf.spl`
emits `[bootstrap-real-llvm] function probe.defs.my_free_fn` — positive
evidence the name resolved and was lowered. Against a **pre-`3226faaf9eb`**
stage2 the same input emits
`HIR lowering error in leaf.spl: unresolved name: MyEnumX` and
`... unresolved name: my_free_fn`.

Repro 2 — no import path (class B). **STILL FAILS at the tip, correctly.**

```
# probe2/defs2.spl
fn my_free_fn2() -> i64:
    7

# probe2/user2.spl     (pulls defs2 into the compiled closure)
use probe2.defs2.{my_free_fn2}
fn user_calls() -> i64:
    my_free_fn2()

# flat.spl             (calls my_free_fn2 with NO import for it)
use probe2.user2.{user_calls}
fn main() -> i64:
    val a = user_calls()
    a + my_free_fn2()
```

→ `error: in-process native-build: HIR lowering error in flat.spl: unresolved name: my_free_fn2`

This is the correct behaviour and is exactly the shape of every class-(B) site
above: the declaring module is in the closure, but the importer never names it.
The Rust seed accepts the same source because it resolves flat over the loaded
closure.

## Census provenance (read this before quoting the numbers)

The per-name counts quoted around this lane — `BackendKind` 174,
`compileerror_backend_error` 89, `HirExprKind` 40, `int_to_str` 25,
`span_new` 15 — come from
`build/bootstrap/release_beta_verify/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(2026-08-01 03:44), which totals **545 `unresolved name` + 3345 `unresolved type`**.
They are the distribution of the **545** census, not of the later 161 one; the
two were conflated in lane hand-off. Enumerate classes before drilling:

```
/usr/bin/grep -oE 'unresolved (type|name)' "$LOG" | sort | uniq -c
```

Whole-class per-file attribution from that log (8 files carry 341 of 545):

```
 92 70.backend/backend/vulkan_backend.spl : BackendKind
 89 70.backend/backend/vulkan_backend.spl : compileerror_backend_error
 80 70.backend/backend/cuda_backend.spl   : BackendKind
 40 semantics/resolve.spl                 : HirExprKind
 22 frontend/core/_Ast/decl_nodes.spl     : int_to_str
  8 frontend/treesitter/heuristic.spl     : Span
 13 frontend/treesitter/outline*.spl      : span_new
  2 frontend/desugar/{desugar_async,poll_generator}.spl : span_new
```

Class-(A) members of that list and their glob hop, for the record:
`BackendKind` via `backend_api.spl`'s named import; `int_to_str` via
`ast_stmt.spl:10`'s named import; `Span` via `lexer.spl:21`'s named import;
`HirExprKind` via `hir.spl`'s `export use compiler.hir.hir_definitions.*`.

## Traps hit while measuring this

- A stage3 run under `SIMPLE_BOOTSTRAP=1` **without** `SIMPLE_BOOTSTRAP_STAGE4=1`
  runs a weaker pipeline; a "0 unresolved / 0 failed" result from it is not
  evidence that names resolve. See
  `doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`.
- `native-build --entry X` is Rust-seed codegen; only a bare positional `.spl`
  exercises the self-hosted front end.
- Default `grep` in this environment is ugrep. Pin `/usr/bin/grep` for counts.
- A resolution-count census is blind to *swapped import winners*: a name that
  resolves to the wrong provider emits no `unresolved` line. Class (A) fixes that
  widen glob visibility need an identity check, not a count check.
