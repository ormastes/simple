# `impl X:` -> free-function refactor wreckage: family sweep (2026-08-07)

Status: PARTIALLY FIXED. One cluster landed (`46c39fa9faf`); the rest is
enumerated below and still open.

## Scope of the sweep

58 `.spl` files under `src/` carry a `# (was: impl ...)` marker on
`origin/main` (`git grep -l 'was: impl' origin/main -- 'src/**/*.spl'`).
This sweep was driven from a **pinned `origin/main` worktree**, never the
shared working copy.

## Why a build log cannot source this family

`warning: unresolved call` SAMPLES rather than enumerates, and an unresolved
`use` is only a warning, so delete-verification is fail-open. Every finding
below comes from symbol-grep over a pinned tree, not from a compiler run.

### Two oracle bugs found while building the detector (both fail-open)

1. **`me` is a method-definition keyword**, not just `fn`. A detector that
   only collects `fn NAME` treats all 2,839 `me`-defined methods in
   `src/compiler/**` as undefined. This produced a ~10x false-positive rate.
2. **An anchored `^\s*...` definition regex without `re.M`** matches only the
   first line of the file, so the definition set comes back nearly empty and
   *everything* reads as broken. This false-RED flagged `numerictype_is_float`
   — a symbol that provably exists — and would have caused a bogus "fix".

Both were caught by injecting a known-bad symbol and confirming the count moved
by exactly one, then confirming it moved back on restore. **Any future lane
rebuilding this detector must run that inject/restore check** — the detector is
otherwise silently vacuous, and a vacuous detector reports a clean sweep.

A third vacuity: a path filter of `compiler/` against a tree extracted as
`src/compiler/...` matched zero files and reported "0 candidates" as if clean.

## Shapes found

- **(a) empty body** — a `# (was: impl X:)` header with no functions under it.
  **Zero instances remain** on `origin/main`. Previously seen in `cast_rules.spl`
  and `escape.spl`; both are now restored (`EscapeState.escapes()`,
  `can_stack_allocate()`, `merge_with()`, `to_text()` all present).
- **(b) call site renamed after the VARIABLE, not the TYPE** — no new instances
  **confirmed** beyond the already-fixed `cast_rules.spl` /
  `api_surface_snapshot.spl`. This is NOT a closure claim: the oracle finds
  undefined free calls but does not classify *why* a name is wrong, and the 20
  residual files below were not classified. Entries such as `universal`,
  `two_phase`, `static_var`, `outlives`, `jit`, `aot` could each be shape (b)
  rather than enum-variant syntax. Shape (b) remains OPEN.
- **(c) NEW: constructor free-function never generated.** The refactor rewrote
  static-constructor call sites `ClassName.create(...)` into free functions
  `classname_create(...)` but never emitted them. **FIXED in `46c39fa9faf`.**
- **(d) NEW: folded-receiver method mangle.** `self.<field>.<method>(args)` was
  rewritten to `self.<field>_<method>(<field>, args)` — the field name welded
  into the method name *and* the field re-passed as the first argument.
  **23 sites in 8 files, still open** (see below).

Shape (d) is invisible to a free-function oracle because the calls are
`.`-preceded. It was found only by reading file bodies.

## Fix direction for (c), and the evidence for it

Both directions were possible: rewrite the call sites back to
`ClassName.create(...)`, or emit the missing free constructors. The codebase's
own surviving convention decides it:

| form | count in `src/compiler/**` |
|---|---|
| `ClassName.create(` call sites | 405 |
| `static fn create(` definitions | 153 |
| free `fn <lowername>_create(` definitions | 15 |

Call-site rewrite is correct. `gc_analysis/mod.spl` confirms this
independently: its own module doc header already documents
`GcSafetyAnalyzer.create(config)` / `analyzer.analyze_function(func)`.

## Still open — shape (d), 23 sites / 8 files

The transform is `self.<field>_<method>(<field>, rest)` ->
`self.<field>.<method>(rest)`.

| file | sites | has `was: impl` marker |
|---|---|---|
| `src/compiler/35.semantics/macro_check/template.spl` | 6 | yes |
| `src/compiler/35.semantics/macro_check/hygiene.spl` | 5 | yes |
| `src/compiler/70.backend/backend/common/expression_evaluator.spl` | 4 | **no** |
| `src/compiler/35.semantics/macro_check/mod.spl` | 3 | yes |
| `src/compiler/70.backend/backend/capability_tracker.spl` | 2 | **no** |
| `src/compiler/15.blocks/blocks/builder.spl` | 1 | yes |
| `src/compiler/40.mono/monomorphize/tracker.spl` | 1 | yes |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl` | 1 | **no** |

**Three of the eight files carry no `was: impl` marker at all.** The marker set
is therefore NOT the boundary of the damage, and any sweep scoped to the 58
marker files will miss sites. Source future sweeps from the call-shape, not the
marker.

### Two hazards that make this NOT a safe mechanical rewrite

A naive regex rewrite was attempted and **reverted unlanded** — it dropped
closing parens on the single-argument form (`self.errors.is_empty(`) and
produced `self.scopes.reverse(:`. Beyond the regex, two semantic traps:

1. `expression_evaluator.spl:245` restores to `for scope in self.scopes.reverse()`.
   Per `.claude/memory`, **`reverse` MUTATES in place** while `rev`/`reversed`
   do not. A faithful textual restore here silently mutates the scope stack
   during iteration. The correct target is almost certainly `.reversed()`.
2. Several sites restore to `Dict.get(...)` (`self.scopes.get(k)`,
   `self.macros.get(k)`, `self.params.get(k)`). Per `CLAUDE.md`, under **native
   codegen `.get()` on a dict with struct/class/enum values is corrupt or
   segfaults**, and `Dict.len()` always returns `-1`. `capability_tracker.spl:66`
   restores to a `.len()` call. These need `contains_key` + index-read instead.

So this cluster needs per-site judgement, not `sed`.

## Still open — free-function unresolved calls in the 58

20 marker files still hold calls with zero definitions tree-wide. Highest
liveness first (`monomorphize` has 24 importing files, `borrow_check` 7):

- `40.mono/monomorphize/cycle_detector.spl` — 10 symbols, the same
  "helper no pass ever generates" shape as the known `points_to_get` defect:
  `visited_get` x3, `cycle_path_clone` x2, `new_to_clone` x2, `rec_stack_get`,
  `in_degree_get`, `in_degree_items`, `queue_pop`, `to_clone`,
  `metadata_add_circular_error`, `metadata_add_circular_warning`.
  **This is the highest-liveness open cluster.**
- `30.types/type_system/effects.spl` — 6 symbols.
- `55.borrow/borrow_check/mod.spl` — `pass_do_nothing` x5. Note line 227 calls
  it **bare, with no parentheses** while five other sites pass a message
  string. It has zero definitions and was never a real function. Per repo rule
  this is implement-or-delete; deleting the no-op match arms is likely correct.
- `00.common/dependency/resolution.spl` — 4 symbols.
- `35.semantics/macro_check/{hygiene,template}.spl` — 5 residual symbols after
  the landed constructor fix.
- Remainder: `recovery.spl`, `macro_contracts.spl`, `binary_ops.spl`,
  `type_coercion.spl`, `visibility_checker.spl`, `engine.spl`, `tracker.spl`,
  `borrow_graph.spl`, `lifetime.spl`, `escape.spl`, `backend_selector.spl`,
  `optimization_passes.spl`, `module_loader.spl`, `cast_rules.spl`.

Some of these are likely enum-variant or associated-function call syntax rather
than defects (`jit`, `aot`, `universal`, `two_phase`, `static_var`) and need
eyeballing before any edit. `_` and `for` entries are detector noise.

`35.semantics/volatile.spl` is in the 58 and shows 9 symbols, but is
**explicitly out of scope** for this lane and was not touched.

## Oracle coverage boundary

"Clean" above means clean under a **free-function-call** oracle over a pinned
`origin/main`. It does not cover: method-shaped calls (except the specific
folded-receiver pattern), trait dispatch, macro-generated calls, or anything
under `src/lib/**`. Do not read the unlisted 38 files as verified-clean.

## `cycle_detector.spl` — discriminator results (highest-liveness open cluster)

Attempted next; **not fixed**, because the discriminator "does the method exist
on the receiver's type?" came back mixed. Receiver types read from the source,
not inferred:

| call | receiver type | verdict |
|---|---|---|
| `visited_get(visited, node, false)` x3 | `{text: bool}` | **cannot** restore to `.get(node, false)` |
| `rec_stack_get(rec_stack, neighbor, false)` | `{text: bool}` | same |
| `in_degree_get(in_degree, edge, 0)` | `{text: i64}` | same |
| `queue_pop(queue)` | `[text]` | `queue.pop()` — `.pop()` used 36x in compiler, safe |
| `metadata_add_circular_error/_warning` | `NoteSdnMetadata` | `me add_circular_error/_warning` DO exist (`note_sdn.spl:259,262`) — safe |
| `cycle_path_clone`, `to_clone`, `new_to_clone` x5 | **text** | see below |

**The blocking finding: the two-argument `dict.get(key, default)` idiom does not
exist anywhere in `src/compiler/**` — 0 occurrences.** So the four `*_get(d, k,
default)` sites cannot be restored by dropping the first argument; they need a
`contains_key` guard plus a bracket read, which is multi-line restructuring
rather than a substitution. That restructuring is also what `CLAUDE.md` requires
for native codegen anyway. Semantically `visited_get(visited, node, false)` on a
`{text: bool}` that only ever stores `true` is just `visited.contains_key(node)`
— but that is a judgement call, not a mechanical restore, and this file is the
highest-liveness cluster found (`monomorphize`, 24 importing files), so a wrong
guess here is expensive.

The `*_clone` sites are all on **`text`** receivers (`cycle_path` is
`cycle.join("->")`; `to` / `new_to` come from iterating a `{text: [text]}`).
Per this repo's own ruling text is a VALUE TYPE, so the original was probably a
no-op clone and the correct restore may be to drop the call entirely rather than
rewrite it to `.clone()`. Needs confirmation that `text.clone()` even exists
before either choice is made.

Net: this cluster is well-specified but needs per-site judgement, not `sed`.
