# Stage-3 callable dependency named/glob precedence (2026-08-21)

## Status

Pure-Simple fix and regressions implemented; fresh bootstrap verification is
pending.

## Exact reproducer

The receipt-bound Stage-3 command recorded in
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
completed all 954 streaming surfaces, then first failed while importing
`HirStmtKind` with:

```text
unresolved type: FrontendAsmTargetSpec
```

The previous run with the original field spelling had instead failed with
`ambiguous explicit callable dependency AsmTargetSpec in
compiler.hir.hir_definitions`.

## Root cause

`hir_definitions.spl` intentionally has both a broad `hir_types.*` route and a
direct named route to the three frontend ASM types. Callable signature
dependency materialization treated a differing glob candidate and named
candidate as peers. Aliasing the named imports avoided that diagnostic, but
the downstream staged projection did not preserve the alias spelling, causing
the first error above and a broad imported-type cascade.

## Fix

Retain the declaration's real type names. Explicit named routes now take
precedence over overlapping glob routes; multiple named routes or multiple
glob routes at the same precedence must still agree or fail as ambiguous.
Behavioral coverage imports a callable whose signature type exists behind both
a conflicting glob and an explicit named route. Adjacent source-contract
coverage retains the same-precedence ambiguity diagnostic.

## Verification

Run one fresh Stage-2 admission, produce a new planner admission receipt, and
run one receipt-bound Stage-3/4 deploy. The first HIR diagnostic must be absent;
only a full Stage-4 result can unblock bootstrap must-check evidence.

---

## REGRESSION (2026-08-26): the whole fix was reverted by a stale-snapshot commit

### Finding

The Stage-3 self-host wall at module **261/713** (RC=1,
`ambiguous explicit callable dependency \`Expr\` in
\`compiler.hir.hir_lowering._Items.module_build\``, and the same for `StmtKind`
in `module_declarations_bootstrap`) is **not a new defect**. It is this bug,
re-opened by a revert.

Commit `4edef8fab8` — *"feat: snapshot current development state"*, 2026-08-26
01:21, **11,225 files, +1,275,284 / -860,823** — is a whole-working-copy
snapshot pushed from a stale tree. It is exactly the anti-pattern fenced by
`.claude/rules/vcs.md` § "Sync must never clobber". Against `src/compiler/20.hir/`
alone it is **831 insertions / 4,235 deletions across 36 files**, wiping months
of HIR-lowering work, including every part of this bug's fix.

Evidence (`git show <rev>:<path> | grep -c`, on
`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`):

| symbol | `4edef8fab8~1` (good) | HEAD `2b35049f8d` |
|---|---|---|
| `canonical_callable_dependency_candidate` | 3 | **0** |
| `selected_rank` (named>glob precedence) | 7 | **0** |
| `hir_ambig_dep_trace` | 33 | **0** |
| `module_surface_syntactically_exports` (use) | 2 | **0** |

`module_surface_syntactically_exports` itself survives at HEAD
(`module_surface_export_index.spl:635`) — only its *caller* was deleted, which is
why nothing failed to compile and the revert was invisible.

Nine commits landed after the snapshot are already piecemeal repairs of the same
clobber, one of them named for it
(`179e18fc74 fix(lib,hir): restore Sha256StreamV1 + ModuleSurface semantic_hash
fields clobbered by 4edef8fab8e`). Nobody restored the callable-dependency fix.

### Mechanism — THREE defects share this one message

Not one defect. The reverted code fixed three, each with its own in-source
receipt:

1. **Explicit-over-glob precedence (EXPLICIT-OVER-GLOB, 2026-08-22).** The sweep
   in `materialize_imported_callable_explicit_dependency_inner` writes named-import
   candidates and wildcard candidates into the SAME `selected_target` with
   last-writer-wins, and flags any disagreement ambiguous. Measured candidate set
   (run14, recorded in the reverted source): the owner's four candidate rows were
   **glob / glob / named / glob** — the named row naming
   `compiler.backend.backend.backend_api`, the globs naming
   `compiler.frontend.parser_types_expr`. Last-writer-wins made the trailing GLOB
   the selection and flagged the pair ambiguous. Fix: a `selected_rank` tier
   (1 = explicit named row, 0 = glob, -1 = none); ambiguity is computed only
   WITHIN a rank, and the first explicit route clears any glob-vs-glob ambiguity.
2. **Phantom facade terminal.** A materialized facade surface lists the
   declarations it re-exports in its ORDINARY declaration arrays, so
   `hir_module_declares_item(facade, "Expr")` is true for every facade on a route
   as well as for the real terminal. Two routes to the SAME declaration therefore
   produce two DIFFERENT `(target_index, item_name)` pairs and read as ambiguous.
   This is why `StmtKind` — which has exactly ONE declaration in the compiler tree
   (`10.frontend/parser_types_expr.spl:644`) — can be reported ambiguous at all;
   no cross-module name collision is involved. Fix:
   `canonical_callable_dependency_candidate` resolves the frozen
   `export_origin_index` carrier chain (bounded at depth 8) to one canonical
   terminal before comparing.
3. **Private imports chased as transitive exports.** The old fallback called
   `find_reexport_source` on every import of every wildcard target, so importing
   `mir_instruction_kinds.*` invented routes to that module's PRIVATE
   `mir_types.*` dependency. **This confirms the prior session's
   wildcard-import-overlap finding in `mir_instruction_graph.spl` as a genuinely
   SEPARATE mechanism from the item-degenerate case.** Fix: admit a chase only
   for a spelling the target syntactically exports
   (`module_surface_syntactically_exports`).

The `Expr` / `StmtKind` failures at module 261 are mechanisms (1) and (2);
`mir_instruction_graph.spl` is mechanism (3).

### Why the perf fix did not move the wall

`808f5cc2dd perf(hir): make reexport visited lookup constant time` landed AFTER
the snapshot. It made the walk 9.57x faster (legA 25,190,210 ms -> legB
2,632,363 ms) but changed no resolution decision, so both Stage-2 binaries stop
at the identical module 261/713 with RC=1. Same endpoint, same failure — the
signature of a semantic wall, not a timeout.

### Reproduction (no bootstrap required)

The Rust seed can INTERPRET the Simple compiler, which executes this Simple
HIR-lowering code, so the wall reproduces in one command without a Stage-2
build:

```sh
./bin/simple run src/app/cli/bootstrap_main.spl compile \
    src/compiler/20.hir/hir_lowering/_Items/module_build.spl \
    --format=smf -o /tmp/mb.smf
```

`SIMPLE_AMBIGDBG=1` prints the sweep's candidate set once the trace helpers are
restored (`[ambig-dep] sweep-candidate route=named|glob owner=... dep=... target=... item=...`).

A smaller synthetic repro was attempted and does NOT fire: mechanism (2) requires
a facade surface that materializes re-exports into its declaration arrays, which
a plain three-file `use pkg.term.*` chain does not create. The command above is
the minimal reliable reproduction.

### Restore

Restored surgically on top of HEAD rather than by reverting
`4edef8fab8`'s 20.hir hunk wholesale — a wholesale revert re-introduces the
pre-snapshot parallel-array walk state and would undo `808f5cc2dd`'s
constant-time `visited_depth` lookup and the post-snapshot repairs. Restored:
`canonical_callable_dependency_candidate`, the `selected_rank` sweep,
and `hir_ambig_dep_trace{,_enabled}`.

### Still open

`4edef8fab8` deleted 860,823 lines across 11,225 files. Only its
`src/compiler/20.hir/` callable-dependency portion is addressed here. **The rest
of that clobber has not been audited** and other landed fixes are very likely
still reverted. That triage is out of scope for this record.

### Correction to the "Reproduction" section above — NOT yet verified to fire

The seed-interpreted command is a *candidate* reproduction, not a confirmed one.
Two attempts on a loaded host were killed while still in the parse phase
(43/124 and 40/124 modules, ~10 s per module); neither reached HIR lowering, so
neither produced nor excluded the diagnostic. Per `.claude/rules/testing.md`, a
run with no result line is UNKNOWN, not clean. Note also that the module-261
failure is raised while lowering an IMPORTER of `module_build` (the sweep runs
when an importer materializes `module_build`'s `extern fn rt_enum_payload(value:
StmtKind) -> Expr`), so `module_import_resolution.spl` is the more faithful
compile target than `module_build.spl`.

A synthetic three-file repro (terminal declaring `Expr`/`StmtKind`, a facade
glob-re-exporting it, a consumer globbing both plus the extern) was written and
does not fire: mechanism (2) needs a facade surface that materializes re-exports
into its declaration arrays, which a plain `use pkg.term.*` chain does not
create. Building that minimal repro remains open work.
