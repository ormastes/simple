# CORRECTION 2026-08-31 — this record's original framing was WRONG

Three claims in the original text below are refuted by a follow-up trace. They are
left in place, struck here rather than silently edited, because the wrong framing
is instructive:

1. **"Option, Dict and Result are builtins failing to resolve" — FALSE, and it was
   called "the load-bearing observation".** Those 225 counts are
   `[hir-*-origin-unresolved]` ADVISORY eprints, not fatals. There are ZERO fatals
   for Option/Dict/Result. `lower_type` has explicit arms for them
   (`20.hir/hir_lowering/types.spl:840` Result, `:857` Dict; argless Option takes
   the soft `recovered` path at `:985`), so builtins never reach `self.error`. The
   advisory walk simply has no builtin table. A non-problem.
2. **"1,088 unresolved-type fatals" — inflated.** 1,088 is the total `[hir-fatal]`
   count; only **796** are `unresolved type:`. The rest are `unresolved name:` and
   `missing importing module surface`.
3. **"across 538 files" — wrong denominator.** 538 is the number of files LOADED.
   Distinct files carrying a fatal is **200**.

Lesson worth keeping: the counts came from `grep -c` over mixed diagnostic
severities. Advisory eprints and hard fatals were tallied together, and the most
alarming-looking group turned out to be the advisory one.

# ACTUAL ROOTS — two, not one

**Root A — truncated entry closure: 543 fatals (68%).** The declaring file is never
loaded at all. Phase 1 reports `closure:done scanned=538` out of ~1500 files, and
replaying the closure's own import extractor over those 538 finds **117 dotted
import targets never loaded** (92 with a real file on disk) — including
`compiler.frontend.core.parser_stmts`, `.parser_decls_use`, `._Ast.decl_nodes`,
`compiler.backend.c_backend_translate`, and `feature_caps_types`.
`src/compiler/20.hir/hir_operators.spl` has **zero mentions in the entire Stage-3
log**, which is why HirBinOp 159 + HirUnaryOp 145 + HirAssignOp 125 = 429 fatals
appear, plus TargetCapsKind 30 + X86Caps 29.

This also explains why the first attempted fix was INERT: adding an import of
`hir_operators` to `hir_definitions.spl` cannot help when `hir_operators.spl` is
never loaded. That attempt was measured (counts identical, 1088 -> 1088) and
reverted.

Ruled out for Root A: extractor logic (a Python replay emits every missing
target), `export use` specificity (192 dropped edges are plain `use`), list
truncation, substring misroute, and Dict array-read corruption.

**Root B — glob-only visibility: 253 fatals (32%).** The class already documented
at `hir_definitions.spl:10-45` (CompileError 20, ConcreteType 19, MirModule 18, …),
same shape as the previously fixed `MethodResolution` and
`AsmConstraintKind`/`AsmLocation`.

# Emitters

- Fatal: `20.hir/hir_lowering/types.spl:994` — `self.error("unresolved type: {name}", span)`,
  reached only from `case _` after `self.symbols.lookup` fails.
- Advisory: `20.hir/hir_lowering/_Items/module_reexport_materialization.spl:492` and `:766`.
  That walk resolves a dependency to its physical origin using only declarations,
  `export use` hops, and explicit named imports — globs excluded by design.

# Open question gating the Root A fix

The fix lives in `driver_source_pipeline_loading.spl:313-333`. Its shape depends on
whether `_driver_resolve_entry_import` returned `""` (in which case the loud
`add_error` at `:330` fired 117 times but is absent from this stderr log, which
carries only eprint/log_phase output), or whether one of the two silent
`contains_key` `continue`s at `:314-320` swallowed them.

# Attribution — still cannot tell

No baseline exists; Stage 3 had never been reachable. One datum: `hir_operators.spl`
was split out of `hir_definitions.spl` on 2026-08-21 (`4b88aebf00b`) and is reachable
only via that `export use`, so the largest single family is 10 days old. But
`parser_stmts` and `_Ast` are long-standing, so the closure defect itself is
probably not new.

# Stage 3 self-host: 1,088 HIR `unresolved type` fatals across 538 files, including builtins

- **Filed:** 2026-08-31
- **Status:** OPEN — first observation; Stage 3 had not been reachable before today
- **Blocks:** Stage 3 self-host, therefore Stages 4 and 5
- **Platform:** aarch64-apple-darwin. **NOT shown to be macOS-specific.**
- **Reached via:** Stage 2 admission (`8cef6333ac8`) + planner-admission-v2 receipt
  (target `//bootstrap:stage3`, reason `verify-landed-compiler-fix`)

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage3
--backend=llvm --bootstrap-receipt=<path>` reaches Stage 3 and fails:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); Stage 4 unavailable
error: --stop-after-stage3 requires a successful Stage 3 compiler
```

Full stderr (816 KB) at
`build/bootstrap/stage3/<triple>/stage3-tmp/native-build-stderr-<pid>.log`.

## Measured scope

1,088 `[hir-fatal]` diagnostics across 538 distinct files. Most frequent
unresolved names:

| count | name |
|---|---|
| 162 | `HirBinOp` |
| 148 | `HirUnaryOp` |
| 126 | `HirAssignOp` |
| 115 | `Option` |
| 67 | `Dict` |
| 44 | `Result` |
| 32 | `TargetCapsKind` |

**`Option`, `Dict` and `Result` are language builtins.** Their appearing as
"unresolved type" is the load-bearing observation: this is not a missing import in
one module, it is builtin/prelude type registration failing on the Stage-3
self-host path. The compiler-internal enums (`HirBinOp`/`HirUnaryOp`/`HirAssignOp`)
are the same failure applied to types reached through re-export chains.

Companion diagnostic naming the mechanism:

```
[hir-callable-dep-origin-unresolved] owner=compiler.common.di dependency=Dict:
no declaration, re-export hop, or explicit import of this name in the owner
```

## Attribution — stated honestly

This is the FIRST time Stage 3 has been reachable in this work. Until Stage 2 was
admitted earlier today it failed at the admission gate, so nothing downstream ever
executed. That means:

- This failure is **not shown to be a regression** from the nine defects fixed to
  reach admission. It may be long-standing and simply never observed.
- It is equally **not shown to be pre-existing**. No baseline exists. Do not assert
  either direction without evidence.

A cheap discrimination, if needed: the nine fixes are all in codegen/lowering
(MIR, backend, one frontend desugar). This failure is in NAME RESOLUTION, a
different layer none of them touched. That is suggestive of pre-existing, not
proof.

## Difference from the Stage-2 fixture

Stage 2 admission compiles a 3-line fixture plus one imported module. Stage 3
compiles the ENTIRE compiler (538 files here). The defect needs a module graph of
real size, which is why no smaller repro surfaced during admission work.

## Next

Determine where builtin/prelude types (`Option`, `Dict`, `Result`) are registered
for a self-host compile and why that registration is absent or unreachable in
Stage 3. Fix that first: 115+67+44 = 226 of the 1,088 fatals are builtins, and the
re-export-hop failures may share the same root.

# ROOT A LOCALISED 2026-08-31 — silent "already satisfied" skip, 203-module gap

Phase 1's own trace gives the discrepancy directly:

```
[BOOTSTRAP-PHASE] phase1:load_sources:closure:done scanned=538 logical=741
```

**741 logical module paths marked seen, 538 physical files loaded — a 203-module
gap.** That is the population the 117 dotted missing targets belong to (203
includes single-segment/prose pseudo-imports that are deliberately skipped).

The branch is identified by elimination, not inference:

- The LOUD path at `driver_source_pipeline_loading.spl:330` emits
  `unresolved import '<mp>' (used in <path>)` whenever the resolver returns "" for
  a DOTTED module path. The Stage-3 log contains **zero** such lines
  (`grep -c "unresolved import '"` = 0). So `_driver_resolve_entry_import` never
  failed — the resolver is NOT the problem, and the earlier open question about
  which branch fired is now answered.
- That leaves the two silent `continue`s at `:313-320`. The first
  (`closure_seen_mods`) cannot account for it: it fires only on a genuine repeat,
  and it runs BEFORE the logical counter is incremented for that path.
- The second is the culprit shape:

```
    closure_seen_mods[closure_mp] = true          # logical++
    if closure_loaded_mods.contains_key(closure_mp):
        # Already satisfied by an explicit --source root (or an
        # earlier closure step): nothing to resolve, not an error.
        continue                                   # no physical load
```

A module counted logical, skipped as "already satisfied", and never actually
compiled into the set produces exactly the observed signature: logical > physical,
no error, and a later hard `unresolved type` when its declarations are needed.

## Why this explains hir_operators.spl specifically

Stage 3 runs with `--source src/compiler --source src/app --source src/lib`, which
pre-populates `closure_loaded_mods`. `src/compiler/20.hir/hir_operators.spl` lives
under one of those roots, so it is claimed as already satisfied — yet it has ZERO
mentions anywhere in the Stage-3 log, i.e. it was never loaded. Its 429 dependent
fatals (HirBinOp 159 + HirUnaryOp 145 + HirAssignOp 125) follow.

## Next step for whoever continues

Find where `closure_loaded_mods` is populated from the `--source` roots and
determine whether membership means "file present under a source root" or "file
actually loaded into the compile set". If it is the former, the fix is to make the
check mean the latter (or to load on miss rather than assume). Note the keys are
LOGICAL module names, so `module_logical_name_from_path` is on this path — two
physical files that normalise to one logical name would also mark the second as
already satisfied.

