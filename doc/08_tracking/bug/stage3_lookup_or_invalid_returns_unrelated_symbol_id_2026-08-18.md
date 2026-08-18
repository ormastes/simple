# Stage 3: `lookup_or_invalid(name)` returns the id of an UNRELATED symbol (2026-08-18)

Status: OPEN (P1) — root cause of the Stage 3 `enum payload dependency` fatal
flood. Containment landed separately; this defect is NOT fixed.

## Symptom

Stage 3 self-host (`native-build` of `src/app/cli/bootstrap_main.spl`) emits
fatal HIR lowering errors of the form

```
enum payload dependency `TokenKind` resolved to non-type binding `asm_arm_backend`
  (kind `const`) in `compiler.frontend.core._AstExpr.nodes`;
  expected the type `compiler.frontend.lexer_types::TokenKind::enum`
```

and produces **no binary**. Loci in
`/mnt/data/worktrees/simple-boot-snap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(630,109 bytes, mtime 2026-08-17 13:42): `source_idx=252 io_passes.spl count=27`,
`source_idx=256 outline_lexer.spl count=8`,
`source_idx=257 outline_types.spl count=7`.

## Root cause, isolated to the resolver (not the fetch)

`claim_materialized_payload_binding`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`) calls
`self.symbols.lookup_or_invalid(local_name)` with a bare payload TYPE spelling,
then reads `self.symbols.symbols[id]`. The record that comes back describes a
completely different, real symbol.

A long-standing comment there offered two candidate layers — (a) a resolver
defect returning an id for a different name, or (b) a native-codegen
`Dict<i64, HirSymbol>` bracket-read returning a foreign record — and added the
`SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1` probe to discriminate them. **The log
discriminates them on its own, and the answer is (a).**

Every symbol Stage 3 named is a real declaration, and the `defining_module` it
reported is the module that actually declares it:

| payload claimed | reported binding | kind | reported owner | actual declaration |
|---|---|---|---|---|
| `TokenKind` | `asm_arm_backend` | const | `compiler.frontend.core._AstExpr.nodes` | exported, `src/compiler/10.frontend/core/__init__.spl:208` |
| `TypeOutlineKind` | `stmt_tag` | const | `compiler.10.frontend.core.ast_stmt` | `var`, `src/compiler/10.frontend/core/ast_stmt.spl:44` — exact |
| `VariantPayload` | `STMT_CONTRACT_DECREASES` | const | `compiler.10.frontend.core.ast_stmt` | `const`, `src/compiler/10.frontend/core/ast_stmt.spl:40` — exact |
| `Visibility` (idx 256) | `ast_module_decl_count_slot` | const | `compiler.frontend.core._Ast.decl_nodes` | `var`, `src/compiler/10.frontend/core/_Ast/decl_nodes.spl:77` — exact |
| `Visibility` (idx 257) | `...outline.toplevelitem_Impl` | callable | `compiler.frontend.treesitter.outline` | `fn`, `src/compiler/10.frontend/treesitter/outline.spl:41` — exact |

A corrupt bracket read does not produce five records whose name, kind, AND
defining_module each independently agree with a real declaration in exactly that
file. **The fetch is faithful; the id is wrong.**

## Two signals about the shape of the defect

- **The same payload name resolves to different symbols as the build
  progresses.** `Visibility` hits `ast_module_decl_count_slot` at source_idx 256
  and `toplevelitem_Impl` at 257. A name collision would be stable across
  sources; a drifting id is not. This points at the id space, not at naming.
- **Every wrong binding is a bootstrap-globals-family symbol** — a module-level
  `var`, a module-level `const`, or a free `fn`, all under
  `src/compiler/10.frontend/core/**` or `src/compiler/10.frontend/treesitter/**`.
  Nothing in the sample is a type, a method, or a class member.

Together these suggest an id-assignment / id-space defect in the flat bootstrap
symbol namespace (`SIMPLE_BOOTSTRAP=1`, `--entry-closure`), where module-level
globals are accumulated across modules. That is a hypothesis, **not measured**.

## What is NOT the cause

The `register_imported_type_methods` re-entrancy breaker
(`stage3_register_imported_type_methods_infinite_recursion_2026-08-17.md`) was
suspected of trading the SIGSEGV for wrong bindings. **Refuted.** That method's
inner body defines exactly one kind of symbol,
`"{owner_module}.{Type}::{method}"`. None of the five wrong bindings is such a
symbol — three are module-level `var`/`const`, one is a free `fn`. No decision
the breaker makes in either direction can make `TokenKind` resolve to a `const`
in `ast_stmt.spl`.

## Containment already landed (does not fix this)

`hir_payload_binding_names_agree` gates both ownership contests in
`claim_materialized_payload_binding` on positive name agreement, so a wrong id
no longer becomes a hard fatal that fails the module. The mismatch stays visible
under `SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1`. Guard:
`scripts/check/check-hir-payload-binding-contest-guarded.shs`. Spec:
`test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl`.

Containment is not a fix: any other consumer of `lookup_or_invalid` in the
bootstrap symbol table is still exposed to the same wrong id, silently.

## Unblock condition

Locate why `lookup_or_invalid` returns a foreign id under the flat bootstrap
namespace. Cheapest reproduction target identified so far is
`src/compiler/10.frontend/treesitter/outline_types.spl` (source_idx 257, 7
fatals) rather than a full ~25-minute Stage 3 run — this has NOT yet been
attempted in isolation.

## Unproven

- That removing these fatals is sufficient for Stage 3 to admit. No bootstrap
  was run in the session that filed this.
- The id-space hypothesis above.
- Whether the same wrong-id defect affects non-bootstrap compiles.

## Landing record — pre-existing test-tree divergence stepped over

`check-test-tree-divergence-delta.shs` on the exact landed range
(`62f7ad741d8..a04448f02e8`):

```
base verdict: FAIL — 875 diverged vs 812 baselined (64 new, 1 fixed-but-still-baselined);
              8 mirror-only (6 unallowlisted, 0 stale-allowlist)
PASS — 71 pre-existing offender(s), 0 introduced by this range      (rc 0)
"pre-existing red is identical at BASE and NEW; this range introduces nothing"
```

The pre-existing red is another lane's and is NOT this change's to fix; it is
recorded here because landing on a delta-PASS requires it. Full offender list as
saved by the helper: `/mnt/data/tmp/test_tree_divergence_preexisting.txt`
(875 lines; first entries `integration:app/app_mcp_intensive_spec.spl`,
`integration:app/check_log_modes_spec.spl`,
`integration:app/cli_log_modes_spec.spl`).

Independently of the measurement, this range's delta is zero **by construction**:
`check-test-tree-divergence.shs` enumerates the SHADOW tree only
(`shadow_files.txt`, lines 242/268) and classifies each shadow file. This
range's sole test-tree change is an ADD in the CANONICAL tree
(`test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl`)
with no shadow counterpart, so it is never enumerated and cannot enter
`mirror_only`, `current_diverged`, or `total_common`.

## Verification status of the edited compiler file — UNVERIFIED, with a control

`bin/simple check` on `module_lowering.spl` returned rc 255 with **no error
text**; the log's last content line is `[TIMEOUT: Process killed after 300s]`.
Per the repo convention a timeout with no result line is UNVERIFIED — neither a
pass nor a fail.

Control: `bin/simple check` on origin's UNMODIFIED copy of the same file
(`git show <origin>:<path>`) timed out identically — 300s, rc 255. So the
timeout is a pre-existing property of `check` on this ~3,000-line file on this
host (load average 80-95 during the run), **not** an effect of this change. The
two arms are indistinguishable, so the edit is not implicated; it also means
compile-level verification of this file was not achieved either way.

---

## ROOT CAUSE PROVEN + FIXED (2026-08-18)

**Mechanism: `SymbolTable.reset_module()`'s eight `self.<dict>.clear()` calls
never executed.** A Dict-typed **class FIELD** receiver does not reach the Dict
dispatch on the self-hosted native backend: the field projection carries no HIR
type and its MIR temp is typed `i64`, so `receiver_is_dict` stays false and the
`local_is_runtime_dict` probe misses. The call falls into the *string* arm.
This is already documented and **proved by disassembly of the stage-2 compiler**
at `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:361-372` (for
`.contains`; `.clear()` on the same receiver shape takes the identical path) and
narrated for `.clear()` specifically at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1618-1639`.

The scalar resets on the following lines (`next_symbol_id = 0`,
`next_scope_id = 1`) *did* run. So symbol NAMES from every previously-lowered
module survived in `root_scope_symbols` / `exact_symbols` / `qualified_*` while
ids restarted at 0; each new module re-issued ids that stale names still pointed
at, and `lookup_or_invalid(name)` returned the id of an unrelated declaration.
This predicts every observed signal: the drift of `Visibility` between
source_idx 256 and 257 (ids re-issued per module), and the
bootstrap-globals-family bias (module-level `var`/`const`/free `fn` are declared
earliest, so they hold the low ids a later module's payload-type lookup lands
on). The id-space hypothesis in this row is **CONFIRMED**, with the precise
code path named.

**Why `3c31fc3aa8b` ("route Dict.clear() to rt_dict_clear") did not fix it:** it
added the dispatch *arm*, but the arm is guarded by `receiver_is_dict`, which
this receiver shape never sets. For `self.<dict>.clear()` the arm is unreachable
dead code. The snap worktree used for the failing 13:42 stage-3 log
(`513cbb7b4`) contains that commit — the fix was present and the flood persisted.

### Fix (`src/compiler/20.hir/hir_types.spl`)

1. `reset_module()` now **assigns a fresh Dict** to each of the eight maps
   (`self.symbols = {}`, …) instead of calling `.clear()`. A plain field STORE
   cannot be mis-dispatched at any layer. No handle to these dicts is held
   across a module boundary (every consumer re-reads the field; the one internal
   alias, `root_scope_symbols`, is re-published into the root `Scope` row in the
   same method).
2. `lookup_or_invalid()` now **fails closed** on an id outside
   `[0, next_symbol_id)` — the only way such an id can exist is a name binding
   that outlived its module, i.e. exactly the wrong-id shape. It returns an
   honest invalid id instead of a valid-looking foreign one.

This does **not** supersede the `hir_payload_binding_names_agree` containment in
`claim_materialized_payload_binding`; that gating is untouched and still passes.

### Guard

`scripts/check/check-hir-symbol-table-module-reset.shs` (fail-closed;
`--selftest` runs first and is fatal, with the reverted pre-fix shape as a
must-FAIL fixture, plus a resets-fixed/guard-reverted fixture and an empty-file
fixture that must yield 0 checked so the caller ERRORs).

Both arms, measured:

```
sh scripts/check/check-hir-symbol-table-module-reset.shs
PASS — 9 invariant(s) checked in .../hir_types.spl                        rc 0

# control: origin's unmodified copy
sh scripts/check/check-hir-symbol-table-module-reset.shs /tmp/hir_types_reverted.spl
FAIL — 9 invariant(s) checked, violations: reset_module-uses-clear:root_scope_symbols
  reset_module-uses-clear:symbols ... lookup_or_invalid-missing-id-range-guard  rc 1
```

### Still UNVERIFIED

- No bootstrap was run (one was already running; starting a second was
  prohibited). That Stage 3 now admits is **not** demonstrated — only that the
  mechanism which produced the flood is removed at source.
- `bin/simple check` on this file is unusable (pre-existing 300s timeout on
  compiler files, another lane owns it), so compile-level verification was not
  attempted.

### Same-family residual, NOT fixed here

`HirLowering.begin_module()` (`20.hir/hir_lowering/types.spl:283`) resets ~15
more class-field containers with the same `self.<field>.clear()` spelling and is
exposed to the identical no-op. Only the resolver's own maps were converted, to
keep this change scoped. The general defect — Dict/array-typed class-field
receivers losing their type at MIR lowering — is the real upstream fix and is
tracked at `expr_dispatch.spl:361-372`.
