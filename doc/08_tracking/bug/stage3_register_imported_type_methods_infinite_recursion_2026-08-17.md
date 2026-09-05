# Stage 3 SIGSEGV: unbounded recursion in `register_imported_type_methods` (2026-08-17)

Status: FIX IN VERIFICATION (P1)

Stage 3 self-host (`native-build` of `src/app/cli/bootstrap_main.spl` by the
admitted Stage 2 compiler) dies with **SIGSEGV, exit 139**, from stack
exhaustion in HIR lowering. Parse is NOT implicated: it completes 619/619 and
the crash lands after it.

## Evidence

Reproduced under gdb with argv and env transcribed verbatim from the
bootstrap's own provenance record
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`,
schema `simple-bootstrap-command-transcript-v2`).

- Tree: `/mnt/data/worktrees/simple-boot-snap` (frozen snapshot; `find src/compiler
  src/lib src/app -name '*.spl' -newermt '-3 hours'` returned 0 files).
- Binary: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`,
  131,324,000 bytes, mtime 2026-08-17 09:17. (NOT `bin/simple`, which is a stale
  Rust seed.)

```
Program received signal SIGSEGV, Segmentation fault.
#0  core::hash::BuildHasher::hash_one
#1  simple_runtime::value::heap::is_registered_heap_ptr
#2  simple_runtime::value::heap::validate_heap_obj
#3  simple_runtime::value::heap::get_typed_ptr_mut
#4  rt_string_len
#5  rt_string_replace
#6  compiler.common.module_path_naming.module_logical_name_from_path
#7  HirLowering.register_imported_type_methods
#8  HirLowering.register_imported_symbol
#9  HirLowering.materialize_imported_callable_type_dependencies
#10 HirLowering.register_imported_type_methods
   ... frames #7-#9 repeat for the entire backtrace ...
rsp = 0x7fffff7ff000   <- stack guard page
rbp = 0x1              <- bogus
```

`rsp` on the guard page plus an unbounded repeating 3-frame cycle is stack
exhaustion, not a wild pointer. Frames #0-#6 are incidental: they are merely
what happened to be executing when the last page ran out.

## Mechanism

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`, cycle:

```
register_imported_type_methods                        (:1453)
  -> materialize_imported_callable_type_dependencies  (:1469, :1492)
  -> register_imported_symbol                         (:1433, :1436, :1440, :1444, :1447, :1451)
  -> register_imported_type_methods                   (:768 composite, :789 enum)
```

Every guard on the path is **check-then-recurse** against the symbol table
(`lookup_qualified_type_raw(...) < 0`; `lookup_or_invalid(...).is_valid()`).
That terminates only if the callee is fully registered BEFORE the descent.

- **Composite path terminates.** `:741-744` defines the symbol and calls
  `bind_qualified_type`, and `:745-746` returns early when `already_bound`, so a
  re-entrant call is refused.
- **Enum path does not.** `:769-789` calls `register_imported_type_methods`
  unconditionally at `:789` with no `already_bound` early return. That is
  deliberate -- gating it inside `not already_bound` silently routed imported
  `DbValue.to_text()` to generic enum stringification (comment at `:784-788`).

So two types declared in one module whose method SIGNATURES mention each other
re-enter the cycle forever.

## Class recurrence

This is the same failure class as
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`. The essay at
`src/compiler/20.hir/hir_types.spl:396-433` records that instance: a
`rt_dict_contains` false negative on a struct-valued `Dict` disabled the only
re-entrancy breakers in this cycle, "producing unbounded mutual recursion ...
that overflowed the stack and SIGSEGVed Stage 3 with zero diagnostic output."

Standing lesson: **every breaker in this cycle has historically been a
membership test that can fail open.** A breaker here must not depend on Dict
membership semantics.

## Fix

Re-entrancy breaker at the top of `register_imported_type_methods`; the original
body moved verbatim to `register_imported_type_methods_inner`. Registering a
type's methods is idempotent, so refusing a re-entrant call loses no work -- the
in-flight outer call performs it.

State: `imported_type_methods_in_progress: [text]` on `HirLowering`
(`src/compiler/20.hir/hir_lowering/types.spl` -- field, initializer, and a reset
in `begin_module`).

Deliberately a plain `[text]` used as a stack with a linear scan, **not a Dict**:
per the recurrence note above, a Dict membership breaker in this exact cycle has
already failed open once and cost a full day of Stage 3 debugging. Depth guarded
is type-reference nesting depth, which is small.

Notably the fix does NOT revert `:789`, so the `DbValue.to_text()` behaviour that
motivated the unconditional call is preserved.

## Why this took a day to find

`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log` was
**0 bytes** across every failing run, so the crash was unattributable. The
redirect is correct (`) >"$log" 2>&1`,
`scripts/check/lib/bootstrap-stage3/command-snapshot.shs:227`, status read on
the next line at `:228`). It is empty by design: the provenance gate at
`scripts/bootstrap/bootstrap-from-scratch.sh:2026-2028` relies on the in-process
pure-Simple driver printing nothing to stdout in order to detect Rust-seed
delegation. Diagnostics went only to `SIMPLE_BUILD_PROGRESS_EVENTS`.

Two contributing traps, both since fixed, that sent three lanes to wrong causes:

1. **`exit-2` is not the compiler's status.** The progress log's terminal
   `milestone=exit-2` is the WRAPPER SCRIPT's exit code (non-strict mode ->
   warning -> "Stage 3 unavailable" -> 2). The compiler's real status is 139.
   `bootstrap-from-scratch.sh:2069` also sets `stage3_status=2` for a genuine
   sanity failure, which is a DIFFERENT event -- distinguish them by whether
   `stage3/<platform>/stage3-sanity.env` exists. In every run here it did not,
   so sanity never ran.
2. **Progress `current=` was stale by up to 63 files** (the `% 64 == 0` cadence
   at `driver_source_pipeline_parsing.spl:275` pre-`4d1aca2d799`), which framed
   this as a "parse tail stall" and named an innocent file. Now one receipt per
   file. Same trap still live for the `source_closure` phase
   (`driver_source_pipeline_loading.spl:192,196`).

Also note **stack-overflow depth is sensitive to environment size**, so the
crash appears to move: the same binary died at parse file 1 in one run and
completed all 619 files then crashed in HIR lowering under gdb. That is not
nondeterminism or ASLR -- do not read it as a wild pointer.

## Status re-check 2026-08-17 — STILL "FIX IN VERIFICATION" (fix present, not re-executed)

binary identity: `readlink -f bin/simple` = `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`; `stat -c '%s %y'` = `59537240 2026-08-17 12:58:51.339525019 +0000`

The breaker described under "Fix" is in the tree and wired through the accessors:

```
$ grep -n "imported_type_methods_in_progress" \
      src/compiler/20.hir/hir_lowering/types.spl \
      src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl
types.spl:102   imported_type_methods_in_progress: [text]          # field
types.spl:255   imported_type_methods_in_progress: empty_...,      # initializer
types.spl:313   me imported_type_methods_in_progress_has(key: text) -> bool
types.spl:319   me imported_type_methods_in_progress_push(key: text)
types.spl:322   me imported_type_methods_in_progress_pop(key: text)
types.spl:355   self.imported_type_methods_in_progress = []        # begin_module reset
module_lowering.spl:1526  if self.imported_type_methods_in_progress_has(reentry_key):
module_lowering.spl:1528  self.imported_type_methods_in_progress_push(reentry_key)
module_lowering.spl:1531  self.imported_type_methods_in_progress_pop(reentry_key)
```

It remains a plain `[text]` stack (not a Dict), as the recurrence note requires.
Verification still needs a stage-3 self-host run to show the SIGSEGV is gone;
that is a bootstrap, which was out of scope for this session, so no pass is
claimed. Nothing changed.

## 2026-08-18 — second, SEPARATE defect found and fixed: unsound payload-binding contest

Binary identity for this session: `readlink -f bin/simple` =
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
`stat -c '%s %y'` = `59621024 2026-08-17 20:28:24 +0000`. No bootstrap was run
and no binary was rebuilt or redeployed (~15 lanes depend on that binary), so
nothing below is a Stage 3 runtime result.

### The re-entrancy breaker did NOT cause the error flood — refuted structurally

The open question was whether the breaker trades the SIGSEGV for wrong bindings,
i.e. whether the `enum payload dependency ... resolved to non-type binding`
errors are the breaker cutting a needed traversal. It is not, and the argument
is structural rather than statistical:

- `register_imported_type_methods_inner` defines only METHOD symbols, named
  `"{owner_module}.{Type}::{method}"`, plus their signature type dependencies.
  It never defines the TYPE symbol itself — that is `register_imported_symbol`.
- `claim_materialized_payload_binding` consults
  `self.symbols.lookup_or_invalid(local_name)` with a bare payload TYPE
  spelling (`TokenKind`), which can never match a `::`-qualified method symbol.

So refusing a re-entrant method registration cannot change what that lookup
returns, and cannot manufacture the observed error. Termination of the breaker
itself is sound: the key is pushed before the descent and popped after, `has()`
prevents duplicates so the `!=` filter in `_pop` removes exactly one entry, and
the stack depth is type-reference nesting depth.

**Unproven, stated as such:** `reentry_key` is `{module}::{type}` and ignores
`local_owner`. A re-entrant call arriving with a DIFFERENT `local_owner` would
be refused, and its methods would be registered only under the outer call's
`owner_module` prefix. Whether that combination occurs in practice was not
measured.

### The actual defect: contesting a binding against a record that is not it

`claim_materialized_payload_binding` reaches an existing symbol through two hops
that both have known failure modes — `lookup_or_invalid(local_name)` returning
an id for a different name, and the chained class-field
`Dict<i64, HirSymbol>` bracket read returning a foreign record (the two
alternatives the pre-existing `SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE` probe was added
to discriminate). It then contested ownership against whatever came back.

That is unsound by construction, independently of which hop is at fault: the
code never established that the fetched record IS the binding for `local_name`,
so a "conflict" between them is a claim about two unrelated entities. The Stage 3
evidence says exactly this out loud — payload `TokenKind` reported as bound by
`asm_arm_backend`, kind `const`, and per the earlier note **in 0 of the 78
unique conflicts did the two sides even share a name**.

Fix: `hir_payload_binding_names_agree(local_name, origin_item_name, symbol_name)`
— a positive identity test in the same spirit as `hir_payload_kind_is_type`.
A record matching neither the local payload spelling nor the terminal declared
name (the two names the binding can legitimately carry, since
`register_materialized_payload_named_dependency` registers the terminal item
under the payload's local alias) gets no vote, and control falls through to
record the binding. BOTH contests are gated, not just the non-type one: a name
mismatch invalidates the identity comparison exactly as much as the kind
comparison. The mismatch stays visible under the existing probe env var, since
it is still a real resolver/fetch defect — just not a conflict.

This does NOT fix the underlying wrong-id-or-wrong-fetch defect. It stops that
defect from being converted into a hard error that fails the module.

### Discriminating measurement (both arms, one tree, one guard)

`scripts/check/check-hir-payload-binding-contest-guarded.shs`, run against the
same guard binary with only the target file swapped:

| arm | target | verdict | rc |
|---|---|---|---|
| applied | working tree | `PASS — 7 invariant(s) checked ..., 0 violated` | 0 |
| reverted | `git show FETCH_HEAD:<same path>` (origin `19835f59fa7`) | `FAIL — 7 invariant(s) checked ..., 5 violated` | 1 |
| selftest | 5 fixtures | `PASS — 5 selftest fixture(s) checked` | 0 |

The reverted arm names the ungated contest explicitly, so the control fails for
the right reason rather than incidentally. The guard's `--selftest` is fatal and
includes the reverted shape as a must-FAIL control and a missing file as a
must-be-unscannable case (ERROR, never a clean pass).

**What this measurement does NOT prove:** it is a source-contract A/B, not a
Stage 3 run. Whether the error flood disappears and Stage 3 admits is UNVERIFIED
— that needs a bootstrap, which another lane owns and which was out of scope.

Spec: `test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl`.

Status: the SIGSEGV breaker remains FIX IN VERIFICATION (unchanged, still needs a
Stage 3 run). The payload-contest fix is landed with a source-contract A/B and is
likewise unverified at Stage 3 runtime.

## 2026-08-18 — boot-snap stage-3 log settles BOTH open questions without running anything

Source: `/mnt/data/worktrees/simple-boot-snap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(630,109 bytes, mtime 2026-08-17 13:42 — read-only; that tree was not modified).
Named loci from the bootstrap-admission lane: `source_idx=256 outline_lexer.spl count=8`,
`source_idx=257 outline_types.spl count=7`, `source_idx=252 io_passes.spl count=27`.
Stage 3 produced no binary.

### The breaker is REFUTED as the cause — by the identity of the wrong bindings

The five distinct symbols stage 3 named as "competing owners" are, every one of
them, a REAL declaration, and the `defining_module` it reported is the module
that actually declares it:

| payload claimed | reported binding | reported kind | reported owner | actual declaration |
|---|---|---|---|---|
| `TokenKind` | `asm_arm_backend` | const | `compiler.frontend.core._AstExpr.nodes` | exported, `10.frontend/core/__init__.spl:208` |
| `TypeOutlineKind` | `stmt_tag` | const | `compiler.10.frontend.core.ast_stmt` | `var`, `10.frontend/core/ast_stmt.spl:44` — **exact module match** |
| `VariantPayload` | `STMT_CONTRACT_DECREASES` | const | `compiler.10.frontend.core.ast_stmt` | `const`, `10.frontend/core/ast_stmt.spl:40` — **exact** |
| `Visibility` (idx 256) | `ast_module_decl_count_slot` | const | `compiler.frontend.core._Ast.decl_nodes` | `var`, `10.frontend/core/_Ast/decl_nodes.spl:77` — **exact** |
| `Visibility` (idx 257) | `...outline.toplevelitem_Impl` | callable | `compiler.frontend.treesitter.outline` | `fn`, `10.frontend/treesitter/outline.spl:41` — **exact** |

Two conclusions follow directly, neither needing a run:

1. **This is defect (a), not (b).** The pre-existing `SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE`
   probe was added to discriminate a resolver defect (wrong id) from a
   native-codegen `Dict` bracket-read defect (right id, foreign record). A
   corrupt fetch does not return five records whose name, kind, AND
   defining_module all independently agree with real declarations in exactly
   those files. The fetch is faithful; **`lookup_or_invalid(local_name)` is
   returning the id of an unrelated symbol.** The probe does not need to be run.
2. **`register_imported_type_methods` cannot be the cause.** Its inner body
   defines exactly one kind of symbol: `"{owner_module}.{Type}::{method}"`.
   Not one of the five is such a symbol — `stmt_tag` and
   `ast_module_decl_count_slot` are module-level `var`s, `STMT_CONTRACT_DECREASES`
   is a module-level `const`, `toplevelitem_Impl` is a free `fn`. No decision the
   breaker makes, in either direction, can cause a bare payload spelling like
   `TokenKind` to resolve to a `const` in `ast_stmt.spl`. **The hypothesis that
   the breaker trades a crash for wrong bindings is refuted at the named locus.**

Two further signals on the real defect, recorded for whoever fixes it:

- **The same payload resolves differently as the build progresses.** `Visibility`
  hits `ast_module_decl_count_slot` at source_idx 256 and
  `toplevelitem_Impl` at 257. A name collision would be stable; a drifting id
  is not. This looks like an id-space defect in the flat bootstrap symbol
  namespace, not a naming conflict.
- **Every wrong binding is a bootstrap-globals-family symbol** — module-level
  `var`/`const`/free `fn` under `10.frontend/core/**` or `10.frontend/treesitter/**`.

The fix in the section above is the correct containment for this and nothing
more: a wrong id no longer becomes a hard fatal that fails the module, and
because the gate demands positive name agreement it cannot mask a genuine
conflict. **It does not fix the resolver defect**, which remains open and is the
thing that should be filed and fixed next. Whether removing these fatals is
sufficient for Stage 3 to admit is UNVERIFIED — no bootstrap was run.

Also noted from another lane, so it is not re-chased here: `source_closure 0/0`
was REFUTED as a defect (caused by passing a module path instead of a file path
to `--entry`).
