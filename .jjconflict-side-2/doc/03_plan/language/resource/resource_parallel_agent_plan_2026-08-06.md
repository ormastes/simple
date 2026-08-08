# Plan: `resource` Feature — Parallel Agent Development

**Date:** 2026-08-06 (updated 2026-08-07, second findings round)
**Scope:** Phase 1 (Grammar A) through pilot migration; Phases 2/3 gated behind it.
**Docs:** research/architecture/design under `doc/{01_research,04_architecture,05_design}/language/resource/`.

Work packages (WPs) are sized so a mid-tier agent (Sonnet, or Haiku for the
mechanical ones) can complete one WP in a single session with only this plan +
the design doc + the named files. Each WP states: files, task, acceptance
check, and model tier. Agents MUST NOT touch files outside their WP (parallel
sessions share the WC — see `.claude/rules/vcs.md`). Commit + push per WP.

## #0.5 — YOUR ACCEPTANCE ORACLE IS PROBABLY UNREACHABLE (added 2026-08-07, read before WP-B/C/E/G/I/J)

**WP-A landed** (`1a6a7da02f6`, `7c60ee34bc0`): `resource` declarations and the
`@sffi` decorator now parse, implemented as a **soft keyword** so the 112
identifier uses of `resource` in `src/` cannot break. Regression spec
`test/01_unit/compiler/resource/resource_decl_spec.spl` is 18/18 and was proven
non-vacuous by sabotage (injecting a `parser_error` turned it red; reverting
restored green).

**But the pilot spec is still RED, and that is correct.** It stays
`Results: 1 total, 0 passed, 1 failed` after the parser landed, because:

> `bin/simple test` re-execs a child **Rust seed**, and the seed's parser reads
> the spec file's own module-level syntax. The pilot's error is Rust `Debug`
> output from `src/compiler_rust/parser/src/error.rs:73`. **No pure-Simple
> frontend change can make that spec parse.**

Proven by positive control, not inference: a spec containing `layer ProbeLayer`
— an **already-landed, working** pure-Simple soft keyword — fails identically
with `function 'layer' not found`.

### What this means for every remaining WP

- **Do NOT write acceptance as "real source using the new syntax, in a spec
  file."** WP-B, WP-C, WP-E, WP-G, WP-I and WP-J all state acceptance that way
  today. Every one of them is unreachable as written. WP-I (interpreter/JIT
  parity) is worst affected.
- **Use the source-string harness instead** — the `const_spec.spl` shape: feed a
  source string to `parse_module_body()` and assert on the resulting AST/HIR.
  That is what WP-A's passing regression spec does.
- **Production `src/**` code cannot adopt `resource` syntax yet either**, for the
  same reason: the seed compiles the tree. Migrating library code is gated on
  stage-3 self-host, not on this feature's own WPs. Land the pipeline behind the
  syntax; migrate call sites after stage-3.

### Other corrections from WP-A

- **WP-0's "the new token is 222" is wrong.** `layer` and `cli` use no token
  constant at all. Adding one is precisely the hard-keyword risk §0 warns about.
- **WP-0's ~13-site wire-point checklist was not needed** — the inert-marker
  path carries the metadata in two edits.
- **WP-B is smaller than assumed:** `*T` in type-annotation position **already
  parses** today (probed directly).
- **Design §1 gap:** `invalid: -1` lexes as **two tokens**. Handling only single
  tokens silently drops the sign.
- The count in §0 says 115 identifier uses of `resource`; measured by
  identifier-position regex it is **112** (raw word count 905 includes comments
  and `resource_*` compounds). The conclusion is unchanged.

## #0 — Stage-3 self-host is the blocker above every WP below (read first)

**No self-hosted `bin/simple` exists.** The deployed `bin/simple` /
`bin/release/x86_64-unknown-linux-gnu/simple` is the **Rust seed**, which has
**zero** borrow-check code — `grep -rln "borrow_check\|BorrowCheck"
src/compiler_rust/driver/src/` returns no hits. Every WP in this plan edits
`src/compiler/**/*.spl` (the self-hosted Simple compiler); the frontend
feedback loop (`bin/simple test <spec>`) proves those edits work *inside the
interpreter's own module loader*, but that is not the same thing as the
change shipping in the binary users run.

Stage-3 self-host (stage2 compiler recompiling itself) is a **known, currently
open blocker**, per `.claude/rules/bootstrap.md` (2026-08-06): `unresolved
type: ByteOrder` in `cache_validator.spl`, then (once that's patched) an
`Effect` facade collision in `compiler.mir.__init__`. Full details and two
failed fix attempts: `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`.

**Consequence, stated plainly so no reader mistakes compiler-side progress for
user-facing hardening: every WP below (F3/F4 already landed, WP-F/F0/G in
flight) delivers ZERO user-facing safety until stage-3 self-host is
unblocked and a genuine self-hosted binary is deployed.** Landing WP-G's
enforcement in `src/compiler/55.borrow` changes nothing for anyone running
`bin/simple` today. Unblocking stage-3 self-host is not itself a WP of this
plan (it's a separate, pre-existing tracked bug) — it is listed here as
priority #0 so agents sequence correctly: do not treat "the checker landed"
as "users are now protected."

Also corrected this round: an earlier draft of this plan implied borrow
enforcement might be structurally AOT-only. That is false — `borrow_check()`
has **three** call sites, all verified at HEAD: `driver_pipeline_execution.spl:21`
(JIT), `driver_orchestration.spl:238` (VHDL-only), `driver_aot_pipeline.spl:97`
(AOT; skipped when `SIMPLE_BOOTSTRAP=1` and `SIMPLE_BOOTSTRAP_STAGE4!=1`).
`lower_to_mir()` (`driver_pipeline_lowering.spl:148`) is shared by all three,
so MIR — and therefore ownership enforcement — is available to JIT too, not
AOT-only. The modes that genuinely skip enforcement by construction (per the
dispatcher, `driver_orchestration.spl:176-198`) are `check` (returns after HIR
typecheck, before MIR), `interpret` (interprets HIR directly, no MIR phase),
`sdn`, and `smf_exec`. Method note: count call sites by grepping the CALL
site (`grep -rn '\.borrow_check()'`), not a keyword inside a file you already
suspect.

## Status as of 2026-08-07 (read before picking a WP — avoids redoing landed work)

- **WP-E, WP-H, WP-J now confirmed landed on `origin/main`** (2026-08-07,
  later pass). WP-E (MIR drop edges, `794bbf6642f`) and WP-H (`sffi_gen`
  wrapper emitter, `51e08eb7ead`) were already correctly pushed. WP-J was
  NOT: its `Image`/`FileLock` wrapper classes existed only in two local
  commits that were never pushed, while a separate already-pushed commit
  (`7868b6ab6e2`) had landed a spec fix whose `use` imports referenced those
  classes — so `origin/main` briefly had a spec importing symbols that did
  not exist anywhere in the tree. Fixed by landing the real wrapper classes
  scoped to their 3 actual files (`35889a86f4f`); re-verified with real spec
  runs, not file presence alone — `image_sffi_resource_wrapper_spec.spl`
  9/9, `file_lock_resource_wrapper_spec.spl` 6/6. Full account:
  `doc/00_llm_process/feature_expert/resource_ownership/skill.md`'s WP-J row.
  Lesson: a subagent's own "landed" self-report and even a locally-committed
  git history are not proof of presence on `origin/main` — always verify
  against fetched origin content directly.
- **LANDED — WP-F progress (use-detection half):** `src/compiler/55.borrow/borrow_check/mod.spl`
  gained a `case Call(dest, func, args)` arm in `analyze_instruction` plus a
  `me record_operand_use(op, nll, point)` helper. Call arguments previously
  rode as bare `MirOperand`s producing no use-fact at all, so `f(x)` after
  moving `x` went unreported while the same misuse via a let-binding was
  caught. Verified by isolation probe (disabling it alone re-broke the
  end-to-end case) and lint-clean. New spec
  `test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl` drives real
  source text through parse -> HIR -> MIR -> borrow check, 4/4 passed.
- **LANDED — WP-F progress (move-emission half):** an iso-typed call
  **argument** now emits a real MIR `Move` — a `case HirTypeKind.Isolated(_):`
  arm in `lower_call`, `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`.
  Spec `test/01_unit/compiler/borrow/iso_move_sites_spec.spl`, 2/2. This and
  the item above are INDEPENDENT layers — one is move-EMISSION, the other is
  use-DETECTION; neither substitutes for the other, and WP-F is not done
  until the remaining sites in F7 below (return, reassignment, field store,
  collection store) also emit moves.
- **REVERTED, reason recorded — do not redo without unblocking first:** the
  WP-F0 iso-struct-binding TODO (`50.mir/mir_lowering_stmts.spl:664-672`) was
  implemented and then reverted because the branch is **unreachable**:
  `find_local_hir_type(x) == Isolated` and `struct_value_syms.get(x) != nil`
  can never co-occur for the same local. Cause:
  `_MirLowering/function_lowering.spl:206` (records `Isolated`) and `:239`
  (sets `struct_value_syms`) match mutually-exclusive variants of the same
  `param.type_.kind` (`Isolated(_)` vs `Named(_,_)`). **Unblock condition:**
  `:239` must unwrap `Isolated` before its `Named` check; only then does the
  original WP-F0 TODO fix become reachable and worth re-landing. The TODO was
  correctly left in place, not converted to a NOTE.
- **ALREADY DONE — WP-P is closed:** `iso T` / `mut T` parse in parameter
  position (landed by a prior session, "LANE ISO2",
  `10.frontend/core/parser.spl:506-534`). Verified by sabotage probe, not
  assumption. Caveat: `mut`'s downstream HIR consumer is still intentionally
  deferred to the `Infer` catch-all — that remains open, tracked under WP-C.
- **New tracked gap, supersedes/refines WP-F's file list:** four transfer
  sites still silently copy instead of moving an iso value — return value
  (double gap: lowering never emits `Move` before `Ret`, and the checker had
  no terminator arm — being fixed now); reassignment to an existing var
  (`mir_lowering_stmts.spl:1039`); struct field store (`:1147`); and the
  collection stores, which are runtime CALLS, not a `Store`-instruction family
  — `arr[i]=v` / `d[k]=v` in the `Index` arm of `lower_assign`
  (`mir_lowering_stmts.spl:1139`, `rt_array_set`/`rt_dict_set` via
  `mir_operand_copy`), and `list.push(x)`
  (`_MirLoweringExpr/method_calls_literals.spl:874`, `rt_array_push`). Tracked
  in `doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`.

## Dependency graph

**Grammar landing alone hardens nothing — the architecture doc already says
wrapper generation is insufficient on its own. The safety-delivering chain is
WP-P -> iso-struct move fix -> WP-F (move sites) -> the `resource` surface.
Do not read "grammar landed" as "resources are safe."**

```
WP-P (parser: iso/mut in param position — HIGHEST PRIORITY, serial, first)
  └─> WP-0 (serial)
        └─> WP-A  WP-B  WP-D  WP-F0  WP-F   (parallel wave 1; WP-F0 = iso-struct move fix, WP-F = move sites)
              └─> WP-C ──> WP-E ──> WP-G  (serial chain: HIR -> MIR drop -> borrow)
                             WP-I         (interp parity; after WP-C)
        WP-H (sffi_gen adapters; after WP-A + WP-D)
        WP-J (pilot migration; after WP-E + WP-H + WP-I)
        WP-K (with-form sugar; after WP-J; optional/Phase 2)
```

**WP-P is now DONE (verified 2026-08-07, see Status section above)** — `iso`/
`mut` parse in parameter position, so the HIR-Isolated -> MIR-Move -> NLL
pipeline that `resource` depends on is reachable from real source, not just
hand-built-HIR specs. The paragraph below is kept for historical context on
why WP-P was gating everything. Wave 1 (after WP-0) runs 4 agents in
parallel; nothing in wave 1 shares files.

<details><summary>Historical: why WP-P blocked everything (resolved)</summary>

Until WP-P landed, `iso`/`mut` were unreachable from real parameter-position
source (`fn take(a: iso i64) -> i64:` failed to parse —
`doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`), so
the entire HIR-Isolated -> MIR-Move -> NLL pipeline that `resource` depends on
was untestable outside hand-built-HIR specs.

</details>

## WP-P — Parser: `iso`/`mut` in parameter position — DONE (verified 2026-08-07)
- **Status: closed.** `iso T` / `mut T` now parse in parameter position
  (landed by a prior session, "LANE ISO2", `10.frontend/core/parser.spl:506-534`).
  Verified by sabotage probe, not assumption — do not re-open or redo.
- Bug (now resolved): `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`.
  `fn take(a: iso i64) -> i64:` used to fail with `expected ), got Ident
  'i64'`; it parses now.
- **Caveat, left open:** `mut`'s downstream HIR consumer is still
  intentionally deferred to the `Infer` catch-all — that gap is real work,
  tracked under WP-C, not a reason to consider WP-P incomplete.
- Original acceptance criteria (retained for reference): `fn take(a: iso
  i64) -> i64:` and `fn borrow(a: mut Data)` parse; `iso_move_pipeline_spec.spl`
  stays 3/3.

## WP-0 — Skeleton + shared decisions (serial, Sonnet, ~1 session; after WP-P)
Land the choke-point edits every other WP depends on, so later agents never
touch shared files concurrently.
- `src/compiler/10.frontend/core/tokens.spl`: `resource` must be recognized
  as a **contextual/soft keyword, declaration-position-only** — NOT a hard
  `TOK_KW_RESOURCE` reserved word. `resource` is already used as an
  identifier in 115 places across `src/`, including the compiler's own
  source (`85.mdsoc/security.spl:257` `var resource = ""`,
  `85.mdsoc/weaving/join_point_kind.spl:10`
  `SecurityGate(capability: text, resource: text)`,
  `src/app/interpreter/control/control/context.spl:83`,
  `src/lib/nogc_sync_mut/security/types.spl:14`). A hard keyword breaks the
  compiler's own rebuild. Give it the same soft-keyword treatment already
  planned for `with` — recognized only when it appears where a declaration
  can start, not added to the general identifier-vs-keyword table. Highest
  token constant in use today is 221; the new token is 222.
- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl`: add
  `decl_resource_def(name, attrs_span, span_id)` ctor (fields per design §1).
  Follow the `DECL_ENUM` pattern: const range is 1..17, so this is 18; the
  ctor must write the tag both via `decl_alloc` AND as the literal-string
  non-arena path (`decl_nodes.spl:650` does this twice for `DECL_ENUM` — miss
  either and the decl silently misbehaves in one path).
- **Answered, no further investigation needed:** the live parser copy is
  `_ParserDecls/enum_module_body.spl` (re-exported by
  `core/parser_decls.spl:8`); `parser_decls_types.spl` is the dead twin and
  self-documents this at its own lines 138-141.
- Full wire-point checklist for the new decl kind (traced from `DECL_ENUM`,
  also recorded in the architecture doc §5.1): `core/__init__.spl:233`
  (export); `_ParserDecls/enum_module_body.spl`;
  `_ParserDecls/fn_struct_decls.spl`;
  `_ParserDecls/bitfield_aop_arch_decls.spl`;
  `core/compiler/c_codegen.spl:91,263`; `core/interpreter/eval_decls.spl:79,240`;
  `core/interpreter/eval_builtins.spl:147`;
  `core/interpreter/module_loader_core.spl:54,295`; `core/ast_clone.spl:25`;
  `35.semantics/lint/match_exhaustiveness.spl:54,112`;
  `70.backend/backend/compile_c_entry.spl:484`;
  `80.driver/shb/shb_extractor.spl:22,56`. **Trap:**
  `module_loader_core.spl:54` **redeclares** `val DECL_ENUM = 8` locally
  instead of importing it — the new decl kind constant must be added there
  separately or it silently misbehaves.
- Verify `resource` does not appear in `dangerous_keywords.spl` policy.
- **Accept:** `bin/simple build` green; a `resource Foo` source produces a
  parse error mentioning the new decl form (not "unknown identifier"); a
  file using `resource` as a plain identifier (e.g.
  `var resource = "x"`, mirroring `85.mdsoc/security.spl:257`) still parses
  and compiles unchanged.

## WP-A — Parser: `resource` decl + `@sffi` consumption (Sonnet; after WP-0)
- Files: `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`
  (confirmed live copy — see WP-0), dispatch arms (both
  sites, cf. `enum_module_body.spl:275,424`), `parser_extensions.spl` (no
  change expected — reuse `parse_attributes()`),
  `90.tools/fix/rules/impl_/lint_annotation.spl:14-23` (+`sffi`).
- Task: parse `@sffi(...) resource Name` per design §1; pre-register the name
  via `named_type_register` (see the TYPE_VOID warning at
  `enum_module_body.spl:68-84`); validate `@sffi` keys, fail-closed on
  unknown keys. `resource` is recognized ONLY at declaration-start position
  (contextual/soft keyword, per WP-0) — never as a general reserved word.
- **Accept:** parser spec `test/compiler/frontend/resource_decl_spec.spl`
  (from `.claude/templates/spipe_template.spl`): valid decl parses; missing
  `prefix:` errors; unknown key errors; **`resource` MUST remain usable as an
  ordinary identifier everywhere except declaration-start position** — add a
  regression case using `resource` as a variable/field name (mirroring
  `85.mdsoc/security.spl:257` and `85.mdsoc/weaving/join_point_kind.spl:10`)
  and confirm it still compiles unchanged. A hard-keyword implementation is a
  FAILING outcome for this WP, not an acceptable simplification — it breaks
  115 existing identifier uses including the compiler's own source.

## WP-B — Type sigils: `*T` / `@T` / `-T` (Sonnet — bridge work is fiddly)
- Files: `10.frontend/parser_types_expr.spl` (TypeKind: add `Shared(Type)`,
  `Weak(Type)`; `Atomic` exists at :47; append-only — discriminants are
  load-bearing), `10.frontend/core/parser.spl:468-530`
  (`parser_parse_type_impl`, follow the `iso` precedent),
  `10.frontend/core/types.spl` (new `TYPE_SHARED_BASE`/`TYPE_WEAK_BASE`
  ranges; wire `TYPE_ATOMIC` if missing), `_FlatAstBridge/convert_nodes.spl`
  (the known half-finish point — Pointer died here; every new kind needs its
  `convert_flat_type` case).
- Task: parse the sigils into TypeKind; semantic enforcement is NOT this WP —
  unknown-on-non-resource types may error later (WP-C/E).
- **Accept:** type-parse spec: `*File`, `@File`, `-File`, `mut *Data`, `~@Data`
  round-trip through the flat bridge (assert converted kind, not just no-crash).

## WP-C — HIR lowering + resource metadata (Sonnet; after WP-A/B)
- Files: `20.hir/hir_lowering/_Items/` (new item lowering),
  `20.hir` type tables; `30.types` move-only marking.
- Task: lower `resource` decl to a HIR item carrying
  {handle_type, invalid, retain, release, sharing, thread_safe}; mark the
  type affine/move-only; expose metadata query for later layers.
- **Accept:** HIR dump spec shows the item + metadata; assigning a resource
  twice type-checks as move (no error yet — enforcement is WP-F/E).

## WP-D — Convention inference engine (Haiku-capable; pure logic, no compiler wiring)
- Files: new `src/compiler/35.semantics/resource_families.spl` (or
  `90.tools/sffi_gen/family_infer.spl` — standalone module, no deps on WP-A).
- Task: given a family prefix + list of extern signatures, classify per design
  §4 tables; return classifications or fail-closed diagnostics (ambiguous
  destructor, multi-receiver, handle-returning fn, no-release).
- **Accept:** unit spec with the `rt_file_*` example mapping from design §4 +
  one spec per fail-closed rule. Pure-function tests; interpreter-only OK.

## WP-E — MIR drop edges + consuming close (Sonnet; after WP-C)
- Files: `50.mir/_MirLowering/function_lowering.spl` + siblings; may reuse
  `defer`/`errdefer` lowering (`parser_stmts.spl:509-526` produces the stmts;
  find their MIR path first — they're parsed but unadopted, so the lowering
  may be missing: if so, implement it here, it's the same machinery).
- Task: emit drop edges for owned resources on scope exit, early return, `?`;
  `close()`/consuming methods lower to drop + state change; wire the builtin
  `Drop` trait (`25.traits/trait_validation.spl:94`) as the drop hook.
- **Accept:** spec: resource dropped exactly once on normal exit, early
  return, and `?` error path (count via a test extern that increments a
  counter on release). Run in BOTH `SIMPLE_EXECUTION_MODE=interpreter` and
  `jit`.

## WP-F0 — iso-struct move fix (Sonnet; after WP-P; independent of A-E)
- **Blocked — do not re-attempt until the unblock condition below is met.**
  This was implemented once (2026-08-06/07) and then reverted: the target
  branch (`find_local_hir_type(x) == Isolated` AND
  `struct_value_syms.get(x) != nil` both true for the same local) is
  **unreachable** as the code stands. Cause:
  `_MirLowering/function_lowering.spl:206` (records `Isolated`) and `:239`
  (sets `struct_value_syms`) match mutually-exclusive variants of the same
  `param.type_.kind` (`Isolated(_)` vs `Named(_,_)`) — a param can only ever
  take one path, so the TODO's target condition never co-occurs.
- **Unblock condition (do this first):** `function_lowering.spl:239` must
  unwrap `Isolated` before its `Named(_,_)` check, so an iso-typed struct
  param can still reach `struct_value_syms` registration. Only after that
  lands does the original TODO fix below become reachable.
- Files: `50.mir/mir_lowering_stmts.spl:664-672` (TODO: iso-typed struct
  bindings take the `maybe_copy_struct_value` path and still emit copy, not
  move). An iso struct is exactly the shape of a resource handle, so this is
  a direct blocker for the `resource` feature.
- Task (after unblock): route iso-typed struct bindings through the same
  move-emission path scalar iso bindings already use
  (`mir_lowering_stmts.spl:48,731-746`, LANE ISO1 2026-07-29).
- **Accept:** spec extending `iso_move_pipeline_spec.spl` with a struct-typed
  iso binding; sabotage-probe (break the routing, confirm RED, revert,
  confirm GREEN). The TODO must stay a TODO (implement or delete) — never
  convert it to a NOTE, per CLAUDE.md.

## WP-F — Borrow checker G1: move-site emission (Sonnet, hardest WP; after WP-P/WP-F0; independent of A-E) — IN PROGRESS, two pieces landed 2026-08-07
- **Correction to earlier framing:** forward propagation of moved-places is
  ALREADY FIXED (SF1, 2026-07-28) — `moved_now: [Place]`
  (`borrow_graph.spl:459`, documented `:444-458`) is the running union of
  moves so far, minus kill-on-reassign. Do not re-implement this.
- **Landed this round — do not redo:**
  - Use-detection for call args: `55.borrow/borrow_check/mod.spl` gained a
    `case Call(dest, func, args)` arm in `analyze_instruction` + a
    `me record_operand_use(op, nll, point)` helper. Spec
    `test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl`, 4/4,
    verified by isolation probe.
  - Move-emission for call arguments: `case HirTypeKind.Isolated(_):` arm in
    `lower_call`, `50.mir/_MirLoweringExpr/switch_operators_calls.spl`. Spec
    `test/01_unit/compiler/borrow/iso_move_sites_spec.spl`, 2/2. This is
    move-EMISSION; the use-detection item above is independent and both were
    needed — neither substitutes for the other.
- What still remains: `MirBuilder.emit_move` (`50.mir/mir_data.spl:353`)
  originally had exactly ONE call site in the entire compiler — the
  variable-to-variable let-binding at `50.mir/mir_lowering_stmts.spl:743` —
  and now has a second (call arguments, above). `borrow_graph.spl:455-458`
  still describes the general problem accurately: most transfer sites don't
  emit `Move` yet. Four sites remain open, verified 2026-08-06/07:
  - **Return value** — double gap: lowering never emits `Move` before `Ret`,
    AND the checker had no terminator arm (an agent is closing the checker
    half now — check current state before starting, to avoid collision).
  - **Reassignment** to an existing var — `mir_lowering_stmts.spl:1039`.
  - **Struct field store** — `mir_lowering_stmts.spl:1147`.
  - **Collection stores** — NOT a `Store`-instruction family, these are
    runtime CALLS: `arr[i]=v` / `d[k]=v` both in the `Index` arm of
    `lower_assign` (`mir_lowering_stmts.spl:1139`, via
    `rt_array_set`/`rt_dict_set` + `mir_operand_copy`), and `list.push(x)`
    (`_MirLoweringExpr/method_calls_literals.spl:874`, `rt_array_push`).
  Tracked in `doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`.
- Files: `50.mir` move-site emission across `mir_lowering_stmts.spl` and
  siblings for the four sites above;
  `55.borrow/borrow_check/borrow_graph.spl` only if the `moved_now`
  propagation needs extending for a new site shape — do not rewrite it.
  Audit ref: `doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md` G1.
- Task: add the missing move sites (return, reassignment, field store,
  collection store) so `moved_now` tracks all transfer points, not just
  let-bindings and call arguments. This fixes a pre-existing soundness gap
  and is REQUIRED for invariants 1-2.
- **Accept:** spec: use-after-move of a `~T`/iso value via return, via
  reassignment, via field store, and via collection store (`arr[i]=`,
  `d[k]=`, `.push()`) all error; existing `moved_now` propagation regression
  stays green; existing test suite stays green (`--no-borrow-check` still
  bypasses). Expect fallout: gate behind incremental rollout if >10 existing
  specs break, and file the breakage list rather than weakening the check.
- **Reminder (F2/#0 above):** none of this reaches a user until stage-3
  self-host is unblocked and a genuine self-hosted `bin/simple` is deployed.

## WP-G — Resource enforcement in 55.borrow (Sonnet; after WP-E + WP-F)
- Task: exactly-once release, use-after-consume errors, borrow pinning across
  extern calls (invariants 1-3, 6), `@R` gated on `thread_safe` (invariant 8),
  `*R` does not grant `mut` methods (invariant 7).
- **Accept:** one negative spec per invariant (compile-error assertions).

## WP-H — sffi_gen adapter generation (Haiku-capable; after WP-A + WP-D)
- Files: `90.tools/sffi_gen/` (new emitter consuming WP-D classifications).
- Task: generate the public wrapper module (acquire → `R?` via invalid
  sentinel; methods borrow; release → drop hook + consuming close). Raw
  `rt_*` stay private to the generated module.
- **Accept:** golden-file spec: `rt_file_*` family in → generated `.spl` out
  matches design §1 shape and compiles.

## WP-I — Interpreter parity (Sonnet; after WP-C, parallel with WP-E)
- Files: `95.interp/`.
- Task: interpreter implements resource decl, drop timing, consuming close
  identically to compiled path.
- **Accept:** WP-E's specs pass under `SIMPLE_EXECUTION_MODE=interpreter`.

## WP-J — Pilot migration (Haiku-capable; after WP-E/H/I)
- Files: `src/lib/nogc_sync_mut/io/image_sffi.spl` (→ `resource Image`),
  new `File` family binding against `src/lib/nogc_sync_mut/sffi/io.spl`.
  Bind ONLY against `sffi/` (the `ffi/` twins are stale debt — do not touch;
  the rename cleanup is a separate pre-existing task, not this feature).
- Task: replace `ImageData` handle-class boilerplate; keep old API as thin
  deprecated aliases for one release.
- **Accept:** existing image/file specs green; new resource-based specs green
  in both engines; no `_free` call sites remain in the migrated modules.

## WP-K — `with` scoped form (Phase 2, Sonnet; after WP-J)
- `with R.open(...)? as x:` desugars to ownership + nested scope, one generic
  implementation. Resolve the soft-keyword collision with class-header `with`
  positionally. **Accept:** spec: resource closed at block exit incl. error
  paths.

## Cross-cutting rules for every agent
- Tests: modern SSpec (template `.claude/templates/spipe_template.spl`;
  anti-patterns `doc/07_guide/infra/sspec_antipatterns.md`); `assert_true`/
  `assert_false` not `to_be_true`; sequential `bin/simple test <dir>` only
  (parallel runs corrupt the shared test DB); trust only the final
  `Results:` line.
- Bare `assert` is inert in specs — never use it as the oracle.
- `bin/simple lint <files>` before commit; `jj commit -m` + push per WP
  (`.claude/rules/vcs.md` guards apply).
- Do not edit `tokens.spl`, `decl_nodes.spl`, or `convert_nodes.spl` outside
  WP-0/WP-B — they are the contention hot spots.
- Any grammar form that fails to parse or forces a workaround: file a bug,
  don't normalize the workaround (CLAUDE.md rule).
- **The frontend feedback loop is cheap — proven, not assumed.** No bootstrap
  rebuild is needed to test `src/compiler/**/*.spl` edits: the test runner's
  interpreter loads compiler source modules directly, so changes take effect
  immediately under `bin/simple test`. Proven by sabotage probe: breaking
  `mir_hir_type_is_isolated` took `iso_move_pipeline_spec.spl` from
  `3 total, 3 passed` to `3 total, 2 passed, 1 failed` (exit 1); reverting
  restored 3/3. Use this exact loop and grep the verdict — lint noise floods
  the log, so never read the raw tail:
  ```
  timeout 900 bin/simple test <spec> --no-cache --no-cover-check > /tmp/out.log 2>&1; echo "EXIT=$?"
  grep -E "^Results:|SPEC FILE VERDICT|^PASS|^FAIL" /tmp/out.log | tail -5
  ```
- **Every agent MUST sabotage-probe its own change**: break it, confirm RED,
  revert, confirm GREEN. A test that cannot fail proves nothing.
- **Grammar landing alone hardens nothing.** Do not report a WP as "done" in
  a way that implies resources are now safe — only the WP-P -> WP-F0 -> WP-F
  chain delivers the move/use-after-move guarantees; grammar/attribute
  parsing (WP-0/A/B/D) is surface only. WP-P is done (2026-08-07); WP-F0 is
  blocked on its unblock condition; WP-F has two pieces landed and four
  transfer sites still open — see the Status section at the top of this plan.
- **Even the full WP-P -> WP-F0 -> WP-F -> resource chain hardens nothing
  for users until stage-3 self-host is unblocked** (priority #0, top of this
  plan) and a genuine self-hosted `bin/simple` is deployed — the Rust seed
  binary users run today has no borrow-check code at all.
