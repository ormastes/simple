# Research: Unified `resource` Ownership for Native and Foreign Resources

**Date:** 2026-08-06
**Status:** Research complete; see companion architecture/design/plan docs.
**Companions:**
- Architecture: `doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`
- Design: `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md`
- Plan: `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`
- **Downstream (2026-08-07):** `doc/01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md`
  — the aerospace/`space-a` hardening line. Its allocation-class analysis
  (`none` / `init_only` / `bounded_pool` / `unbounded` / `unknown`) and its
  steady-state sealing model build directly on the ownership/move work here;
  its `resource` lifecycle (`construct → initialize → seal → start → step →
  recover → shutdown`) is the consuming-drop story generalized to a whole
  program. Both share the same gate: no self-hosted binary reaches users.

## Verified state as of 2026-08-07 (second round, folded into 2026-08-06 findings below)

- **The real top blocker is not in this feature at all: no self-hosted
  `bin/simple` exists.** The deployed binary is the Rust seed
  (`grep -rln "borrow_check\|BorrowCheck" src/compiler_rust/driver/src/` — no
  hits), and stage-3 self-host is a known open blocker
  (`.claude/rules/bootstrap.md`, 2026-08-06; details:
  `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
  Every finding below about the compiler's own `src/compiler/**/*.spl` source
  is real and verified via the frontend test loop, but none of it is
  user-facing until stage-3 unblocks. See the plan's new #0 section.
- **`borrow_check()` has three call sites, not one — enforcement is not
  structurally AOT-only.** `driver_pipeline_execution.spl:21` (JIT),
  `driver_orchestration.spl:238` (VHDL-only), `driver_aot_pipeline.spl:97`
  (AOT, skipped under `SIMPLE_BOOTSTRAP=1`/`SIMPLE_BOOTSTRAP_STAGE4!=1`).
  `lower_to_mir()` (`driver_pipeline_lowering.spl:148`) is shared by all
  three, so MIR (and ownership enforcement) is available to JIT too. Modes
  that genuinely skip enforcement by construction:
  `check`/`interpret`/`sdn`/`smf_exec` (`driver_orchestration.spl:176-198`).
  This is a distinct fact from the `emit_move` one-caller finding below (§3.3)
  — that one is still accurate and unchanged; do not conflate the two.
- **WP-P (parser: `iso`/`mut` in parameter position) is done**, landed by a
  prior session ("LANE ISO2", `10.frontend/core/parser.spl:506-534`),
  verified by sabotage probe. This closes §3.3's previously-open parser gap
  below — read that section as historical/resolved context, not a current
  blocker.
- **Landed:** call-argument use-detection (`55.borrow/borrow_check/mod.spl`,
  `case Call(dest, func, args)` + `record_operand_use`, spec
  `iso_use_after_move_e2e_spec.spl` 4/4) and call-argument move-emission
  (`case HirTypeKind.Isolated(_):` in `lower_call`,
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl`, spec
  `iso_move_sites_spec.spl` 2/2) — independent layers, both needed.
- **Reverted with cause recorded:** the iso-struct-binding TODO fix
  (`mir_lowering_stmts.spl:664-672`) — the target branch is unreachable
  because `function_lowering.spl:206` and `:239` match mutually-exclusive
  variants of `param.type_.kind`. Unblock: `:239` must unwrap `Isolated`
  before its `Named` check.
- **Four transfer sites still emit copy, not move:** return (double gap —
  lowering + checker, checker half in progress), reassignment
  (`mir_lowering_stmts.spl:1039`), field store (`:1147`), and the collection
  stores which are runtime calls, not `Store` instructions — `arr[i]=`/`d[k]=`
  in the `Index` arm of `lower_assign` (`:1139`) and `list.push`
  (`_MirLoweringExpr/method_calls_literals.spl:874`). Tracked:
  `doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`.

## Verified state as of 2026-08-06

- **Move tracking (G1) is HALF fixed, not open.** SF1 (2026-07-28) added
  forward propagation: `moved_now: [Place]` at
  `src/compiler/55.borrow/borrow_check/borrow_graph.spl:459`, documented at
  `:444-458` as the running union of moves minus kill-on-reassign. What
  remains is move **sites**: `MirBuilder.emit_move`
  (`50.mir/mir_data.spl:353`) has exactly one caller in the whole compiler
  (`50.mir/mir_lowering_stmts.spl:743`, plain variable-to-variable let). See §3.3.
- **The real bottleneck is a parser gap**, not borrow-checker plumbing: `iso T`
  / `mut T` do not parse in parameter position
  (`doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`).
  Until this lands, the whole HIR-Isolated -> MIR-Move -> NLL pipeline is
  unreachable from real source — only hand-built-HIR specs exercise it.
- **LANE ISO1 (2026-07-29) already landed** foundational iso plumbing this
  proposal builds on: `HirTypeKind.Isolated(inner)` in
  `src/compiler/20.hir/hir_types.spl`, move/copy branching in
  `50.mir/mir_lowering_stmts.spl:48,731-746`, and iso-param HIR-type threading
  in `50.mir/_MirLowering/function_lowering.spl`. A live gap remains: iso
  **struct** bindings take the `maybe_copy_struct_value` path and still copy,
  not move (`mir_lowering_stmts.spl:664-672`, TODO).
- **The frontend feedback loop is cheap, proven by sabotage probe:** the test
  runner's interpreter loads `src/compiler/**/*.spl` source directly, so
  compiler edits take effect under `bin/simple test` with no bootstrap
  rebuild. See §3.3 and the plan's cross-cutting rules.

## 1. Problem

Simple's SFFI exposes foreign objects as raw `i64` handles requiring a
manually-paired `_free`/`_close` call (`doc/07_guide/platform/ffi/sffi.md:344`).
~250 distinct `_free`/`_close`/`_destroy`/`_release` externs exist in the tree.
Meanwhile the memory design (`doc/05_design/language/misc/memory.md:15-41`)
already defines unique (`&T`), shared RC (`*T`), atomic RC (`@T`), weak (`-T`),
and isolated/move (`~T`) ownership forms — but none of these apply to SFFI
handles, and (see §4) most are not even parsed yet.

**Thesis (confirmed by this research):** callers should distinguish
*ownership semantics*, not whether a resource is native or foreign. One
nominal declaration kind — `resource File` — should cover files, sockets,
GPU buffers, DB connections, locks, and SFFI handles alike. Types such as
`Foreign<File>` or `SffiHandle<File>` encode implementation origin and must
not appear in public APIs.

## 2. External precedent

- **WASM Component Model (WIT):** `resource` = entity outside the component;
  plain type is an owned handle; borrowed handles explicitly distinguished;
  constructors return ownership, methods borrow their receiver.
- **Rust / C++ Core Guidelines:** unique deterministic ownership is the
  ordinary case (`Drop`, RAII); shared RC (`Rc`/`shared_ptr`) only when
  multiple owners are actually needed.
- **Swift noncopyable types:** file descriptor as the motivating example —
  unique ownership, automatic `deinit`, borrow/exclusive/consume operations,
  no exposure of C origin.
- **Objective-C ARC / Core Foundation:** ownership inferred from *name
  families* (`new`/`copy`/`init`, `Create`/`Copy`), with explicit attributes
  overriding irregular APIs. Strongest precedent for convention-over-
  configuration binding.
- **.NET SafeHandle:** P/Invoke pins the handle alive for the duration of a
  foreign call, preventing close/recycle mid-call; supports owned and
  externally-owned handles. Precedent for borrow-pinning at SFFI calls.
- **Linear Haskell / Oxide:** integrate linearity with ordinary datatypes
  rather than minting separate "linear versions" of every type; ownership and
  borrowing via substructural typing.

## 3. Current state of the repo (measured 2026-08-06)

### 3.1 SFFI
- `extern fn` decls are flat, typed, no `unsafe` block:
  `src/lib/nogc_sync_mut/sffi/io.spl:10` `extern fn rt_file_exists(path: text) -> bool`.
- Naming: `rt_<family>_<verb>` (`rt_file_`, `rt_env_`, `rt_cuda_`, ...).
  Non-`rt_` externs also exist (`path_join`, `rc_box_init`); interpreter
  internals use `__rt_`.
- Cleanest wrapper exemplar: `src/lib/nogc_sync_mut/io/image_sffi.spl:10-45` —
  `rt_image_load -> i64`, `rt_image_free(handle)`, `class ImageData { handle: i64 }`,
  manual `is_valid()` (`handle > 0`). This is exactly the boilerplate
  `resource` replaces.
- Invalid sentinels are inconsistent in practice: `0` per
  `.claude/memory/ref_sffi.md:41`, `> 0` validity in image_sffi. A `resource`
  declaration must carry the sentinel as metadata.
- **Duplicate-tree debt:** the `ffi`→`sffi` rename left live divergent twins
  (`src/lib/nogc_sync_mut/ffi/` 24 files vs `sffi/` 23 files, differing
  content, 110 vs 138 importers; same pattern in `src/app/io/*_ffi/_sffi`).
  `sffi/` is canonical; the twins are cleanup debt, tracked in the plan.
- **Registration is multi-backend:** adding an extern touches
  `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`,
  `codegen/cranelift_sffi.rs`, `codegen/interpreter_extern/`, and
  `src/compiler/70.backend/sffi.spl` — drift is a live bug
  (`doc/08_tracking/bug/cranelift_seed_missing_sffi_externs_2026-07-16.md`).
- `sffi_gen` (`src/compiler/90.tools/sffi_gen/`, CLI `simple ffi-gen`)
  already consumes `@Lib` metadata — but via its **own text parser**
  (`parser.spl:106-115`), not the compiler frontend.

### 3.2 Ownership sigils: designed, mostly unimplemented
- Design table `doc/05_design/language/misc/memory.md:15-41`:
  `T` GC ref · `&T` unique RAII · `*T` shared Rc (COW, not thread-safe) ·
  `@T` atomic Arc · `-T` weak · `+T` pool handle · capabilities `mut`/`iso`(`~T`).
- Frontend reality: `parser_parse_type_impl`
  (`src/compiler/10.frontend/core/parser.spl:468-530`) parses **only `iso`**.
  `TypeKind.Pointer(Type, bool)` (`parser_types_expr.spl:54`) means **raw
  pointer**, constructed only at `_FlatAstBridge/convert_nodes.spl:421`;
  `TYPE_POINTER_BASE=8000` has zero producers. No `Weak` variant exists.
- **`*T` collision resolution:** the memory-design meaning (shared RC) wins for
  surface syntax; raw pointers get an explicit SFFI-internal spelling
  (`raw<T>`). Rationale: memory.md is the committed language design, the raw
  `Pointer` kind never shipped to users, and foreign resources must share the
  native ownership notation (decision recorded in the architecture doc, §4).

### 3.3 Move/borrow/drop enforcement
- NLL borrow checker exists and runs **on by default**
  (`src/compiler/55.borrow/borrow_check/`, wired in
  `80.driver/driver_pipeline_passes.spl:11-12`; bypass `--no-borrow-check`).
- Gap **G1** in the safety audit
  (`doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md:156-183`)
  is **half fixed**, not open. The SF1 fix (2026-07-28) added forward
  propagation of moves: `moved_now: [Place]`
  (`borrow_graph.spl:459`, documented `:444-458`) is "the running union of all
  moves recorded so far... minus places revived by a later reassignment
  (kill-on-reassign)". What remains is the other half — **move sites**:
  `MirBuilder.emit_move` (`50.mir/mir_data.spl:353`) has exactly ONE call site
  in the entire compiler — the variable-to-variable let-binding at
  `50.mir/mir_lowering_stmts.spl:743`. `borrow_graph.spl:455-458` states it
  plainly: "Move instructions only enter MIR from explicit move sites, which
  Simple's surface language does not produce today." So use-after-move stays
  undetectable in practice not because tracking is broken, but because almost
  nothing emits a `Move` instruction to track (no call-arg moves, no return
  moves, no reassignment/field/collection-store moves).
- **RESOLVED 2026-08-07 (was open as of 2026-08-06):** `iso T` / `mut T` now
  parse in parameter position (`10.frontend/core/parser.spl:506-534`, "LANE
  ISO2", verified by sabotage probe). Originally: `fn take(a: iso i64) ->
  i64:` failed with `expected ), got Ident 'i64'` —
  `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`.
  The ownership pipeline that DOES exist (HIR `Isolated` -> MIR `Move` -> NLL
  check — see LANE ISO1 below) is now reachable from real source code, not
  only from specs that hand-build HIR.
- **LANE ISO1 (2026-07-29) already landed** and is foundation this proposal
  builds on, not something to re-propose: `HirTypeKind.Isolated(inner)` in
  `src/compiler/20.hir/hir_types.spl` (iso T carried through HIR instead of
  collapsing to `Infer`); `mir_hir_type_is_isolated` + emit_move/emit_copy
  branch at `50.mir/mir_lowering_stmts.spl:48,731-746`; iso-param HIR-type
  threading via `remember_local_hir_type` in
  `50.mir/_MirLowering/function_lowering.spl`. Verified via
  `test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl`.
  There is a live, explicit gap next to it: iso-typed **struct** bindings take
  the `maybe_copy_struct_value` path and still emit copy, not move — an
  unimplemented TODO at `mir_lowering_stmts.spl:664-672`. An iso struct is
  exactly the shape of a resource handle, so this is a direct blocker for
  `resource` and should be its own work package.
- A `Drop` trait exists as a builtin (`25.traits/trait_validation.spl:94,127-129`)
  with **zero consumers** downstream. No destructor lowering.
- `defer`/`errdefer` are fully parsed
  (`10.frontend/core/parser_stmts.spl:509-526`) but have zero uses in
  `src/lib` — parsed-but-unadopted cleanup machinery `resource` can lower onto.
- Consequence: **wrapper generation alone cannot deliver the safety
  invariants.** The parser gap (`iso`/`mut` in param position) blocks the
  pipeline from being reachable at all; the missing move sites block move
  detection even once reachable; both must close, and `resource` must lower
  to real MIR ownership states and drop edges (plan WP-P, then the iso-struct
  move fix, then WP-F, ahead of the `resource` declaration surface itself).
- **Feedback loop is cheap — proven, not assumed.** The test runner's
  interpreter loads `src/compiler/**/*.spl` modules directly, so edits to
  compiler source take effect immediately under `bin/simple test`, no
  bootstrap rebuild required for iteration. Proven by sabotage probe:
  breaking `mir_hir_type_is_isolated` took
  `iso_move_pipeline_spec.spl` from `3 total, 3 passed` to
  `3 total, 2 passed, 1 failed` (exit 1); reverting restored 3/3. Loop:
  ```
  timeout 900 bin/simple test <spec> --no-cache --no-cover-check > /tmp/out.log 2>&1; echo "EXIT=$?"
  grep -E "^Results:|SPEC FILE VERDICT|^PASS|^FAIL" /tmp/out.log | tail -5
  ```
  Output is flooded with lint warnings — grep for the verdict, never read the
  tail. `--no-cache --no-cover-check` avoids the shared-manifest race;
  directory-level `simple test <dir>` runs must be sequential (parallel runs
  corrupt the shared test DB). Every agent should sabotage-probe its own
  change (break it, confirm RED, revert, confirm GREEN) — a test that cannot
  fail proves nothing.

### 3.4 Grammar headroom
- `resource`, `drop`, `using`, `scope` are **not reserved**
  (`src/compiler/10.frontend/core/tokens.spl`, 242 `TOK_KW_*`). `with` is not
  in the token table either, yet the syntax quick reference documents
  `with X as f:` / `async with` (`syntax_quick_reference.md:901-910,1222`) and
  `class C with Trait:` composition — `with` is doc-overloaded and must be
  treated as a soft/contextual keyword (discrepancy flagged; architecture §6).
- **`resource` MUST be a contextual/soft keyword — it is already used as an
  identifier in 115 places across `src/`**, including the compiler's own
  source: `src/compiler/85.mdsoc/security.spl:257` (`var resource = ""`),
  `src/compiler/85.mdsoc/weaving/join_point_kind.spl:10`
  (`SecurityGate(capability: text, resource: text)`),
  `src/app/interpreter/control/control/context.spl:83`,
  `src/lib/nogc_sync_mut/security/types.spl:14`, and many more. A hard
  keyword would break the compiler's own rebuild. Recognition must be
  declaration-position-only — the same treatment already planned for `with`.
- Attribute syntax `@name(args)` is fully supported by the frontend
  (`parser_extensions.spl:20-38`); known-attribute lint list at
  `90.tools/fix/rules/impl_/lint_annotation.spl:14-23`. `@sffi(...)` fits.
- A library `Resource` **trait** (close/is_open/resource_name) exists
  (`syntax_quick_reference.md:1183-1195`) — the nominal `resource` decl
  subsumes it; migration noted in the plan.
- Prior art in-tree:
  `doc/01_research/language/modules/resource_cleanup_patterns.md`,
  `doc/05_design/language/syntax/baremetal_async_resources_v0.3.md`,
  `doc/03_plan/language/net_shared_dma_ownership.md`.

## 4. Conclusions

1. **The proposal is additive and well-aligned.** Plain `R` means ownership
   *only when `R` was declared as a `resource`*; `class`/`struct`/GC semantics
   unchanged. No global reinterpretation of `T`.
2. **The missing bridge is nominal.** Simple already has (on paper) every
   ownership form the proposal needs; what's missing is a declaration kind
   that ties a handle + release contract to those forms.
3. **Of the four gaps originally identified, one is now closed (2026-08-07)
   and the compiler-side gaps that remain still deliver nothing to users
   until stage-3 self-host unblocks (see the new 2026-08-07 section above):**
   (a) **RESOLVED — `iso`/`mut` now parse in parameter position**
   (`doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`,
   closed by "LANE ISO2");
   (b) ownership-sigil parsing (`*T`/`@T`/`-T` — only `iso` parses at all,
   and only outside parameter position) — still open;
   (c) drop lowering (Drop trait has no consumers) — still open;
   (d) borrow-checker move **sites** — partially closed: call-argument
   use-detection and move-emission both landed 2026-08-07; return,
   reassignment, field store, and collection store remain open (tracked in
   `doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`);
   the related iso-struct-copy TODO at `mir_lowering_stmts.spl:664-672` was
   attempted and reverted as unreachable — see unblock condition above.
4. **Convention inference is viable but must be fail-closed and scoped** to a
   declared family (`@sffi(prefix: "rt_file")`) — never a global `rt_*` scan.
   ObjC method-families prove conventions work *only* with explicit overrides.
5. **Phasing:** Grammar A (attribute form) first — it reuses the existing
   attribute parser and keeps every current `extern fn` valid. Grammar B
   (`resource File from rt_file:`) is sugar for A. Grammar C (per-function
   attributes) is the escape hatch for irregular APIs.
