# Architecture: `resource` Declaration and Origin-Neutral Ownership

**Date:** 2026-08-06 (facts refreshed 2026-08-07)
**Status:** Proposed
**Research:** `doc/01_research/language/resource/resource_unified_ownership_research_2026-08-06.md`
**Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md`

> **2026-08-07 update:** the parser gap referenced throughout this doc
> (`iso`/`mut` not parsing in parameter position) is now **closed** — see the
> plan's Status section
> (`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`).
> Also, above every item in this doc: no self-hosted `bin/simple` exists yet
> (stage-3 self-host is an open, separately-tracked blocker), so none of this
> architecture reaches users until that lands — see the plan's #0 section.

## 1. Concept

A new nominal declaration kind:

```simple
@sffi(prefix: "rt_file", invalid: -1)
resource File
```

`resource R` declares an **affine owning value**: move-only, released exactly
once, deterministically, when its owning lifetime ends. Whether `R` wraps
native Simple state, an `i64` fd, a pointer, or a foreign RC object is
implementation/SFFI metadata — never part of the public type. There is no
`Foreign<R>`, `Native<R>`, or `SffiHandle<R>`.

## 2. User-facing type grammar (reuses memory.md sigils)

| Form | Meaning |
|------|---------|
| `R` | Unique owner; move-only; automatic deterministic release |
| borrowed param/receiver | Temporary access (existing borrow convention; methods borrow by default) |
| `mut R` | Exclusive temporary access (existing capability syntax) |
| `*R` | Shared, non-atomic RC owner |
| `@R` | Shared, atomic RC owner (requires thread-safety capability, §7) |
| `-R` | Weak reference |
| `R?` | Optional owned resource |
| `Result<R, E>` | Fallible acquisition |

**The one rule:** plain `R` means ownership only when `R` was declared as a
`resource`. `class T` / `struct T` / GC semantics are unchanged — additive,
not a reinterpretation of `T`.

```simple
val file = File.open("data.bin")?
val count = file.read(buffer)
# no close call needed; released exactly once at end of owning lifetime

file.close()      # consuming method — sugar for drop(move file)
# file unusable here: compile error, not an is_closed flag
```

## 3. Ownership/RC strategies (hidden behind the type)

1. **Unique direct** (default): raw handle + drop metadata. No RC allocation.
   Right default for files, sockets, command buffers, transactions, locks.
2. **Wrapper RC** (`sharing: wrapper`): `*R` allocates a Simple control block
   `{strong, weak, raw_handle, release_fn}`; the foreign runtime sees exactly
   one owning handle; release fires when the last `*R` dies. Works when the
   foreign API has no retain.
3. **Foreign RC** (`sharing: foreign`): copy of `*R` calls the declared
   `retain:` extern, drop calls `release:`. For GObject/CF/COM-style APIs.
4. **`sharing: auto`** (default): explicit or unambiguous retain/release pair
   → foreign RC; else wrapper RC. `sharing: none` prohibits `*R` entirely.
   Unique `R` remains the ordinary case; RC activates only when the program
   writes `*R`/`@R`.

## 4. Sigil collision — decision

`doc/05_design/language/misc/memory.md` assigns `*T` = shared Rc; the frontend
AST has `TypeKind.Pointer` (`*T` raw) — but that kind **never shipped**: not
parsed by `parser_parse_type_impl`, `TYPE_POINTER_BASE` has zero producers,
sole constructor is the flat-AST bridge (`convert_nodes.spl:421`).

**Decision: `*T` is shared ownership (memory.md wins). Raw pointers are
spelled `raw<T>`, legal only inside generated SFFI code or an explicit unsafe
boundary.** Foreign resources use the same ownership notation as native ones —
no second SFFI-only notation. `TypeKind.Pointer` is repurposed/renamed for
`raw<T>` in the same change so no dead meaning lingers.

## 5. Compiler placement (layer by layer)

| Layer | Change |
|-------|--------|
| `10.frontend` | `resource` MUST be recognized as a **contextual/soft keyword, declaration-position-only** — NOT a hard `TOK_KW_RESOURCE` reserved word. `resource` is already used as an identifier in 115 places across `src/`, including the compiler's own source (`85.mdsoc/security.spl:257` `var resource = ""`, `85.mdsoc/weaving/join_point_kind.spl:10` `SecurityGate(capability: text, resource: text)`); a hard keyword breaks the compiler's own rebuild. Same treatment already planned for `with` (§6). `parse_resource_decl()` in `_ParserDecls/` — **confirmed**: `enum_module_body.spl` is the live copy (re-exported by `core/parser_decls.spl:8`); `parser_decls_types.spl` is the dead twin and self-documents this at its own lines 138-141, so no further investigation is needed; pre-register name via `named_type_register` (see enum_module_body.spl:68-84 warning); `@sffi` consumed via existing `parse_attributes()`; sigil parsing `*T`/`@T`/`-T` in `parser_parse_type_impl` following the `iso` precedent; new `TypeKind` variants `Shared`/`Weak` + `TYPE_*_BASE` side-table ranges + `_FlatAstBridge/convert_nodes.spl` cases (the bridge is the known half-finish point — Pointer died there). **RESOLVED 2026-08-07 (was the highest-priority blocker):** `iso T`/`mut T` now parse in parameter position (`10.frontend/core/parser.spl:506-534`, "LANE ISO2") — the ownership pipeline this feature depends on is reachable from real source; original bug `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md` |
| `20.hir` | `resource` item lowering (`hir_lowering/_Items/`); resource metadata (handle repr, invalid sentinel, release/retain fns, sharing, thread_safe) carried on the HIR item |
| `25.traits`/`30.types` | resource types are move-only (affine); consuming methods; `Drop` trait finally gets its consumer |
| `35.semantics` | method-family inference + fail-closed diagnostics (design doc §4) |
| `50.mir` | ownership states + **drop edges** on scope exit / early return / `?` propagation; `close()` lowers to consuming drop; lowering may reuse the parsed-but-unadopted `defer`/`errdefer` machinery |
| `55.borrow` | enforce exactly-once release + use-after-move. **Depends on the remaining half of audit gap G1**: forward propagation of moves is already fixed (`moved_now` at `borrow_graph.spl:459`, SF1 2026-07-28); move-site emission is partially closed as of 2026-08-07 — call-argument use-detection (`borrow_check/mod.spl`, `case Call` arm) and call-argument move-emission (`switch_operators_calls.spl`, `case HirTypeKind.Isolated(_):`) both landed; `MirBuilder.emit_move` (`50.mir/mir_data.spl:353`) now has two callers (`mir_lowering_stmts.spl:743` and the call-arg site) but return/reassignment/field-store/collection-store sites remain open (`doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`). The parser gap that used to block this is RESOLVED (`iso`/`mut` parse in parameter position, 2026-08-07). Separately, note `borrow_check()` itself (the driver-level call, not `emit_move`) has three call sites — JIT, VHDL, AOT — enforcement is not structurally AOT-only |
| `70.backend` | lower handle repr per config (i64 default); borrow-pinning across SFFI calls (SafeHandle semantics); C-backend export wrappers |
| `90.tools/sffi_gen` | consume `@sffi` families, generate adapters (design doc) |
| `95.interp` | interpreter parity — mandatory; `run` (JIT) and `test` (interpreter) are different engines |

## 6. `with` scoped form

`with` is currently a **soft keyword**: not in the token table, but documented
for trait composition (`class C with Trait:`) and context-managers
(`with X as f:`). The resource `with` form is one generic desugar over
ownership + a nested scope — not per-library:

```simple
with File.open(path)? as file:
    file.read(buffer)
# file definitely closed here
```

Ship it as a later phase; plain ownership is already safe without it. The
trait-composition collision is resolved positionally (class-header `with` vs
statement-position `with`).

## 7. Thread safety

Atomic RC protects the control block, not the resource. `@R` is legal only
when the resource declares `thread_safe: true` (or `impl Share`); otherwise
`val x: @R = ...` is a compile error. Destruction affinity (`drop_on: main` /
`gpu` / `creating_thread`) is reserved config for UI/GPU/event-loop resources
— schema now, enforcement later.

## 8. Safety invariants (the feature is these, not the syntax)

1. Exactly-once release: live owned resource → moved or dropped exactly once.
2. Use-after-move is a compile error.
3. Borrow pinning: a borrowed resource stays live through the entire foreign
   call, including blocking calls.
4. No raw-handle escape outside generated SFFI code / explicit unsafe.
5. No GC-finalizer dependence; a finalizer is at most a leak backstop.
6. `close()` consumes even though spelled as a method.
7. `*R` does not grant exclusive (`mut`) methods.
8. `@R` requires the declared share capability (atomic count ≠ thread safety).
9. Borrowed returns cannot outlive their owner (`@resource_borrow(..., from:)`).
10. Foreign retention must be declared; a callee may not store a call-scoped
    borrow past return.

Per the safety audit (2026-07-28), the production path does not currently
enforce move/lifetime properties uniformly — so these invariants **require**
the MIR/borrow work (G1's remaining move-site half — partially closed
2026-08-07, four sites still open — plus drop edges); the upstream parser fix
(`iso`/`mut` in parameter position) is RESOLVED (2026-08-07). Wrapper
generation alone is still explicitly insufficient, and none of this reaches
users until stage-3 self-host unblocks (plan #0).

## 5.1 Full wire-point checklist for a new declaration kind

Traced from `DECL_ENUM` as the reference pattern (const range is 1..17, so a
new kind is 18): `_Ast/decl_nodes.spl:234` (const) and `:650` (ctor — note it
writes the tag TWICE, once via `decl_alloc` and once as a literal string
`"8"` in the non-arena path — both must change together); `core/__init__.spl:233`
(export); `_ParserDecls/enum_module_body.spl`; `_ParserDecls/fn_struct_decls.spl`;
`_ParserDecls/bitfield_aop_arch_decls.spl`; `core/compiler/c_codegen.spl:91,263`;
`core/interpreter/eval_decls.spl:79,240`; `core/interpreter/eval_builtins.spl:147`;
`core/interpreter/module_loader_core.spl:54,295`; `core/ast_clone.spl:25`;
`35.semantics/lint/match_exhaustiveness.spl:54,112`;
`70.backend/backend/compile_c_entry.spl:484`; `80.driver/shb/shb_extractor.spl:22,56`.

**Trap:** `module_loader_core.spl:54` **redeclares** `val DECL_ENUM = 8`
locally instead of importing the shared constant — a new decl kind must be
added there separately, or it silently misbehaves. Highest token constant
currently in use is 221, so the new resource-decl token is 222.

## 9. Phasing

- **Phase 1 — Grammar A:** `@sffi(...) resource File` attribute form. Additive;
  all existing `extern fn` stay valid; no ABI change.
- **Phase 2 — Grammar B:** `resource File from rt_file:` block sugar,
  desugaring to A (sugar only, no second semantic mechanism).
- **Phase 3 — Grammar C:** per-function explicit attributes
  (`@resource_acquire`, `@resource_method`, `@resource_retain`,
  `@resource_release`, `@resource_borrow`) for irregular C APIs; optional
  typed-SFFI surface (`extern fn image_load(path: text) -> Image?`).
