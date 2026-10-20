# No-GC Ownership Baseline and Migration Lint (WP-00 / WP-01)

**Date:** 2026-10-20
**Base:** `origin/release_phase3` at `2de687836d7`
**Plan:** `nogc_ownership_recovery_plan_2026-10-19.md` (same directory), §1–§3, §10, §12, §15
**Status:** source-reviewed and fixture-verified (plan §2.4). Nothing here enables a new
default. The lint is WARNING-only.

## 1. Which default exists today

| Question | Answer, with evidence |
|---|---|
| Is unique ownership the no-GC default for class instances? | **No.** Only `iso` values move. Every MIR `emit_move` call is gated on `local_hir_type_isolation_state(id) == 1` (`50.mir/mir_lowering_stmts.spl:1357,1488,1956`, `_MirLowering/function_lowering.spl:826`; classifier `mir_lowering_types.spl:952`). |
| What does a class assignment do? | It aliases. Classes keep reference semantics (`mir_lowering_stmts.spl:1335-1341`). Structs are copied on a place read (`maybe_copy_struct_value`). Arrays and dicts are COW values. |
| Is there a no-GC policy object? | `GcMode` (`00.common/gc_config.spl:22`) has `default_pointer_kind()` returning `"Unique"` for NoGc and `default_capability()` returning `"Isolated"` (:44-61). **Nothing outside that file calls either.** NoGc mode drives only family-import warnings (`35.semantics/gc_boundary_check.spl:315,338`) and the MIR effect flag (`50.mir/mir_effects.spl:84`). |
| Grammar | `iso T` (`10.frontend/core/parser.spl:838` → `TypeKind.Isolated`), `&T`/`&mut T` types (:756-767), `&x`/`&mut x` (`parser_types_expr.spl:830-831`), `*T`, `@T`, `-T`; `move` is a contextual keyword. `mut T` as a type capability is not implemented (parser comment :834-837). There is no `own`/`borrow`/`ref` keyword. |

Measured on the shipped binary. `bin/simple` resolves to
`bin/release/aarch64-unknown-linux-gnu/simple`, and it prints the Rust-seed banner.
A 20-line probe printed `class a.v=2` after `var b = a; b.v = 2`, so the class aliased.
It printed `struct p.v=1`, so the struct copied, and `arr xs.len=1`, so the array was COW.
It also printed `use after copy c.v=5 d.v=5`: a class "moved" by `val d = c` was still usable.

## 2. Which short-borrow boundaries are enforced

| Plan §3.2 row | Enforced today? | Where |
|---|---|---|
| Return a borrow | Partial. It fires only when the `Ref` temporary itself is returned ("borrow of `X` may still be active at return"). | `55.borrow/borrow_check/nll.spl:415-433`, `borrow_graph.spl:698-720` |
| Store a borrow in a field, global or container | **No** (stated limitation) | `borrow_graph.spl:705-707` |
| Capture in an escaping closure or task | **No.** There is no HIR spawn node. | `35.semantics/safety_checker_transfer.spl:15-30` |
| Hold across `await`/`yield`/device submission | **No** | there are no suspension hits in `55.borrow/borrow_check` |
| Move or drop while borrowed, conflicting borrows, use after move | Yes, for `iso` values on the MIR route | `nll.spl:282,293`, `borrow_graph.spl:489,499` |
| Parameter mutated without `mut` (E1047); collection mutated while iterated (E1048); transfer/share (E1049) | Yes (HIR) | `35.semantics/safety_checker*.spl` |

The NLL diagnostics carry no error codes.

## 3. Which routes run the checker

| Route | Ownership/borrow check |
|---|---|
| `compile` / JIT / AOT / LLVM IR / VHDL (self-hosted driver) | `borrow_check()` (`80.driver/driver_pipeline_passes.spl:15-24`) is on by default. It is skipped by `--no-borrow-check`. |
| **Bootstrap Stage 2/3** (`SIMPLE_BOOTSTRAP=1` without `SIMPLE_BOOTSTRAP_STAGE4=1`) | **Skipped.** See `80.driver/driver_aot_pipeline.spl:156` (`aot:flat_mir_passes:skipped`). The bootstrap closure has never been borrow-checked. |
| Self-hosted interpret (`interpret_pipeline`) | **Never.** `80.driver/driver.spl:102-120` calls only `interpret_hir_module`, and `driver_orchestration.spl:521-524` does not call `borrow_check()`. Bug `iso_borrow_check_unreachable_from_interpret_pipeline_2026-08-09` is still open. |
| Rust seed interpreter (`bin/simple` today) | There is no MIR borrow checker. The only check is a runtime check for `Value::Unique` in `let` (`interpreter/node_exec.rs:164-169`, error `USE_AFTER_FREE`). |

Consequence for plan §3.7: "ownership checking is mandatory on every admitted
route" is false today on three routes: bootstrap AOT, self-hosted interpret, and the
seed. Do not enable a stricter default until that is repaired (WP-02).

## 4. Migration lint (plan §3.8)

The rule is `nogc_ownership`, a single rule in the static lint table, at WARNING level in the Safety category.
- Checker: `src/compiler/35.semantics/lint/nogc_own/checker.spl`, with text helpers in `text_scan.spl`.
- Wrapper: `src/compiler/90.tools/lint/rules/nogc_ownership_rule.spl`.
- Spec: `test/01_unit/compiler/lint/nogc_own/nogc_ownership_lint_spec.spl`. It has 20 cases, with a positive and a negative per code. A sabotaged oracle made 2 cases fail, so the spec can go red.

| Code | Flags | Never flags |
|---|---|---|
| NOGC-OWN-001 | A class local handed to another place (`val b = a`, `b = a`, `x.f = a`, `d[k] = a`, `.push(a)`, `.append(a)`) and then used again on the same path, including after a conditional move | structs, arrays, text, scalars; `.clone()`; a transfer with no later use; mutually exclusive `elif`/`else`/match arms; a path ended by `return`/`break`/`continue`; reassignment before the use. Moves inside loops are skipped, not modelled. |
| NOGC-BOR-001 | `return p` or tail `p` for a class-typed parameter or the class receiver, or a class-typed field of either | `iso T` parameters; scalar fields; struct receivers |
| NOGC-BOR-002 | A borrowed parameter or receiver stored into a field or index slot, `.push`/`.append`/`.insert`, or a known class/struct constructor argument | reading it; storing a scalar read from it |
| NOGC-BOR-003 | A borrowed parameter or receiver referenced by a `\` lambda that is returned, stored, pushed, or handed to `spawn`/`thread_spawn`/`spawn_task`/`task_spawn`/`actor_spawn`/`go` | synchronous callbacks (`xs.map(\x: ...)`); spawned lambdas that do not reference the borrow |
| NOGC-BOR-004 | A borrowed parameter or receiver used after the first `await`/`yield` of the function | values copied out before the suspension |
| NOGC-ALIAS-001 | `val b = owner.f` / `owner.f[i]` / `param[i]` of class type, then mutated through `b` (field assignment, compound assignment, push/append/insert, or a call of a `me` method of its class) | owner-path mutation (`self.f.x = ...`); read-only locals |

A value is class-typed only when the lint can see it:
- a `C(...)` or `C.new(...)` constructor;
- a `: C` annotation;
- a parameter typed `C`, where `C` is a class declared in the file or in the repo-wide index that the blast-radius driver passes through `check_nogc_ownership_indexed`.

The index drops names that are also declared as a struct/enum/trait/union/type anywhere.
The in-editor rule sees only in-file classes, so its counts are a subset of the table below.

**nil outside `unsafe`.** There is no nil lint to reuse yet. The nilunsafe lane
(`work/nil-only-unsafe`, `75c294d70a2`) enforces only one MIR site
(`50.mir/_MirLoweringExpr/enum_constructor_payload.spl:239`), and only for enum
constructor payloads. This lane does not duplicate it. The heuristic count below
(`nil` tokens outside `unsafe:` blocks and `@unsafe` functions, ignoring comments and strings)
sizes that lane's work and is not a lint result.

## 5. Blast radius

The full scan ran on 2026-10-20 over 44,538 `.spl` files in `src/` and `test/` (vendor excluded).
It called `check_nogc_ownership_indexed` with a repo-wide index of 7,852 unambiguous class names and 11,098 struct names.
The run used four seed shards under `MemoryMax=8G`.
One shard was killed by the host CPU-spin guard at file 11,201 of 12,497, and its last 1,296 files were rerun.
The bootstrap closure is the 781-file import closure of `src/app/cli/bootstrap_main.spl`.
It was computed by resolving `use` statements, which is approximate, and 9 relative imports were unresolved.
The table lists buckets with at least 20 findings.

| Bucket | OWN-001 | BOR-001 | BOR-002 | BOR-003 | BOR-004 | ALIAS-001 | Total |
|---|---:|---:|---:|---:|---:|---:|---:|
| **bootstrap closure (781 files)** | 3 | 5 | 5 | 0 | 0 | 0 | **13** |
| **whole tree (src+test)** | 163 | 1213 | 1077 | 3 | 3 | 228 | **2687** |
| `src/compiler_rust` | 13 | 311 | 111 | 1 | 3 | 1 | 440 |
| `src/lib/gc_async_mut` | 43 | 120 | 95 | 0 | 0 | 71 | 329 |
| `src/lib/nogc_sync_mut` | 16 | 116 | 118 | 0 | 0 | 38 | 288 |
| `src/os` | 28 | 54 | 132 | 0 | 0 | 57 | 271 |
| `src/app/llm_caret` | 4 | 72 | 155 | 0 | 0 | 5 | 236 |
| `src/lib/nogc_async_mut` | 13 | 101 | 73 | 2 | 0 | 14 | 203 |
| `test/01_unit` | 8 | 82 | 55 | 0 | 0 | 12 | 157 |
| `src/lib/common` | 5 | 42 | 97 | 0 | 0 | 4 | 148 |
| `src/lib/skia` | 5 | 48 | 28 | 0 | 0 | 0 | 81 |
| `test/unit` | 1 | 40 | 24 | 0 | 0 | 1 | 66 |
| `src/app/office` | 2 | 30 | 6 | 0 | 0 | 0 | 38 |
| `src/compiler/90.tools` | 1 | 19 | 6 | 0 | 0 | 9 | 35 |
| `test/03_system` | 0 | 21 | 8 | 0 | 0 | 1 | 30 |
| `test/fixtures` | 4 | 20 | 3 | 0 | 0 | 0 | 27 |
| `src/compiler/30.types` | 0 | 0 | 27 | 0 | 0 | 0 | 27 |
| `src/lib/nogc_async_immut` | 0 | 25 | 0 | 0 | 0 | 0 | 25 |
| `src/app/mcp` | 1 | 9 | 7 | 0 | 0 | 5 | 22 |

The bootstrap closure had 14 findings before Step 3, then 13 after the first reorder fix.
The remaining 13 sites:

| Site | Code | Shape | Fix direction |
|---|---|---|---|
| `20.hir/hir_lowering/module_surface_registry.spl:260` | BOR-002 | `self.surfaces.push(surface)` stores a param | consume contract for the param |
| `20.hir/hir_lowering/types.spl:819,825` | BOR-002 | `lowering.module_surfaces = module_surfaces` | consume contract for the param |
| `25.traits/trait_solver.spl:504` | BOR-001 | getter returns `self.assoc_resolver` | short-borrow accessor / call-site use |
| `50.mir/hwir/mir_to_hwir.spl:52` | BOR-002 | `HwirLowerResult(module: module, ...)` | consume contract for the param |
| `80.driver/driver_source_pipeline_parsing.spl:844,1186` | OWN-001 | one owner stored in two fields (documented native `Option<class>` workaround) | one owner plus a handle/ID |
| `src/lib/log.spl:322` | OWN-001 | ring backend pushed to a global registry **and** returned | registry owns it; return the index handle (`self_ptr` already is one) |
| `nogc_async_mut/database/query.spl:110,115,126,132` | BOR-001 | builder `me` methods return `self` | consuming-receiver builder, or drop the return |
| `nogc_sync_mut/io/file_text_session.spl:159` | BOR-002 | `FileTextSession(_codec: codec)` | consume contract for the param |

**nil outside `unsafe` (heuristic, not a lint):** 5,339 tokens in 335 bootstrap-closure files.
54,861 tokens across the whole tree.


## 6. Gates before any default flips (plan §15.4 Stage B)

1. The NOGC-* count for the bootstrap closure is 0.
2. A diagnostic Stage 2 build of the closure passes in a separate output directory.
3. The checker runs on the bootstrap AOT and interpret routes (WP-02). Without this, a lint count of 0 is the only evidence.
4. The new semantics sit behind the semantic-version boundary (plan §3.8). Old unchecked artifacts are not reused.
5. Lint severity rises to Deny only for the converted scope.
