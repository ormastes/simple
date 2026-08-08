# M5 — strict interpreter mode (Miri-lite): insertion-point design

Predecessor: `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
(M5) and `doc/01_research/runtime/memory_analysis/memory_infra_gap_and_tools_2026-07-29.md`
§3. Builds on M1 attribution (`heap.rs` `note_attr_alloc`/`set_current_owner`)
and M2 (`doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md`),
which already splits page-guard sampling (malloc-backed) from arena
generation-harden (index-based) — M5 reuses that split. Sources read:
`value.rs`, `interpreter/{node_exec,expr/literals,block_exec}.rs`,
`interpreter_extern/ast_sffi.rs`, `runtime/src/value/heap.rs`,
`_AstExpr/nodes.spl` (all under `src/compiler_rust/compiler/src/` unless noted).

## 1. Gate: `SIMPLE_STRICT_MEM=1`, read once

Mirror `heap.rs:546-551` (`ATTR_ENABLED: OnceLock<bool>`) and
`nodes.spl:314-319` (`ast_gen_check_enabled`): one `OnceLock<bool>` in
`value.rs`, consulted at each call site below — no per-check env read, no
lock on the disabled path. A `strict_mem_enable()` twin (mirrors
`mem_attr_enable()`) lets fixtures/`--mem-infra=strict` (M3) enable it early.

## 2. Uninit-read trap: where Nil-vs-uninit is conflated today

**Finding**: there is no "uninitialized" state — only "bound to `Value::Nil`"
and "absent from `CowEnv`". `Node::Let` (`node_exec.rs:69`) only calls
`bind_pattern_value` inside `if let Some(value_expr) = &let_stmt.value`; a
`let` with no initializer executes nothing — no binding, no tombstone, no
sentinel. The name becomes indistinguishable from one never declared.

Reading it falls into `Expr::Identifier`'s cascade (`expr/literals.rs:256`):
`env.get(name)` misses, then it tries `functions`/`classes`/`enums`/
`MODULE_GLOBALS`/unit-registry before raising `E1001 UNDEFINED_VARIABLE`
(`literals.rs:346`). The hazard: if any enclosing scope, module global,
function, or class shares the uninitialized name, the read silently resolves
to that unrelated binding instead of erroring — a shadow-miss dressed as
"it worked." `CowEnv::get` (`value.rs:314`) has the same shape (overlay miss
→ tombstone check → base, no third state).

**Minimal separation**: no new `Value` variant (blast radius, see §5).
Instead, one gated `CowEnv` set: `uninit_names: HashSet<String>`. Under the
gate, `Node::Let` with `value == None` inserts the pattern name(s) (no
`overlay` entry — a plain read still falls through today's cascade). A
strict-only check at the top of `Expr::Identifier` (`literals.rs:256`, after
the `pass_todo`/`OptionVariant::None` cases): if
`strict_mem_enabled() && env.uninit_names.contains(name)`, raise
`E-STRICT-UNINIT` before the fallback cascade runs. `bind_pattern_value`
removes the name from `uninit_names` on first assignment (same removal point
`insert()` uses for `tombstones`, `value.rs:332`).

Scope is deliberately narrow: only `let` with a missing initializer — the
one declaration form the parser accepts without a value. Struct/class fields
and array elements are out (`Object`/`Array`/`FixedSizeArray` are always
built complete in one shot from a `Vec`/`HashMap` before becoming reachable
— no partial-construction window exists to detect).

## 3. Poison-on-free: what "free" means, and the real hazards

**Does not apply**: `Value` payloads are `Arc`/`Box`-owned; Rust's ownership
model frees them on last-drop and a stale reference is a compile error, not
a runtime hazard. Classic UAF on a `Value` is structurally impossible here —
no `unsafe`, no raw pointers.

**What does apply — stale-*state*, not stale-*memory*:**

1. **Stale `Arc<Env>` captures.** `Value::Lambda{env}`/`Value::Function{captured_env}`
   snapshot an `Arc<Env>` at creation. The `Arc` keeps it alive (no UAF), but
   frozen — a global mutated after capture is invisible unless refreshed via
   `refresh_bound_global` (`value.rs:590`)/`forward_globals`. Detectable
   under the gate: tag captures with a monotonic `capture_generation` (one
   `AtomicU64`, bumped on owner-crossing, reusing M1's `set_current_owner`
   signal). A strict-mode read through `global_bindings` whose generation
   predates the owner's current live generation, and isn't in
   `refreshed_globals`, logs a "possibly-stale global capture" note (both
   generations, both sites) — diagnostic, not a hard trap.
2. **Block-env write-back replay** (`block_exec.rs:166`, already fixed once):
   `copy_back_block_writes` copies only `dirty_names()`, not every shared
   key — copying everything once replayed a cloned block env's stale
   snapshot over values a deeper call had since written (a real regression
   this repo shipped and fixed). Strict mode asserts, at block exit, that
   `dirty_names()` only names entries actually present in the block env's
   overlay — a regression lock on the invariant that already broke once.
3. **Arena index reuse across the SFFI boundary** — see §4; same
   "container recycled, reference not invalidated" shape as UAF, on indices.

## 4. Provenance across the SFFI boundary

Two AST representations; only one has a gap. `interpreter_extern/ast_sffi.rs`
(Rust `simple_parser::ast::Expr`, exposed to Simple macros): thread-local
`HashMap<i64, Expr>` registries, handles from one `AtomicI64` counter
explicitly "monotonically increasing, never reused" (`ast_sffi.rs:23`).
Every accessor does `reg.get(&handle).ok_or_else(invalid_handle)` — a stale
handle is already a hard error. `clear_ast_sffi_registries()`
(`ast_sffi.rs:770`) wipes the maps but not the counter, so cleared handles
can never alias new ones. **Already provenance-safe; nothing to add.**

`_AstExpr/nodes.spl` (self-hosted compiler's parallel-array arena) *does*
recycle slot indices via a free-list; L6's `ast_gen_slot`/
`ast_generation_bump()`/`ast_gen_check_index()` (`nodes.spl:108,309,324`) is
diagnosis-only, gated `SIMPLE_AST_GEN_CHECK=1`, at a few probe sites, not the
read gate — M2 §4 already scoped promoting it under
`SIMPLE_AST_GEN_HARDEN=1`; M5 does not duplicate that. M5's addition: when a
`nodes.spl`-minted index crosses into an `interpreter_extern` SFFI call,
thread it as an `(idx, gen)` pair (M2's `NodeRef` shape) so a stale index
fails at the boundary, named, before Rust-side logic touches it — a thin
adapter over M2's mechanism, not new machinery.

## 5. What is NOT worth doing

- **Classic UAF on `Value`.** Structurally impossible (no `unsafe`, `Arc`/`Box` ownership) — the value is entirely in stale-*state* detection (§3).
- **A `Value::Uninit` variant.** Touches every exhaustive `match Value` arm
  across interpreter/SFFI/codegen for a state that exists between two
  adjacent statements in one narrow case; `uninit_names` gets equal
  detection power at near-zero blast radius.
- **Struct/array partial-init tracking.** No partial-construction window
  exists (§2) — a fixture can't be written for a state that can't occur.
- **Full Miri-style byte-level provenance** (pointer-int casts, alignment) —
  out of scope for a tree-walking `Value` interpreter with no raw memory
  model; that's M4/ASan territory.
- **A separate GC-tier dangling-survivor mechanism.** M2 §3/§5 already scope
  GC poison-on-sweep under the shared `SIMPLE_MEM_HARDEN` gate; strict mode
  implies harden's GC behavior rather than adding a parallel path.

## 6. Test plan (fixtures pass normally, trap under strict)

New `test/03_system/runtime/memory_analysis/`, SSpec, `SIMPLE_STRICT_MEM=1`
per-fixture (never globally):

1. `strict_uninit_read_spec.spl` — `let x: i32` unread-before-write. Normal:
   `E1001` or a shadow-miss. Strict: `E-STRICT-UNINIT` naming `x`, before
   the fallback cascade.
2. `strict_uninit_shadow_miss_spec.spl` — uninitialized local `total`
   shadows a module global `total`. Normal: silently reads the global
   (wrong answer, no error). Strict: traps at the local read first.
3. `strict_stale_capture_note_spec.spl` — capture a global in a `Lambda`,
   mutate it via `refresh_bound_global` without refreshing the closure, call
   it. Strict logs the stale-capture note (§3.1); normal is silent.
4. `strict_dirty_names_invariant_spec.spl` — nested blocks/closures shaped
   like the bug `block_exec.rs:166` documents was once live. Regression
   lock: the set-diff assertion passes today: proves it stays true.
5. `strict_arena_boundary_stale_index_spec.spl` — mint a `nodes.spl` index,
   bump generation, recycle the slot, cross the stale `(idx,gen)` into an
   SFFI call. Strict refuses at the boundary, naming the owning generation.
6. `strict_overhead_spec.spl` — perf gate: representative run with
   `SIMPLE_STRICT_MEM` unset, wall time within noise of the M1/M2 baseline —
   the enforced zero-overhead-when-off proof.

## 7. Cost per check (zero-overhead-when-off)

Every check funnels through the §1 `OnceLock<bool>`; off-path is one relaxed
load + early return, matching `ATTR_ENABLED`/`ast_gen_check_enabled`:

| Check | On-path cost | Off-path cost |
|---|---|---|
| Uninit-name gate (§2) | one `HashSet` insert per unset `let`; one `contains`+removal per `Identifier` read | one bool load; `uninit_names` stays an unallocated empty `HashSet` |
| Stale-capture note (§3.1) | one `AtomicU64` load+compare per captured-global read; log only on mismatch | one bool load |
| Dirty-names invariant (§3.2) | one `O(dirty_names.len())` set-diff at block exit (rarer than expr evals) | one bool load |
| SFFI boundary provenance (§4) | one extra `i64` (generation) per call + one compare at the callee — thin adapter over M2's `(idx,gen)` | one bool load, no `NodeRef` widening (M2 §5, reused) |

All four stay diagnostic-first (log/error, no silent auto-repair), per the
plan's verification-culture note; `strict_overhead_spec.spl` (§6.6) is the
enforced proof, not an assumption, that the aggregate off-path cost is noise.
