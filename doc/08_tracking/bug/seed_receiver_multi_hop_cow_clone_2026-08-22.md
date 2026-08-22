# Seed interpreter: a `me`-mutating method deep-clones the field array when the receiver arrived through more than one parameter hop

- **Filed:** 2026-08-22
- **Component:** Rust seed interpreter (`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`)
- **Severity:** perf — O(n^2) on every accumulator threaded through helper functions
- **Status:** FIXED (this record's change)
- **Parent:** `doc/08_tracking/bug/hir_codec_writer_quadratic_cow_clone_2026-08-22.md`
  (landed `13bf3b2beee`), which bounded ONE victim (`HirCodecWriter`) by chunking
  its `parts` array and explicitly left this root defect open.

## Symptom

`w.put(x)` — a `me` method whose body is `self.parts.push(line)` — is O(1)
amortised when called from the frame that owns `w`, and O(len) when `w` reached
that frame as a parameter of a parameter.

Measured on `13bf3b2beee`, same binary, 80,000 pushes:

| shape | clones | elements copied | wall |
|---|---|---|---|
| `w.put(..)` called directly on a parameter | 4 | ~0 | 0.57 s |
| passed one hop further, then `w.put(..)` | 80,000 | 3.2e9 | 595 s |

The existing `STEAL_*` fast path is not merely unsuccessful for this shape —
it is never attempted (all `STEAL_*` counters read 0). That path is about
MODULE GLOBALS; this receiver is a frame-local parameter.

## Mechanism

`interpreter/expr/calls.rs`'s MECALL-OWNED path (landed 2026-08-22) makes the
mutation in-place by **moving** the receiver out of the calling frame
(`env.remove(var_name)`) before executing the method, so the callee's Arc is
unique and `Arc::make_mut` writes in place.

That is sufficient only when the calling frame is the sole holder. Reference
classes are NOT copied at argument binding (`arg_binding.rs::copy_value_type_in_place`
clones fields only for `is_value_type` structs), so `f(w)` leaves the CALLER's
binding and the callee's parameter sharing one `Arc<HashMap<..>>` — and through
it one `Arc<Vec<..>>` per array field. Every intermediate frame in the chain
keeps its own binding alive for the whole nested call. At the bottom,
`Arc::strong_count > 1`, so `try_field_array_mutation_in_place` takes its
copy-on-write branch and deep-copies the entire backing `Vec` on every push.

Nothing observes those intermediate bindings during the call: each such frame is
suspended, and the value it will hold afterwards is already determined —
`write_back_mutable_arguments` (Bug #19) overwrites it with the callee's final
value for exactly these argument shapes (identifier argument, container or
non-value-type object). The caller's handle is therefore pure aliasing pressure.

Every generated `hc_enc_*` HIR encoder is the multi-hop shape
(`hc_enc_hir_module(w, ..) -> hc_enc_hir_function(w, ..) -> .. -> w.put_i64(..)`),
which is why HIR encoding was quadratic in a module's encoded line count and
looked like a lowering cliff.

## Fix

`function_exec.rs`:

- `identifier_arg_bindings` reconstructs the argument -> parameter mapping using
  **exactly** the rules `write_back_mutable_arguments` uses, so the park set can
  never contain a binding the write-back will not restore. A spread or a
  variadic that breaks positional reconstruction parks nothing.
- `park_written_back_arguments` runs after argument binding and before the body:
  for each eligible identifier argument it replaces the caller's binding with
  `Value::Nil`, dropping the caller's Arc. `Nil` rather than removal so the
  write-back's `outer_env.contains_key` gate still passes.
- `restore_parked_arguments` runs after the write-back (and is the ONLY restore
  on the error path): any parked name still holding `Nil` is refilled from the
  callee's final parameter value. Idempotent.
- Counters `PARK_ARG_OK` / `PARK_ARG_RESTORED`.

Wired into all three call paths that already do the Bug #19 write-back:
`exec_function_with_captured_env`, `exec_function_inner`,
`exec_function_with_values_and_writeback_inner`.

### Deliberately NOT parked (each would let some other holder see a hole)

- non-local names — a module global is reachable through `MODULE_GLOBALS` and
  the owner stores, and has its own machinery (`80c39729a40`, `413b2f47988`)
- `self` under `SelfMode::SkipSelf`
- a caller name passed more than once in the same call (the two parameters
  legitimately alias and only one write-back wins)
- value-type structs — they keep value semantics and are never written back
  wholesale
- non-container values

### Arch preservation

Value semantics and copy-on-write are unchanged for genuinely live aliases. A
second binding of the same object elsewhere (`val snap = w.parts`, a captured
closure, a container holding it) is untouched by the park, keeps its Arc, and
still forces the copy — pinned by the aliased control test below, which asserts
both the old contents ARE preserved and that a clone still happens.

## Pins

- `src/compiler_rust/compiler/tests/interpreter_receiver_hop_depth_linear.rs`
  - `me_method_field_push_is_linear_at_every_hop_depth` — counter-based:
    elements deep-copied at depths 0/1/2/3 must each stay under `4n`
    (quadratic copies ~n^2/2; 8,000 vs 8,000,000 at n = 4,000). FAILS pre-fix.
  - `a_genuine_alias_still_forces_the_copy` — the aliased control: the snapshot
    keeps its old length AND the clone count must stay > 0.
  - `multi_hop_mutation_is_visible_to_the_owning_frame` — ordering/propagation.
- `test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl` with
  `test/fixtures/interpreter_receiver_hop_depth/shapes.spl` — scaling ratio
  (4x pushes < 8x time) plus direct-vs-3-hop at one size, and the two
  semantics cases.
- `scripts/check/check-perf-regression-tests.shs` — 8 `HOPPARK` mechanism rows
  (`PASS — 82 mechanism(s) checked, 0 regressed`).

## Measured A/B (same tree, same target dir, `SELF_FIELD_ARR_*` counters)

`me_method_field_push_is_linear_at_every_hop_depth`, n = 4,000 per depth,
depths 0..3 in one process:

| | pre-fix | post-fix |
|---|---|---|
| `SELF_FIELD_ARR_MUT_CALLS` | 8,204 | 16,204 |
| `SELF_FIELD_ARR_COW_CLONES` | 4,203 | **1** |
| `SELF_FIELD_ARR_COW_ELEMS_CLONED` | **8,018,103** | **1** |
| `PARK_ARG_OK` | n/a | 24,404 |
| `PARK_ARG_RESTORED` | n/a | 0 |
| verdict | `FAILED. 2 passed; 1 failed` | `ok. 3 passed; 0 failed` |

Pre-fix the run aborts at depth 1, so the 8.0M figure is ONE depth's 4,000
pushes — n^2/2 = 8,000,000 exactly. Depth 0 passed pre-fix, which is the direct
control: the defect is the hop, not the method.

The single post-fix clone is the aliased control (`val snap = w.parts` after one
push), i.e. copy-on-write still fires exactly where a live alias demands it and
nowhere else.


## Census (2026-08-22)

Scan of `src/**.spl` (owned code, `vendor/**` excluded): a class or struct with a
method doing `self.<field>.push/append/extend/insert(..)` — an accumulator — that
is ALSO declared as a parameter type somewhere, i.e. reachable through at least
one parameter hop and therefore in this defect's class before the fix.

**750 accumulator classes; 384 of them are passed as a parameter.** The count in
the first column is parameter-annotation sites, which is the multiplier on the
number of hops the receiver can travel.

| param sites | class | accumulated fields | file |
|---|---|---|---|
| 319 | `BeDomNode` | `event_listener_actions`, `event_listener_capture`, `event_listener_types` | `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` |
| 136 | `Buffer` | `data` | `src/lib/nogc_sync_mut/buffer/types.spl` |
| 132 | `Scheduler` | `high_priority`, `low_priority`, `normal_priority`, `systems` | `src/lib/nogc_sync_mut/ecs/system.spl` |
| 98 | `HirCodecWriter` | `chunks`, `parts` | `src/compiler/20.hir/hir_codec_support.spl` |
| 94 | `ActorContext` | `links`, `monitored_by`, `monitors` | `src/lib/nogc_sync_mut/enterprise_sale/foundation.spl` |
| 88 | `GdbMiClient` | `breakpoints`, `pending_results` | `src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl` |
| 87 | `ComponentStore` | `dense`, `ents`, `sparse`, `ticks` | `src/lib/nogc_sync_mut/ecs/component_store.spl` |
| 85 | `UISession` | `changelog`, `submitted_draw_ir_input_keys` | `src/lib/nogc_sync_mut/ui/session.spl` |
| 77 | `VfsManager` | `mounts` | `src/os/services/vfs/vfs.spl` |
| 64 | `TreeSitter` | `errors` | `src/compiler/10.frontend/treesitter/outline_lexer.spl` |
| 53 | `HttpRequest` | `headers` | `src/lib/nogc_sync_mut/net/http.spl` |
| 42 | `SessionManager` | `sessions` | `src/lib/nogc_async_mut/mcp/session.spl` |
| 39 | `SymbolTable` | `qualified_function_ids`, `qualified_function_names`, `qualified_type_ids`, `qualified_type_member_names` | `src/lib/nogc_sync_mut/dependency_tracker/symbol.spl` |
| 38 | `Table` | `column_order`, `rows` | `src/lib/nogc_sync_mut/src/table.spl` |
| 36 | `PhysicsWorld` | `objects`, `static_objects` | `src/lib/nogc_sync_mut/io/rapier2d_sffi.spl` |

### Estimated impact

The cost is `O(hops-independent) x O(final length)` per push, so it scales with
how long the accumulated array gets in one traversal, not with the param-site
count. Ranked by that:

1. **`ComponentStore` / `Scheduler` (ECS)** — `dense`/`sparse`/`ticks` grow to
   the entity count and are appended through `Scheduler -> System -> store`
   helper chains. This is the largest single-array accumulation in the tree and
   was quadratic in entity count on the interpreted lane.
2. **`SymbolTable`** — four parallel qualified-name arrays appended once per
   resolved symbol, through the dependency-tracker's helper chain. Grows with
   the whole program's symbol count, so it was quadratic per compile.
3. **`BeDomNode`** — three parallel listener arrays; per-node lengths are small,
   but the 319 param sites mean nearly every browser-engine helper is on the
   slow shape.
4. **`Buffer.data`** — byte accumulation through `Buffer` parameters; quadratic
   in buffer length, which is unbounded for file/network reads.
5. **`TreeSitter.errors`, `HttpRequest.headers`, `VfsManager.mounts`,
   `Table.rows`** — bounded in practice (tens to hundreds), so the pre-fix cost
   was real but not a cliff.

`HirCodecWriter` is listed for completeness: it is already bounded by
`HIR_CODEC_CHUNK_LINES` (`13bf3b2beee`). That chunking stays — it is a
defence-in-depth bound on a hot generated encoder, and its cost spec still
passes — but with this fix it is no longer load-bearing.

**No further per-site changes are proposed.** The defect was in the interpreter,
not in any of these call sites; the fix is at the single choke point all 384 of
them pass through, so working around it per class would be exactly the kind of
normalised workaround CLAUDE.md forbids.

## Seed suite regression check

`cargo test --release -p simple-compiler` with the fix: **3870 passed, 6 failed**.
All six were then re-run with the fix REVERTED on the same tree (`13bf3b2beee`)
and **all six fail identically without it**, so this change introduces zero new
failures:

- `hir::lower::tests::expression_tests::impl_text_self_chars_index_remains_a_string_receiver`
- `hir::lower::tests::expression_tests::text_rfind_uses_string_method_lowering`
- `hir::lower::tests::expression_tests::uppercase_string_is_empty_uses_string_method_lowering`
- `interpreter::interpreter_extern::tests::rt_string_ends_with_is_registered_and_correct_sdoctest_2026_08_07`
- `pipeline::native_project::tests::test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source`
- `pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive`

None touches `interpreter_call`; they are HIR string-method lowering, an extern
registration assertion, and two native_project build lanes. They are pre-existing
reds on `13bf3b2beee`, not caused or masked here.
