# Seed JIT array reclamation — design options

- **Date:** 2026-11-14
- **Status:** proposal, awaiting owner decisions (section 6). No product code changed.
- **Scope:** the Rust seed's cranelift JIT lane (`src/compiler_rust/`). Other lanes are covered only as constraints.
- **Bug:** `doc/08_tracking/bug/core_interp_per_iteration_array_leak_2026-11-14.md` ("Remaining", item 1).
- **Earlier records:** `seed_jit_array_copy_never_freed_2026-10-19.md`,
  `seed_jit_field_store_array_copy_never_freed_2026-11-04.md`,
  `native_build_worker_interpreter_heap_grows_unbounded_2026-08-17.md`,
  `native_array_copy_leaks_2026-10-20.md` (all under `doc/08_tracking/bug/`).

Paths below are relative to the repo root; `rs/` abbreviates `src/compiler_rust/`.

## 1. Summary

JIT'd code frees a heap object at exactly one lowering site, and only for arrays. Every
other array, string, dict, tuple, closure, enum and struct block lives until process exit.

The obstacle to fixing it is not the missing `free` call. It is that the JIT **aliases
arrays at seven assignment-like sites where the interpreter copies** (section 2.4), and no
heap object carries a reference count. A release is therefore safe only where the compiler
can prove the buffer has one holder.

Recommendation (section 5): extend the existing compile-time proof in
`rs/compiler/src/mir/lower/array_move.rs` to release proven-unique array locals at block
end, staged; keep explicit regions for coarse boundaries; do not add refcounting or a
collector to the seed.

## 2. Measured current state

### 2.1 Binary and method

- Seed built at `76f3263aa71` (`origin/release/1.0.0`, merge of PR #9068):
  `cargo build --release --bin simple`, sha256
  `76a5348ac554642975af981d49fe29d81316c129b5d31bbadfded6cc49368aa9`.
- Host: DGX Spark aarch64. Runs were serial, each under
  `systemd-run --user --scope -q -p MemoryMax=16G timeout 900`.
- JIT lane: `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT_ALL=1 simple run <probe>`.
  Interpreter lane: `SIMPLE_EXECUTION_MODE=interpret`.
- The counter probe was also run on the seed PR #9068 used for its evidence
  (sha256 `a6456302e14307e0…`); every counter row was identical.
- The run prints `[engine-demotion] reason=hybrid-interp-splice detail=rt_heap_live_count_by_kind`.
  That splices only the counter extern calls through the interpreter bridge; the module
  stays JIT'd (`rs/driver/src/exec_core.rs:1409-1424`).
- Probe sources are in the appendix. A probe file needs a `main` function; without one
  the run falls back to the interpreter (`jit-bail:no-main-fn`).

### 2.2 Where objects are allocated and freed

| Fact | Citation |
|---|---|
| Heap header is `object_type: u8, gc_flags: u8, reserved: u16, size: u32`. No refcount. | `rs/runtime/src/value/heap.rs:57-66` |
| An array is a header plus a separately allocated element buffer. `rt_array_new` uses `std::alloc`, registers the pointer, and adds it to an open transient scope if there is one. | `rs/runtime/src/value/collections.rs:907-915`, `:1391-1418`, `:224-249` |
| `rt_array_free` is shallow: frees the buffer, unregisters, frees the header. | `collections.rs:3814-3830` |
| `rt_array_free_deep` frees a graph of arrays and unshared strings, and refuses on any alias, cycle or other element kind. | `collections.rs:3917-4005`, `:3851-3878` |
| Counters are always on. `total_allocs` / `total_frees` / `kind_live_count` move only in `register_heap_ptr` / `unregister_heap_ptr*`. | `heap.rs:346-377`, `:428-454`, `:539`, `:565`, `:599` |
| Every validated accessor checks the registry, so a stale handle yields the accessor's default, not a crash, until the address is reused. | `heap.rs:812-828` |
| The only `rt_array_free` the JIT emits: `local.field = v` where the field is an array and `array_move.rs` proved the struct local is the only holder. | `rs/compiler/src/mir/lower/lowering_stmt.rs:708-765` |
| `MirInst::Drop` is emitted only before `Return`, for every non-parameter local. The cranelift arm is a no-op. | `lowering_stmt.rs:1331`, `:2685-2731`; `rs/compiler/src/codegen/instr/mod.rs:1494-1529` |
| `MirInst::EndScope` is a no-op and no lowering path emits it. | `lowering_stmt.rs:2737`; `rs/compiler/src/codegen/cranelift_emitter.rs:697` |
| `rt_string_free`, `rt_dict_free`, `rt_tuple_free`, `rt_object_free`, `rt_closure_free` exist. None is emitted by lowering or codegen. No enum free exists. | `collections.rs:4036`, `:4123`; `rs/runtime/src/value/dict.rs:198`; `rs/runtime/src/value/objects.rs:159`, `:234` |
| `rt_object_free` and `rt_closure_free` deallocate without `unregister_heap_ptr`. They would leave the registry and counters stale if used. | `objects.rs:157-169`, `:232-244` |
| Struct literals are raw `rt_alloc` blocks. They are not registered heap objects, so the counters do not see them. | `rs/compiler/src/codegen/instr/closures_structs.rs:571-573` |
| A side-table refcount (`rt_rc_share/retain/release`) exists. No MIR lowering emits it. | `rs/runtime/src/value/rc_graph.rs:34`, `:151-235` |
| Regions exist: `rt_transient_array_scope_begin/_end`, `rt_transient_heap_promote/_adopt`, `rt_session_heap_begin/_end`. Rust lowering never emits them; Simple sources call them explicitly. | `collections.rs:3058`, `:3292`, `:3487`, `:3575-3670`; e.g. `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` |

Array copies. `rt_array_copy` is emitted for a `Let` whose initializer is a place
(`lowering_stmt.rs:406-430`), for a field store from a place (`:685-703`), and for
`.copy()` / `.clone()`. It is not emitted for plain `Assign`, argument passing, return,
struct-literal arguments, closure capture, global write, or pushing into another array.
`array_move.rs` turns some `Let` and field-store copies into moves
(`array_move.rs:1-30`, `:38-50`).

### 2.3 Per-operation counts

Counter deltas over 1,000 iterations of the loop body, JIT lane. One string per row is
the report line itself and has been subtracted, as have arrays built once outside the
loop (1 to 3 per row). "aux" is element-buffer bytes. Raw output is reproduced by the
appendix probe.

| Loop body | arrays | other kind | frees | aux bytes |
|---|---|---|---|---|
| `acc = acc + i` (control) | 0 | 0 | 0 | 0 |
| `val a = [i, i+1, i+2]` | 1000 | – | 0 | 32,000 |
| `xs = []` (overwrite) | 1000 | – | 0 | 128,000 |
| `xs.push(i)` (one array grown) | 0 | – | 0 | 8,192 total |
| `xs[1] = i` | 0 | – | 0 | 0 |
| `val c = src` (read only) | 1000 | – | 0 | 32,000 |
| `var c = src; c[0] = i` | 1000 | – | 0 | 32,000 |
| `take_len(src)` (argument) | 0 | – | 0 | 0 |
| `val a = make_arr(i)` (returned literal) | 1000 | – | 0 | 32,000 |
| `val row = rows[1]` (local `[[i64]]`) | 1000 | – | 0 | 32,000 |
| `rows[1][0]` (direct read) | 0 | – | 0 | 0 |
| `val a = g_arr` (global) | 1000 | – | 0 | 32,000 |
| `g_arr[1] = i` | 0 | – | 0 | 0 |
| `val row = g_rows[1]` | 1000 | – | 0 | 32,000 |
| `val xs = h.xs` | 1000 | – | 0 | 32,000 |
| `var xs = h.xs; xs.push(i); h.xs = xs` | 0 | – | 1000 | 16,000 total |
| `h.xs = [i]` | 0 | – | 1000 | 0 |
| `val h = Holder(xs: [i], n: i)` | 1000 | obj 0 | 0 | 32,000 |
| `val p = Plain(a: i, b: i)` | 0 | obj 0 | 0 | 0 |
| `val s = "a" + "b"` | 0 | str 1000 | 0 | 0 |
| `val s = "v={i}"` | 0 | str 1991 | 0 | 0 |
| `val d = {"k": i}` | 0 | dict 1000 | 0 | 192,000 |
| `val t = (i, i+1)` | 0 | tuple 1000 | 0 | 0 |
| `val f = \x: x + 1` | 0 | closure 1000 | 0 | 0 |
| `val f = \x: x + src[0]` | 0 | closure 1000 | 0 | 0 |
| `val c = a + b` (array concat) | 1000 | – | 0 | 32,000 |
| `for i in 0..N` | 0 | 0 | 0 | 0 |
| `for x in src` | 0 | 0 | 0 | 0 |

Whole probe: `allocs=20985 frees=2000`. Both free rows are the single emission site of
section 2.2. On the interpreter lane every row reads zero, because interpreter values are
not runtime heap objects; that control is vacuous for counters, so RSS is used instead.

Peak RSS for 2,000,000 iterations (`/usr/bin/time`, kB). The JIT empty loop is 26,860 kB.

| Loop body | JIT RSS | growth per iteration | Interpreter RSS |
|---|---|---|---|
| `val a = [i, i+1, i+2]` | 190,880 | 84 B | 22,712 |
| `val h = Holder(xs: [i], n: i)` | 253,532 | 116 B | 28,540 |
| `val p = Plain(a: i, b: i)` (struct) | 89,452 | 32 B | not run |
| `val p = Pt(a: i, b: i)` (class) | 95,176 | 35 B | not run |
| `val s = Sh.Circle(i)` (enum) | 122,792 | 49 B | not run |
| `val s = "v={i}"` | 379,664 | 181 B | not run |
| `val t = (i, i+1)` | 163,456 | 70 B | not run |
| `val f = \x: x + 1` | 135,504 | 56 B | not run |
| `val d = {"k": i}` | 705,680 | 348 B | not run |

Findings:

1. **Every heap kind leaks, not only arrays.** Strings, dicts, tuples, closures and enums
   have the same "allocated per evaluation, never freed" behaviour.
2. **Structs and classes leak outside the counters.** `Plain` shows `allocs=0` and
   grows 32 B per iteration. Any acceptance test built only on `rt_heap_*` counters is
   blind to them. RSS must be part of acceptance.
3. **Reads allocate.** `val c = src`, `val row = rows[i]` and `val xs = h.xs` each mint an
   array even when the binding is only read.
4. **The interpreter lane does not grow** on the same programs (arrays are
   `Arc<ArrayData>`, freed by Rust `Drop`; `rs/compiler/src/value.rs:3098`).

### 2.4 The 18 frees

Re-run of the bug's repro (two `core_interpret` calls of a 10,000-iteration `for`) on the
HEAD seed:

| Point | allocs | frees | live arrays |
|---|---|---|---|
| start | 727 | 0 | 409 |
| after call 1 | 70,708 | 9 | 50,201 |
| after call 2 | 140,440 | 18 | 99,992 |

So the 18 frees are **9 per `core_interpret` call, independent of iteration count**. They
are one-off frees in per-call setup, not loop reclamation. The only site the JIT can emit
is `lowering_stmt.rs:762`; which nine source statements reach it was not attributed.
Alloc totals are lower than the bug's 700,504 because PR #9068 removed allocation sites;
about 5 arrays per iteration remain.

### 2.5 Aliasing: the JIT does not match the interpreter today

Each row mutates one name and reads the other. "copy" means the other name is unchanged.

| # | Case | Interpreter | JIT |
|---|---|---|---|
| A1 | `var b = a; b[0] = 9` | copy | copy |
| A2 | `var b = a; b.push(9)` | copy | copy |
| A3 | callee does `x[0] = 9` on its parameter | caller sees 9 | caller sees 9 |
| A4 | callee does `x.push(9)` on its parameter | caller sees it | caller sees it |
| A5 | `var b = ident(a); b[0] = 9` | copy | **alias** |
| A6 | `h = Holder(xs: a, ..); a[0] = 9` | copy | **alias** |
| A7 | closure captures `a`; `a[0] = 9`; call | copy | **alias** |
| A8 | `g_slot = a; a[0] = 9` | copy | **alias** |
| A9 | `rows.push(a); a[0] = 9` | copy | **alias** |
| A10 | `b = a` (plain assign); `b[0] = 9` | copy | **alias** |
| A11 | `var r = rows[0]; r[0] = 9` | copy | copy |
| A12 | `var x = h.xs; x[0] = 9` | copy | copy |
| A13 | `t = (a, 1); a[0] = 9` | copy | **alias** |

Consequences for any reclamation design:

- A5-A10 and A13 are the **escape list**. After any of them the array has a second holder
  that the runtime cannot see. Freeing through either name is a use-after-free.
- Parameters are shared with the caller in both lanes (A3, A4). A callee must never free
  a parameter.
- A5 means a call result is not known to be a fresh buffer.
- Closing the divergence by copying at those sites would add leaks until a release
  mechanism exists. `array_move.rs:70-76` records that this was tried and measured
  (280 MB to 2.0 GB on a 128 KiB zstd decode).

## 3. Constraints

1. **Value semantics.** "Arrays and text copy on assignment in every engine"
   (`doc/07_guide/language/value_semantics_by_engine.md:90`). Section 2.5 shows the JIT
   meets this only for `Let` from a place and field/row extraction. A reclamation change
   must not make any section 2.5 row worse, and must not turn an alias into a dangling
   handle.
2. **Interpreter contract.** The seed interpreter implements arrays as copy-on-write
   `Arc`; a real user alias still copies
   (`doc/08_tracking/bug/seed_interp_global_array_index_store_cow_quadratic_2026-11-13.md:53`, `:69-70`).
3. **Memory model documents disagree.** `doc/05_design/language/misc/memory.md:10-11`
   makes the GC domain the default (`T` is a GC reference, `:19`; `--gc=on` default,
   `:55`) and makes `&T` the meaning of plain `T` only in no-GC mode (`:27-29`).
   The no-GC plan removes tracing GC from no-GC mode and forbids implicit shared RC for
   ordinary unique values
   (`doc/03_plan/language/memory_safety/nogc_ownership_recovery_plan_2026-10-19.md:55-56`),
   and asks for cleanup generated from live-on-exit facts (`:217`). This design follows
   the no-GC plan. See owner decision D1.
4. **Drop is unimplemented everywhere.** The plan lists the JIT among the lanes that
   need parity (`:790`); its progress file records "backend Drop paths are no-ops"
   (`nogc_pointer_borrow_hardening_progress_2026-10-20.md:413-414`). The self-hosted
   backends also no-op `Drop`
   (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1521`,
   `src/compiler/70.backend/backend/native/isel_x86_64.spl:498`), and the native lane
   leaks array copies too (`doc/08_tracking/bug/native_array_copy_leaks_2026-10-20.md:13-18`).
5. **Self-hosted parity of the move pass.** `array_move.rs` has a pure-Simple port
   (`mir_array_move.spl`, commit `5760e201922`). A seed-only extension widens the gap.
6. **The seed is bootstrap-only by policy** (`CLAUDE.md:61`) but is what `bin/simple`
   resolves to today (`.claude/rules/commands.md:110`). It runs the spec suite and the
   bootstrap, where the measured peaks were 15.2 GB before and 4.8 GB after PR #9068
   (bug doc, evidence table). Cost matters, and so does not regressing bootstrap.
7. **Prior rejections stand unless something changed.** Refcounting was rejected because
   "one missed site is a use-after-free"
   (`seed_jit_array_copy_never_freed_2026-10-19.md:131-136`). A transient scope per JIT
   frame was rejected as unsound without escape analysis
   (`native_build_worker_interpreter_heap_grows_unbounded_2026-08-17.md:329-342`).
8. **No widening of nil.** A stale handle currently reads as the accessor default
   (section 2.2). A wrong release would therefore surface as a silent nil or zero, not a
   crash. Verification must make that loud (section 4, "Verification common to all").

## 4. Options

### Option A — proven-unique release at block end (extend `array_move.rs`)

**Mechanism.** `array_move.rs` already computes, per function, which array locals are
"owned": every write is a fresh literal or a copied place (`write_keeps_unique`,
`array_move.rs:359-381`) and every read is one that cannot create a second holder
(`scan_expr` with `Ctx`, `:495-582`; non-escaping methods at `:86-90`). Add a fourth
result set, `block_release_locals`, and have statement-list lowering emit
`rt_array_free(local)` when the declaring block ends.

**Files.** `rs/compiler/src/mir/lower/array_move.rs`, `lowering_stmt.rs` (block exit),
and later `mir_array_move.spl` for parity. No runtime change for arrays.

**Correctness risks and how the proof handles them.**

| Risk | Handling |
|---|---|
| Alias via A5-A10, A13 | Each is a `Ctx::Bare` use and disqualifies the local. Negative specs pin every row. |
| Closure capture | Already disqualifies (`array_move.rs:551-556`). |
| Parameters | Never owned (`owned`, `:349-355`). |
| Call results | Not fresh (A5); excluded until stage A4's summary. |
| Elements that are heap values | Stage A1 takes scalar element types only. Later stages use `rt_array_free_deep`, which refuses aliased graphs. |
| Early exit (`break`, `continue`, `return`, `?`) | Stage A1 skips any block that contains one after the declaration. Stage A2 emits the release on each exit edge. |
| Loop-body slot reuse | The `Let` re-initialises the slot before any use in the next iteration, so one release per allocation. |
| `defer`, generators, actors, `await` | Already poison the function (`:491`, `:558-567`). |
| Runtime retains the handle (FFI) | Only non-escaping builtin methods are allowed as readers. Passing the local to any other call disqualifies it. |
| Double free | One static release per `Let`, on a path that the `Let` dominates. |

`emit_function_drops` is not a usable shortcut. It reloads every non-parameter slot once
before `Return`, so it would free only the last value of a loop-body local, and would
free moved, aliased and never-initialised slots.

**Expected effect.** Rows of section 2.3 that become flat, by stage:

- A1: `val a = [..]`, `val c = src`, `var c = src; c[0] = i`, `val row = rows[1]`,
  `val a = g_arr`, `val row = g_rows[1]`, `val xs = h.xs` (scalar elements).
- A2: the same inside blocks with early exits, and arrays of arrays or strings.
- A3: overwrite release, `xs = []` and `xs = <fresh>` when `xs` is owned.
- A4: "returns a fresh array" function summary, enabling `make_arr(i)` and `a + b`.
- A5: struct temporaries with owned array fields, including freeing the `rt_alloc` block.

In the core-interpreter bug, the row-copy sites (`env_define`, `env_lookup`,
`env_assign`) were at least 10 of the 33 arrays per iteration (bug doc table) and are
A1-shaped. The share of the remaining 5 per iteration that A1 would remove was not
measured.

Time: one `rt_array_free` per released array, which takes the registry shard lock once,
the same cost class as the allocation's registration. The two rows that already free
(section 2.3) show the mechanism working in a loop with flat live bytes.

Strings, dicts, tuples, closures and enums are untouched by A. They need their own
proofs, and `rt_object_free` / `rt_closure_free` need the unregister fix first.

**Effort.** A1 small. A2 and A3 medium. A4 and A5 medium each. Parity port medium.

**Verification.** Counter and RSS rows above; the alias matrix must print the same
values on both lanes before and after; negative specs for every escape row must still
show the leak (delta 1000), proving the release did not fire.

### Option B — runtime reference counting

**Mechanism.** Give arrays a count (a header field, or the existing `rc_graph` side
table) and emit retain at every share site and release at every drop site.

**Files.** Runtime array header and all `rt_array_*` that store a handle; every lowering
path of section 2.5 plus `Any` boxing, dict and tuple element stores, struct copies
(`AggregateCopy` is shallow, `rs/compiler/src/mir/lower/lowering_core.rs:1027-1064`);
codegen for inlined element loads.

**Correctness risks.** One missed retain is a use-after-free; one missed release is the
current leak. The share-site list is exactly the set where the JIT already disagrees with
the interpreter, which is evidence that these sites are not uniformly routed through one
place. Structs are raw blocks with no header to count. Cycles need weak handling.

**Expected effect.** Would reclaim all array rows, and would make copy-on-write possible
(removing the read copies of finding 3). Adds a retain/release pair to every array
hand-off; with the side table that is a hash lookup under a lock per hand-off.

**Effort.** Large. **What changed since the 2026-10-19 rejection:** nothing. This option
is listed for completeness and is not recommended for the seed. It is the right shape
only if the owner decides the seed must reach interpreter-equal value semantics (D2).

**Verification.** Would need the quarantine mode below on the whole spec suite, plus a
count audit at exit (every live count explained by a root).

### Option C — regions at coarse boundaries

**Mechanism.** Use the existing transient scope: everything allocated while a scope is
open is freed at `rt_transient_array_scope_end`, except what was promoted
(`rt_transient_heap_promote`) or adopted into a session heap.

- **C1, explicit (exists today).** Simple source brackets a phase and promotes its
  result. The self-hosted compiler driver already does this.
- **C2, automatic per spec example.** The test runner opens a scope around each `it`.
- **C3, automatic per JIT frame.** Rejected on 2026-08-17 and still unsound: a callee
  that stores into a global, an outer container or its parameter (A3, A4, A8, A9)
  creates a reference that outlives the frame.

**Files.** C1: call sites in `.spl` only. C2: the spec runner, plus a promotion rule for
everything reachable from module globals at scope end.

**Correctness risks.** C2 frees anything an example stored into a module-level `var`
(for example `kept_rows` in `env_scope_ops_no_array_leak_spec.spl`), into a `describe`-level
binding, or into runner state, unless those roots are enumerated and promoted. The JIT
has no root map for globals that the runtime can walk today (not verified to exist), and
struct blocks are not registered objects, so a promotion walk cannot see through them.
C1 has the same risk at each call site, but each site is reviewed by hand.

**Expected effect.** C1 bounds memory per phase where applied and costs nothing
elsewhere; it does nothing for a long loop inside one phase. C2 would bound spec-suite
memory per example but not the 1M-iteration example that produced the 15.2 GB peak.

**Effort.** C1 small per site. C2 medium to large because of the root problem.

**Verification.** Per-site: counters before and after the phase, and the phase's result
read back after scope end.

### Option D — nothing in the seed; fix only the self-hosted backend

**Mechanism.** Accept unbounded growth on the seed JIT, keep removing allocation sites
in `.spl` as in PR #9068, and implement drops once in the pure-Simple compiler.

**Risks.** Not free: the self-hosted backends no-op `Drop` too and the native lane
leaks (constraint 4), so the same design work is needed there. Until a full-CLI
self-hosted binary is the daily tool, spec and bootstrap runs stay exposed to the seed's
growth; the 2026-10-19 host OOM was this class (commit `5760e201922` message).
Site-by-site `.spl` edits are permanent workarounds, which the project rules ask to file
rather than normalise.

**Effect.** None on the seed. **Effort.** None now, large later.

### Option E — tracing collection (considered, not developed)

The header has tri-colour and pin bits (`heap.rs:96-106`) and every object is in a
registry, so a mark-sweep is conceivable. It is out for the seed JIT: there are no stack
maps or safepoints, JIT frames hold raw handles in registers and spill slots, and struct
blocks are unregistered `rt_alloc` memory that would have to be scanned conservatively.
The abfall collector in `rs/runtime/src/memory/gc.rs` is not connected to
`runtime/src/value` allocation. It also contradicts the no-GC plan (constraint 3).

### Verification common to all options

- **Quarantine mode.** An env-gated runtime mode in which `rt_array_free` unregisters and
  poisons the object but does not return memory to the allocator, and
  `validate_heap_obj` aborts with a message when asked about a quarantined address.
  Because accessors already consult the registry (`heap.rs:821`), this turns every
  use-after-free on a validated path into a deterministic abort instead of a silent
  default value. Codegen paths that load elements without validation would need the same
  check or must be listed as uncovered.
- **Differential.** The section 2.5 matrix and the existing cross-engine specs, both
  lanes, same printed values before and after.
- **Counters plus RSS.** Section 2.3 rows as a spec (`@jit_spec_entry`), with RSS for the
  kinds the counters cannot see.

## 5. Recommendation

Adopt **Option A, staged**, with **C1** kept for phase boundaries. Reject B, C2, C3 and E
for the seed. Treat D as the fallback if the owner caps seed investment (D3).

Reasons: A is the only option whose safety argument is local and already has a working
precedent in the tree (the field-release proof, which is the source of every free
measured here). It cannot make semantics worse, because anything unproven keeps today's
behaviour. It is also the shape the no-GC plan asks for, so the proof logic carries over
to the self-hosted compiler.

### First landable slice (A1)

Release at fall-through block end, for a `Let`-bound array local when all hold:

1. the element type is a scalar (no heap elements);
2. the initializer is an array literal, an array-repeat, or a place (which lowering
   copies);
3. the local is owned under the existing analysis and never appears in an escaping
   context (section 2.5 rows A5-A10, A13, any non-builtin call argument, capture);
4. it is not a move source or a hand-over source in the existing sets;
5. no `break`, `continue`, `return` or `?` occurs in the declaring statement list after
   the declaration, at any depth.

Ship the quarantine mode in the same change, since it is the acceptance tool.

### Acceptance test for A1

A `@jit_spec_entry` spec plus an RSS check, on a recorded seed sha256:

- Positive (1,000 iterations each, live-array delta at most 2, frees at least 1,000):
  `val a = [i, i+1, i+2]`; `val c = src`; `var c = src; c[0] = i`; `val row = rows[1]`;
  `val a = g_arr`; `val row = g_rows[1]`; `val xs = h.xs`.
- Negative (must still show delta 1,000 and the same printed values): one case per
  escape row A5-A10 and A13, a closure capture, a block with `break` after the
  declaration, and an array of arrays.
- RSS: the 2,000,000-iteration `val a = [i, i+1, i+2]` run within 8 MB of the empty loop
  (today 190,880 kB against 26,860 kB).
- Alias matrix: identical output on both lanes, before and after.
- Whole run and the interpreter unit directory under quarantine mode with zero aborts.
- Red first: the positive cases fail on the current seed (delta 1,000, section 2.3).

## 6. Open owner decisions

- **D1. Which memory model governs.** `memory.md` says GC is the default domain; the
  no-GC plan and the lane brief say unique ownership is. This design assumes the latter.
  If GC is the intended default, Option E needs a real design instead of a paragraph.
- **D2. Is the JIT's aliasing (A5-A10, A13) to be fixed in the seed?** Fixing it by
  copying multiplies allocations, so it must come after a release mechanism. If the
  answer is yes, Option B's cost should be re-examined against "A plus copies".
- **D3. Investment ceiling for a bootstrap-only seed.** A1 only, A1-A3, or the full
  ladder. Each stage is separately landable.
- **D4. Are struct, class, string, dict, tuple, closure and enum leaks in scope?** They
  are measured in section 2.3 but untouched by A1-A4.
- **D5. Parity.** Must each stage land in `mir_array_move.spl` in the same change, or
  may the seed lead?
- **D6. Parameter semantics.** Both lanes let a callee mutate the caller's array through
  a plain parameter (A3, A4). If that is not intended, it changes what "owned" means.

## Appendix — probe sources

All probes share this shape and are run as in section 2.1.

```simple
extern fn rt_heap_live_count_by_kind(kind: i64) -> i64   # 1 str, 2 array, 3 dict, 4 tuple, 5 object, 6 closure
extern fn rt_heap_alloc_count() -> i64
extern fn rt_heap_free_count() -> i64
extern fn rt_heap_aux_live_bytes() -> i64

struct Holder:
    xs: [i64]
    n: i64

struct Plain:
    a: i64
    b: i64

var g_arr: [i64] = [1, 2, 3]
var g_rows: [[i64]] = [[1, 2], [3, 4]]

fn p_case():              # one function per row of section 2.3
    var i = 0
    var acc = 0
    val src = [1, 2, 3]   # per-case setup outside the loop
    while i < 1000:
        val c = src       # <- the loop body named in the table
        acc = acc + c[0]
        i = i + 1

fn main():
    # snapshot the four counters, call p_case(), print the deltas
    p_case()

main()
```

RSS probes use the same loop with 2,000,000 iterations and no counter calls, under
`/usr/bin/time -f %M`.

Alias matrix (section 2.5), one block per row, for example:

```simple
fn ident(x: [i64]) -> [i64]:
    x

fn main():
    val a5 = [1, 2, 3]
    var b5 = ident(a5)
    b5[0] = 9
    print "A5 a[0]={a5[0]} b[0]={b5[0]}"     # interpreter 1 / 9, JIT 9 / 9

main()
```

Frees repro (section 2.4): `core_interpret("var acc: i64 = 0\nfor i in 0..10000:\n    acc = acc + 1\nacc\n", ...)`
called twice from `main`, printing `rt_heap_alloc_count()` and `rt_heap_free_count()`
after each call, run from the repo root.
