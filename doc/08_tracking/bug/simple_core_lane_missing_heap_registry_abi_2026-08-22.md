# simple-core lane: 8 core-required ABI symbols need the C heap-registry design ported

**Status:** OPTION 1 IMPLEMENTED 2026-08-31 (all 13 ported to pure Simple — see Appendix (2)); awaiting Linux `emit_archive` test pass before closing
**Test:** `pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive`
**Filed:** 2026-08-22 (seed lane, follow-up to `doc/08_tracking/test/seed_cargo_test_backlog_2026-08-21.md` group 2)

## What is red

The test builds `src/runtime/simple_core/*.spl` into `libsimple_runtime.a` with
`emit_archive` and asserts every name in `simple_common::CORE_REQUIRED_RUNTIME_SYMBOLS`
is defined. Eight are not:

```
rt_is_jit_runtime
rt_struct_alloc            rt_struct_receiver_valid
rt_transient_array_scope_begin  rt_transient_array_scope_pause
rt_transient_array_scope_end    rt_transient_heap_promote
rt_native_cmp
```

These are exactly the "8 undefined ABI symbols" the 2026-08-21 backlog named.
They are **not** missing from the core-C archive any more (that was a separate
one-symbol gap, `rt_is_jit_runtime`, fixed the same day in `runtime_native.c`);
they are missing from the **pure-Simple** core tree.

## Why this is not a "straightforward runtime function"

- `rt_struct_alloc` / `rt_struct_receiver_valid` are the C heap registry
  (`runtime_memory.c`: a tombstoned open-addressing table of live struct
  allocations under an rwlock, consulted on every guarded field access so a
  freed receiver traps instead of reading garbage — see
  `src/runtime/test/rt_struct_receiver_valid_selfcheck.c`).
- `rt_transient_array_scope_*` / `rt_transient_heap_promote` are the transient
  immortal-registration and reclaim machinery in `runtime_native.c`
  (`rt_core_register_scoped_immortal`, `rt_core_reclaim_transient_immortal`,
  the transient plan walker over arrays/dicts/closures).
- `rt_native_cmp` needs the tagged string/float decoders of that same value
  model.

A faithful port means porting the heap-registry and transient-scope design
into `simple_core/core_memory.spl`. A *non*-faithful port is exactly what the
task rules forbid: `rt_transient_array_scope_begin` returning 0 ("no scope")
forever, or `rt_struct_receiver_valid` returning 1 unconditionally, would make
the symbol table green while silently removing a safety check. Neither was
done.

## The undocumented decision

`doc/04_architecture/runtime/default_native_runtime_shift_to_c_core_abi.md`
defines `simple-core` as "the preferred pure-Simple lane **when** an
ABI-complete pure-Simple core runtime archive is present", and auto-selection
falls back to `core-c-bootstrap` otherwise. The test's own name says the tree
emits a *partial* archive, yet it asserts *completeness*. One of these must
give:

1. **Port the design to pure Simple** (`core_memory.spl` gains the registry +
   transient scopes; `core_values.spl` gains `rt_native_cmp`). Makes the
   `simple-core` lane selectable. Real work, needs its own verification pass
   against the C selfchecks.
2. **Scope the test to the lane's documented contract**: assert the archive
   builds and that `runtime_archive_has_core_required_symbols` is *false* (so
   auto-selection falls back to core-C), and move the completeness assertion
   under a `simple-core-complete` gate that flips when option 1 lands.
3. **Shrink `CORE_REQUIRED_RUNTIME_SYMBOLS`** for the pure-Simple lane. Not
   recommended — it is the ABI the codegen emits against.

Until one is chosen the test stays red, and `resolve_runtime_lane` keeps
correctly choosing `core-c-bootstrap`.

## Related, recorded here rather than lost

- `.preinit_array` browser-renderer hook in `runtime_process.c` is compiled out
  of the `SIMPLE_CORE_C_STANDALONE` archive (Stage4 forbids ctor/dtor sections
  in the archive core). `rt_browser_renderer_sandbox_enter()` is fail-closed on
  it, so a core-C-built renderer worker refuses to start rather than running
  unjailed. Hosting the renderer on the core-C lane needs an explicit startup
  entry point instead of a constructor. See
  `core_c_lane_cannot_host_browser_renderer_preinit_2026-08-22.md`.

---

## Appendix 2026-08-31 — the set is 13, not 8; and the fix locus is NOT C

Re-measured mechanically against the authoritative array
`CORE_REQUIRED_RUNTIME_SYMBOLS` (`src/compiler_rust/common/src/runtime_symbols.rs:118`,
extraction bounded on its closing `];` — **88 entries**) and against
`pub fn` definitions in `src/runtime/simple_core/*.spl` (340 exports).

**75 present, 13 absent.** The 13 are the 8 already filed above plus **5
statistics siblings** added to the contract after this record was written:

| # | symbol | group |
|---|---|---|
| 1-8 | as listed at the top of this record | heap registry / transient scopes / cmp |
| 9 | `rt_transient_last_promoted_nodes` | transient promotion statistics |
| 10 | `rt_transient_last_promoted_bytes` | transient promotion statistics |
| 11 | `rt_transient_promotion_stats_reset` | transient promotion statistics |
| 12 | `rt_transient_scope_promoted_nodes` | transient promotion statistics |
| 13 | `rt_transient_scope_promoted_bytes` | transient promotion statistics |

### Locus correction (read this before "implementing" anything)

**All 13 already have real C definitions.** Measured by definition-line grep over
`src/runtime/**/*.c` excluding `test/`:

- `rt_is_jit_runtime` — `runtime.c:258`, `runtime_native.c:596`
- `rt_struct_alloc` — `runtime_memory.c:491`, `runtime_native.c:5834`
- `rt_struct_receiver_valid` — `runtime_memory.c:501`, `runtime_native.c:5844`
- `rt_native_cmp` — `runtime_native.c:3847`
- all six `rt_transient_*` scope/promote entries and all five statistics
  entries — `runtime_native.c` (statistics at `2073-2091`)

So "add these in C" is a no-op against the red test and an active hazard: the
test builds its archive from `src/runtime/simple_core/*.spl` via `emit_archive`
(`native_project/tests.rs:6345-6371`), a tree into which C can never link, and
duplicating `runtime_native.c` definitions is the 475-collision class already
disproved in `8ca87866c6`. **The gap is a pure-Simple porting gap, exactly as
option 1 above states. Nothing was implemented, deliberately.**

### Derived contracts for ranks 9-13 (C impl is the spec)

Backing state is four `_Thread_local int64_t` counters
(`runtime_native.c:1066-1069`) — per-thread, never shared.

- **`rt_transient_last_promoted_nodes() -> i64`** (`:2073`) and
  **`rt_transient_last_promoted_bytes() -> i64`** (`:2077`) report the node and
  byte counts promoted by the **most recent** `rt_transient_heap_promote` call
  only. `rt_transient_heap_promote` zeroes them on entry (`:2124`) and writes
  the final tallies at `:2200-2201`, so a promote that promotes nothing leaves
  them at 0 — they are a "last call" window, not a running total.
- **`rt_transient_scope_promoted_nodes() -> i64`** (`:2081`) and
  **`rt_transient_scope_promoted_bytes() -> i64`** (`:2085`) are the running
  totals **accumulated across every promote within the current scope**. Each
  promote adds its `last` tallies into them with explicit `INT64_MAX`
  saturation rather than wraparound (`:2202-2211`). They are zeroed only by
  `rt_transient_array_scope_begin` (`:1303-1304`), never by promote.
- **`rt_transient_promotion_stats_reset() -> void`** (`:2089`) zeroes **only**
  the two `last_*` counters (`:2090-2091`) and deliberately leaves the two
  `scope_*` totals untouched. That asymmetry is the whole point of the pair and
  is the thing a port is most likely to get wrong; `scope_begin` gets the
  scope counters back to zero by assigning them separately right after calling
  reset.

A faithful port must preserve: thread-locality, the reset asymmetry, saturating
rather than wrapping accumulation, and the zero-on-entry behaviour of promote.
Behaviour is pinned by `src/runtime/test/rt_transient_heap_scope_selfcheck.c`
(e.g. `:89` asserts `last_promoted_nodes() == 8`, `:97` and `:119` assert it
returns to 0), which is the acceptance oracle for option 1.

### Scope note

Ranks 9-13 are the statistics surface of the very machinery ranks 4-7 implement.
They cannot be ported independently and add no new design work — they land with
option 1 or not at all. This remains a finishing task, not a program.

---

## Appendix 2026-08-31 (2) — option 1 IMPLEMENTED: all 13 ported to pure Simple

The pure-Simple port landed (this appendix records what/where; verification
limits below are honest, not rhetorical):

| symbols | file |
|---|---|
| `rt_struct_alloc`, `rt_struct_receiver_valid`, `rt_transient_array_scope_begin/_pause/_end`, `rt_transient_heap_promote`, all 5 statistics entries; transient-aware `rt_alloc`/`rt_realloc`/`rt_free` | `src/runtime/simple_core/core_memory.spl` |
| `rt_native_cmp` (next to its `rt_native_eq` sibling) + transient string flag/reclaim helpers | `src/runtime/simple_core/core_string.spl` |
| `rt_is_jit_runtime` (next to `rt_is_interpreter_runtime`) | `src/runtime/simple_core/core_process.spl` |
| allocator note-hooks + membership/reclaim helpers (incl. a NEW dict registry in the unused header word @24, so a reclaimed dict handle reports invalid instead of dereferencing freed memory) | `core_array.spl`, `core_array_ops.spl`, `core_enum.spl`, `core_closure.spl` |

Semantics carried over from the C spec, each pinned by a code comment naming
the C line: reset asymmetry (`stats_reset` zeroes ONLY `last_*`; `scope_*`
zeroed only by `scope_begin`), INT64_MAX saturation on `scope_*`
accumulation, promote's refusal gate BEFORE the stats reset, zero-on-entry
`last_*` window, raw-registry-first classification with tag stripping,
persistent containers classifying as plan nodes while persistent strings do
not, owned = !paused for raw registration, membership recheck before every
reclaim free, and the silent scope-death contract (registry-gated validity).

Documented deviations: module-level `var` state instead of `_Thread_local`
(equivalent only under the lane's single-threaded contract — disclosed at the
top of `core_memory.spl`); linear ponytail tables instead of C's hash tables
(performance, not semantics); no shared/short-cache string exemption (this
lane has no intern); heap floats and UINT boxes stay unregistered leaves
(pre-existing lane behaviour); lane-local byte accounting per this lane's
header sizes.

Verification on the Windows checkout (no cargo, no Linux `emit_archive`):
mechanical census 88/88 required symbols now defined as `pub fn`; all edited
files parse and reach SMF emission (fail only on the expected no-`main`);
lint shows only the pre-existing `primitive_api`/style debt every raw-ABI
sibling already carries; a renamed 1:1 transliteration of the state machine,
stats expressions, receiver-validity and cmp dispatch passed 43/43 checks
under `bin/simple.exe run`. NOT yet verified: the seed test
`test_simple_core_source_tree_emits_partial_runtime_archive` (Linux-gated)
and the graph-walk/reclaim halves against
`rt_transient_heap_scope_selfcheck.c` — the raw-memory SFFI externs
(`malloc`/`spl_load_i64`/...) are unbacked under the interpreter, so those
halves are verified by inspection only until a Linux archive build runs.
The selfcheck's shared-cache / literal-intern assertions are NOT satisfiable
on this lane (no intern exists; those symbols are not in the 88) and its
`rt_heap_registry_count` assertions map onto the per-kind registries
(`rt_heap_registry_count` itself is not core-required and was not added).
