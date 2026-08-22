# simple-core lane: 8 core-required ABI symbols need the C heap-registry design ported

**Status:** OPEN — product decision, test left red on purpose
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
