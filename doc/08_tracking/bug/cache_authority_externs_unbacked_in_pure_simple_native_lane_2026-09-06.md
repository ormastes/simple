# `rt_cache_host_*` externs are unbacked in the pure-Simple native lane

- **Filed:** 2026-09-06
- **Class:** missing runtime backing for a stdlib extern (silent-nil / NULL-GOT
  family, `unregistered_extern_silent_nil_2026-08-01.md`)
- **Status:** open, deliberately not papered over by a parity-baseline row.

## Claim

`src/lib/common/cache_host_authority_v1.spl` and
`src/lib/common/cache_daemon_host_authority_v1.spl` are **stdlib** and declare 28
`extern fn rt_cache_host_*_v1` plus two `rt_cache_daemon_*_v1`. Their C provider
is `src/runtime/runtime_cache_host_authority_v1.c`, which is registered in
exactly one of the three C runtime source lists:

| list | file | carries it? |
|---|---|---|
| seed | `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:347` | yes |
| simple | `src/compiler/70.backend/backend/runtime_compiler.spl` | **no** |
| rust | `src/compiler_rust/runtime/build.rs` | no — and correctly so |

The Rust crate is fine: it defines the whole family itself in
`src/compiler_rust/runtime/src/cache_host_authority_v1.rs`, so adding the C file
to `build.rs` would be a duplicate-symbol link error.

The gap is the **simple** lane — the pure-Simple native product build. There, no
list compiles the C file and no Rust crate is linked, so every one of those
stdlib externs has no definition. Per
`unregistered_extern_silent_nil_2026-08-01.md` an extern with no runtime backing
returns nil rather than failing, so the failure mode is a silent wrong answer at
an authority boundary, not a link error.

## Why it is filed rather than fixed

`compile_runtime_objects` in `runtime_compiler.spl` is not a flat list. It has
bundle logic around lines 593-640 that assigns canonical owners
(`runtime_memory.c` owns the allocator ABI, `runtime_dynload.c` owns
`spl_dlopen`/`spl_dlsym`/`spl_dlclose`, `runtime_native.c` has per-lane copies
compiled out by `-DSIMPLE_RUNTIME_MEMORY_OWNER`). Adding a member to that list
without being able to link-test the result is how the ownership collisions those
comments describe get reintroduced. No deployed pure-Simple `bin/simple` is
available on this host to test the resulting product link.

`scripts/check/runtime_source_list_parity_baseline.txt` therefore records the row
as `runtime_cache_host_authority_v1.c seed`, which is the file's **true** current
membership — the parity gate's job is to freeze truth and catch drift, not to
assert desired state. The row is annotated with a pointer to this record so the
gap is visible rather than absorbed.

## What closing it requires

1. Decide the owner: add `runtime_cache_host_authority_v1.c` to
   `compile_runtime_objects`' source list, or provide a pure-Simple twin under
   `src/runtime/simple_core/` (the pattern `core_fs.spl` / `core_memory.spl`
   already use for other `rt_*` families).
2. Link a pure-Simple native product and confirm no duplicate definition against
   `runtime_native.c` / `runtime_memory.c`.
3. Update the parity baseline row to `seed,simple` **as a consequence** of the
   source change, never ahead of it.
4. Extend `src/runtime/test/rt_cache_host_authority_v1_selfcheck.c` to assert the
   symbols resolve in that lane.

## Related

- Two of the daemon externs (`rt_cache_daemon_serve_v1`,
  `rt_cache_daemon_route_v1`) had **no C definition at all** in any lane until
  2026-09-06; that half is fixed in
  `src/runtime/runtime_cache_host_authority_v1.c`. This record covers the
  remaining lane-membership gap, which affects the whole family.
- Note that 7 of the `rt_cache_host_*` symbols are additionally *fail-closed*
  (`return -1`) in the C provider by design, pending byte-record parity with the
  Rust provider. That is a separate, deliberate state and is not this bug.
