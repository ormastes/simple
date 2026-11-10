# Interpreter gaps behind the lib/native failing-spec cluster (2026-08-21)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN (Rust seed changes required; seed rebuild is blocked — a sweep
is running against the deployed `bin/simple`, so no diff was applied.)

Found while fixing the 33-spec `lib`/`native` failure cluster. Nine of those
specs were repaired entirely in Simple product code (see the commit touching
`src/lib/nogc_sync_mut/{src/collections/hashset,compression/brotli/*,db/dbfs_engine/superblock,fs_driver/mem_block_device,storage/shared/*,engine/render/*}.spl`).
The following are genuine seed defects that no Simple-side change can close.

## 1. Arrays returned by runtime allocators are not index-assignable

Minimal reproducer (fails; the same code with a Simple-built `[u8]` passes):

```simple
extern fn rt_byte_array_new(n: i64) -> [u8]
extern fn rt_array_set_len_known(arr: [u8], n: i64)

class Box:
    xs: [u8]
    static fn new() -> Box:
        var xs = rt_byte_array_new(4)
        rt_array_set_len_known(xs, 4)
        Box(xs: xs)
    fn set(i: i64, v: u8):
        self.xs[i] = v          # semantic: invalid assignment: cannot index
                                # assign to field `xs` of type array
```

Aliasing through a local gives the sibling message
`invalid assignment: cannot index assign value of type array`. Same for
`rt_bytes_alloc`. Every buffer handed back by a runtime allocator is therefore
write-once on the interpreter, which silently forced every `.spl` module that
preallocates a buffer and fills it slot-by-slot onto a dead path.

**Fix needed:** teach the interpreter's assignment path to treat a runtime
array value as an ordinary indexable array lvalue (both the direct
`self.f[i] = v` form and the aliased-local form).

**Workaround applied in product code:** replaced `rt_bytes_alloc` /
`rt_byte_array_new` / `rt_array_new_with_cap_text` with pure-Simple
push-built arrays in the affected stdlib modules.

## 2. Nested lvalues are unsupported

`self.buffers[idx].data[dst_i] = data[src_i]` →
`semantic: invalid assignment: complex field access not supported`.
Hit in `src/lib/nogc_sync_mut/engine/render/software_backend3d.spl`
(`upload_buffer`, `upload_texture`), which broke 4 render specs.

**Workaround applied:** hoist the intermediate object and its array into locals.

## 3. `use std.spec.*` omits some symbols that an explicit import resolves

`expect_not` and `get_test_count` are `pub` in
`src/lib/nogc_sync_mut/spec.spl`, and `use std.spec.{expect_not}` resolves
them, but under `use std.spec.*` the interpreter reports
`semantic: function 'expect_not' not found`. Other symbols in the same file
(`is_linux`, `assert_contains`, `skip_on_windows`) DO come through the glob, and
reordering the definition does not change the outcome — so it is a selective
export-set defect, not a truncation. Blocks
`test/01_unit/lib/nogc_sync_mut/spec_bool_expect_spec.spl`.

Note `SPIPE_INLINE_HELPERS` in
`src/compiler_rust/driver/src/cli/test_runner/execution.rs:969` also has no
`expect_not` shim, so the compile-mode path is missing it independently.

## 4. `dict` has no `for_each`

A `Map<K, V>` is represented as a `dict` by the interpreter; `filter`,
`map_values` and `merge` resolve to dict builtins, but
`map.for_each(\k, v: ...)` →
`semantic: method 'for_each' not found on type 'dict'`. Blocks
`test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl`.

## 5. `use pkg.Mod.{Mod}` still binds the module dict, not the class

`Widget.kind()` →
`method 'kind' not found on type 'dict' (receiver value: {Widget: <constructor:Widget>, Widget__kind: <fn:Widget__kind>, ...})`.
This is the exact defect
`doc/08_tracking/bug/group_import_self_named_module_binds_module_dict_2026-08-17.md`
claims fixed in `interpreter_eval.rs` / `evaluation_helpers.rs`; the deployed
seed does not carry it. Blocks both
`test/01_unit/compiler/module_resolver/group_import_self_named_module_spec.spl`
and `..._shadowing_generalization_spec.spl`.

## 6. Unbacked externs used by `compiler.types.simd_capabilities`

`rt_cpu_is_x86_64` / `rt_cpu_is_aarch64` / `rt_cpu_is_riscv64` / `rt_cpuid`
are defined ONLY in `src/runtime/runtime_native.c` and have no interpreter
backing, so `detect_capabilities()` dies with
`semantic: unknown extern function: rt_cpu_is_x86_64`. Blocks 12 of 14 examples
in `test/01_unit/compiler/native/simd_capabilities_spec.spl`.

Replacing only the three arch gates with a pure-Simple `host_arch()` test was
tried and deliberately reverted: it does not fix the spec (`rt_cpuid` fails
next) and it silently swaps compile-time arch for run-time host arch, which is
wrong under cross-compilation.

## Triage note 2026-08-21 (interpreter/evaluation bug sweep)

Re-read against the pure-Simple tree looking for anything closable without a
seed change. All six items stand as recorded — every one of them is in the
Rust seed. Item 4 (`dict` has no `for_each`) was independently re-confirmed:
`src/compiler/95.interp` has no dict method table, so there is no pure-Simple
surface to add it to (details in
`map_for_each_missing_on_dict_2026-08-21.md`). Still OPEN, still blocked on a
seed rebuild + deploy.


## Addendum 2026-11-11 (lane interp6) — SUPERSEDED on 5 of 6 items; item 2 fixed in source, blocked on seed redeploy

All checks on lane worktree `work/p3-interp6-20261111` (origin/release/1.0.0
tip 462b3b334fef), refreshed seed (build-commit 0791c2b7f4a7), every run
labelled seed-smoke with `--mode=interpreter --no-cache`.

**Item 1 — raw allocator arrays index-assignable: SUPERSEDED, verified.**
Scratch probe `build/p3fix-interp6/raw_array_lvalue_seed_smoke_spec.spl`
(build/, gitignored): `rt_byte_array_new` + `rt_array_set_len_known` buffer
written via `self.xs[i] = v` in a `me` method and via an aliased local —
both pass (2 examples green).

**Item 2 — nested lvalues: FIXED IN SOURCE, but the refreshed seed still
rejects them — BLOCKED on a seed rebuild (heavy native build, forbidden in
this lane).** Granularity probe
`build/p3fix-interp6/nested_lvalue_granularity_spec.spl` plus a plain
`simple run` fixture (`build/p3fix-interp6/fx/nested1.spl`) on the seed:
- `obj.field[i] = v` (2-level, field-first): WORKS on the seed.
- `arr[i].field[j] = v` and the bug doc's exact `self.buffers[idx].data[dst] = v`
  (index-first chains): still fail with
  `invalid assignment: complex field access not supported`.
The tree source carries the fix and proves it: a general place fallback
(`resolve_place` + `write_place`, `interpreter/node_exec.rs:2660-2745`) with
a Rust unit test for the exact shape
(`three_deep_field_index_field_index_assignment_lands`,
`s.rows[0].cols[1] = 42`). Both arrived with `9e7e7a526edb` (2026-11-07,
PR #7597 squash) + `3185f12d1d85` (place.rs), ancestors of the seed's
build-commit, and `git diff 0791c2b7f4a7 HEAD` on node_exec.rs/place.rs is
EMPTY — so the tracked seed binary does not match the source at its own
build-commit for this path (same lag observed for the MECALL perf counters
in the 2026-09-13 owned-call record). Closest verification available without
a rebuild: the fix's own Rust tests in the tree source.
Exact command needing grant: rebuild + redeploy the seed —
`cargo build --release --manifest-path src/compiler_rust/Cargo.toml --bin simple`
then redeploy via `scripts/bootstrap/bootstrap-deploy-transaction.shs`
(installs to `bin/simple.exe`); after redeploy, rerun the two probes above.

**Item 3 — `use std.spec.*` glob omissions: SUPERSEDED, verified.**
`test/01_unit/lib/nogc_sync_mut/spec_bool_expect_spec.spl`: 3/3 passed
(`expect_not` reaches glob importers on the seed).

**Item 4 — `dict.for_each`: SUPERSEDED, verified.**
`test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl`: 6/6 passed.

**Item 5 — `use pkg.Mod.{Mod}` self-named group import: SUPERSEDED, verified.**
`group_import_self_named_module_spec.spl` 2/2 and
`group_import_shadowing_generalization_spec.spl` 3/3 passed.

**Item 6 — unbacked `rt_cpu_*`/`rt_cpuid` externs: SUPERSEDED, verified.**
`test/01_unit/compiler/native/simd_capabilities_spec.spl`: 14/14 passed
(the interpreter extern table now backs the whole family).
