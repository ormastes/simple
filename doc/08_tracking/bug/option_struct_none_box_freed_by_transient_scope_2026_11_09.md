# Option<struct> `nil` built inside a transient scope is freed at scope end (general class)

Severity: P1. Status: fix-implemented-verification-pending (this PR).
Found 2026-11-09 as the general class behind
`stage3_native_build_heap_corruption_c0000374_2026_11_08` (PR #7872, which
fixed the single site `hir_cache_load` in `src/compiler/80.driver/driver_hir_cache.spl`).

## Class

In native code `nil` for an `Option<struct>` (`T?` with struct `T`) is NOT an
immediate: it is `rt_option_none()`, a heap-boxed `RtCoreEnum` (kind 4) from
`rt_enum_new(SPL_OPTION_ENUM_ID, SPL_HASH_NONE, nil)`. `rt_enum_new`
(`src/runtime/runtime_native.c`) interned payload-less variants only when NO
transient scope was active; inside an active scope it allocated a fresh box,
registered it through `rt_core_register_scoped_immortal`, and
`rt_transient_array_scope_end` freed it with the rest of the scope.

Consequence: any function that opens a transient scope, computes an
`Option<struct>`, ends the scope and returns the None handed its caller a
dangling pointer. The caller's `x == nil` went through the registry-checked
`rt_is_none` on freed memory (false), `.unwrap()` + a field write corrupted
the heap, and Windows reported c0000374 at the next malloc. Unlike
`Some(struct)`, a None gives the caller nothing to `transient_promote`
(call sites gate promotion on `!= nil`), so the class cannot be closed at the
call sites in general. The same applies to custom unit variants (`Mode.Idle`)
and to `Ok(true)` / `Ok(false)` / `Some(bool)` payloads built inside a scope.

## Root fix (runtime, both twins)

`rt_enum_new` now routes payload-less variants -- payload is the nil special,
the integer 0 that `lower_enum_construct_named` passes for unit variants, or
the `true` / `false` specials -- through `enum_new_unit_singleton`: a
lock-free, prepend-only singleton list keyed by (enum_id, discriminant,
payload). Lookup is acquire loads; publish is a CAS on the list head; a
thread that loses the race re-scans only the nodes prepended since its
snapshot and releases its own allocation (unregister + free) if a twin was
published meanwhile. `Option.None`, the hottest key, has a dedicated atomic
slot. Exactly one node exists per distinct key: memory is bounded by the
program's unit-variant count, with no capacity and no fallback allocation.
The one allocation per key is registered as a plain immortal
(`transient_scope_id = 0`, never tracked by a transient scope or a session
heap). `rt_transient_heap_promote` already treats a registered immortal root
as a no-op success, so callers that promote a None keep working. (Review
round 1 replaced the first version's fixed 4096-slot unsynchronised table,
which raced between native-build threads and leaked once full.)
Scalar payloads other than nil/0/true/false keep the scoped-box behaviour
(a caller returning `Some(7)` past scope end must promote it, as before).

- C: `src/runtime/runtime_native.c` (`enum_payload_is_unit`,
  `enum_new_unit_singleton`, `rt_enum_new`).
- Pure-Simple twin: `src/runtime/simple_core/core_enum.spl`
  (`enum_payload_is_unit`, `enum_new_unit_singleton`; 40-byte singleton nodes
  carry the singleton-list link at offset 32 and stay members of the enum
  registry so `enum_ptr` validates them).
- Selfcheck: `src/runtime/test/rt_enum_unit_variant_scope_singleton_selfcheck.c`
  (None / unit / bool-payload boxes survive scope end and are the same
  singleton inside and outside a scope; a heap-payload and a non-unit scalar
  payload variant left in the scope are still reclaimed -- the control; plus
  a 4-thread x 2000-iteration stress over 64 fresh keys asserting one
  identical singleton per key on every thread and distinct singletons for
  distinct keys).

## Audit (2026-11-09)

Every `transient_scope_begin()` site under `src/compiler`, `src/lib`,
`src/app` (46 functions in 35 files) was listed with its enclosing function's
return type. `hir_cache_load -> HirModule?` is the only one that returns an
Option built inside its scope (fixed at the site by #7872; now also safe at
the runtime level). The remaining sites return `bool`, `text`, `[NLLError]`,
structs built after scope end, or `Result<_, text>` (`Err(text)` payloads are
heap text and are promoted or built after scope end by those owners; `Ok(bool)`
is now covered by the singleton rule). No further call-site change was needed.

## Red / green (native, `s3_fable64b.exe`, `SIMPLE_HIR_CACHE=0 --runtime-bundle core-c-bootstrap`, `CC`=llvm-mingw clang)

Fixture `test/fixtures/compiler/transient_scope_option_struct_nil/escaping_none_runtime_singleton.spl`
(the OLD un-gated `hir_cache_load` shape plus a unit-variant probe and a
promote-None probe). Same compiler binary; only `src/runtime` differs
(resolved from the cwd):

- RED (cwd = pristine checkout; `llvm-nm` on its `runtime_native.o`: 0
  `enum_new_unit_singleton` symbols): `miss-case hit=true`,
  `hit-case hit=true`, `unit-case idle=false`, `promote-none ok=true`, exit 1.
- GREEN (cwd = this worktree; `llvm-nm`: 2 unit-singleton symbols; relinked
  with `-lwinhttp`, the known link-line gap): `miss-case hit=false`,
  `hit-case hit=true`, `unit-case idle=true`, `promote-none ok=true`, exit 0.
- Selfcheck linked by hand against the GREEN bundle's 42 runtime objects:
  `SELFCHECK PASSED (0 failures)` (22 checks). A standalone RED selfcheck
  could not be linked: the bundle's per-TU defines are not recorded, and a
  bare `clang -c runtime_native.c` duplicates owner symbols. The fixture
  flip above is the discriminating evidence.
- Lint of the twin: the 14 `primitive_api` errors are pre-existing on the
  untouched file (same count); one added `unnamed_duplicate_typed_args`
  warning of the same class as the existing `store_u32_le` calls.
- End to end (hello world on a stage3 rebuilt from this runtime) is pending a
  stage3 rebuild, like #7872.

## Not fixed here

- Rust seed runtime twin `src/compiler_rust/runtime/src/value/objects.rs`
  `rt_enum_new` tracks every enum via `track_transient_heap` (same class, no
  interning). The seed is bootstrap-only and its interpreter does not box
  Option this way; parity change deferred, noted for the owner.
- `SIMPLE_HIR_CACHE=0 native-build` from a non-repo cwd still dies in
  `_runtime_dir_not_found_message` (recorded in #7872).
