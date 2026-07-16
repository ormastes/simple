# native-build: `?` on `Option` silently miscompiles (treated as `Result`)

**Severity:** high (silent-wrong on BOTH oracle and native — no diagnostic)
**Found:** 2026-07-14, errhandling lane
**Status:** open
**Backend:** native-build `--entry` and seed interpreter

## Symptom

Applying `?` to an `i64?`/`Option` value inside a `Result`-returning function
produces wrong values with no diagnostic on either backend (observed rc 208
oracle / 209 native for a case that should be deterministic).

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` ~L972
`lower_try_expr` unconditionally treats the `?` base as a `Result`
(`rt_enum_discriminant`/`rt_enum_payload`), with no branch for `Optional` types.

## Blocking design findings (2026-07-15)

A reviewed prototype proved that `Option<T>` first needs canonical HIR lowering:
the flat bridge preserves `Option<i64>`, but `lower_named_kind` currently turns
it into unresolved `HirTypeKind.Error`. Direct-call recovery then works, while
unannotated locals and method-call results still lack authoritative container
metadata and would regress valid Result `?` if unknown operands were rejected.

The deeper blocker is the native flat primitive Option ABI. Raw `i64?` payloads
use their bare bits while nil uses sentinel `3`, so a valid present payload `3`
is indistinguishable from absence. Explicit `None` is separately constructed as
an enum with discriminant `1`, but `rt_is_none` recognizes sentinel `3` or a
legacy hashed discriminant, not ordinal `1`.

The fix therefore requires a uniform tagged/boxed Option representation (or an
equivalent non-colliding ABI) at producers and consumers, plus declared-type
provenance for direct calls, locals, and method calls. Acceptance must cover
raw/boxed zero, payload `3`, explicit `Some`/`None`, compatible and incompatible
return containers, unannotated locals, Result method calls, and unchanged
Result Ok/Err propagation. The incomplete MIR-only prototype was reverted.

## Reviewed ABI design (2026-07-15)

Implementation is deferred until a runnable pure-Simple `native-build` gate is
available. Source-only landing cannot prove the absence of double wrapping,
payload-3 collisions, or Result regressions across this ABI boundary.

The coherent fix requires both layers below:

1. Canonicalize `Option<T>` to HIR Optional and add MIR
   `Optional(inner)` as static container metadata. Its backend ABI is one `i64`
   tagged handle, not the current unused physical `(Bool, T)` tuple. Preserve
   function-return and MIR-local HIR container metadata across annotated and
   unannotated locals, direct calls, and method calls. `?` must accept only
   Option-to-Option or Result-to-compatible-Result propagation and loudly
   reject unknown or mismatched containers.
2. Reserve `OPTION_ENUM_ID = 1` with `Some = 0` and `None = 1`. Every typed
   boundary (let/assign/field/argument/return/call) converts `T` to the same
   outer `rt_enum_new` handle, passes an existing Option through without
   double-wrapping, and converts nil to the same None handle. Explicit
   `Some`/`None` use that helper. The outer handle makes raw payloads `0` and
   `3` unambiguous; inner payload boxing is needed only for erased `Any`.
3. Add `rt_enum_id` consistently to the C and pure-Simple runtimes. Option
   predicates and unwrap require the reserved enum id plus ordinal
   discriminant. Result keeps its existing Ok/Err path and must not be
   reclassified by generic Option predicates.

Required executable acceptance covers `Some(0)`, `Some(3)`, text, raw nil,
explicit `Some`/`None`, lets, assignments, fields, parameters, returns, direct
and method calls, unannotated local aliases, and single evaluation. It also
requires incompatible return containers and unknown operands to build-fail
without artifacts, plus unchanged Result Ok/Err propagation controls.

## Additive prerequisite (2026-07-15)

The behavior-neutral `rt_enum_id(i64) -> i64` API is now implemented across
the C, hosted, Rust-seed, and pure-Simple runtime owners and their LLVM,
llvm-lib, Cranelift/runtime-symbol, ELF-resolution, and strict-stub surfaces.
Focused API/link assertions cover valid enum IDs and supported null/non-enum
`-1` results in the weak C, hosted C, Rust, and pure-Simple owners.
This does not change Option producers, predicates, coercion, or `?` behavior,
and therefore does not close the bug. Execution remains pending a valid
pure-Simple artifact; the tagged Option producer/consumer switch must still
land atomically with the full dual-backend acceptance matrix.

The emergency MIR call-lowering registration now also uses the canonical
`Some = 0`, `None = 1` order instead of reversing the variants when module
registration is missing. A focused source-contract spec keeps both owners in
lockstep; this prerequisite likewise does not close the ABI bug.

## Reproduce

`/tmp/wt_errhandling/` probes (Option `?` alongside Result `?`).
