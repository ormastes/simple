# native-build: `?` on `Option` silently miscompiles (treated as `Result`)

**Severity:** high (silent-wrong on BOTH oracle and native — no diagnostic)
**Found:** 2026-07-14, errhandling lane
**Status:** typed local/direct-call support implemented; execution and uniform tagged Option ABI pending
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
unannotated locals and unresolved method-call results still lack authoritative
container metadata and would regress valid Result `?` if unknown operands were
rejected.

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

## Fail-closed boundary (2026-07-16)

MIR lowering now rejects an authoritatively typed Optional base before the
existing Result `?` decoder evaluates it. Annotated locals and direct-call
Optional returns have independent loud-fail parity cases; a strict default-LLVM
plus explicit-Cranelift Result `?` control preserves Ok and Err propagation.
The diagnostic is fatal in the native driver, so no binary survives this known
wrong path.

The source now recovers resolved method return types through the existing
`MethodResolution` symbol before the same guard. This source-implements the
fail-closed path for typed locals, direct calls, and resolved methods without
changing the Option representation or Result decoder. Unresolved late-dispatch
methods remain open and are not guessed, because rejecting them could break
valid Result `?`. Default-LLVM and explicit-Cranelift execution proof remains
pending the pure-Simple native gate; this does not validate the tagged ABI.
The hosted Linux/macOS/Windows matrix and FreeBSD x86_64 full gate now select
the existing annotated-local and direct-call loud-fail cases for both backends,
requiring a nonzero build, no artifact, and the exact diagnostic. Their CI
execution is pending; resolved-method coverage remains source-contract only.
ARM32 default LLVM and Windows ARM64 LLVM/Cranelift also schedule the same
fixtures with explicit targets and require compile refusal with no object.
Those are target-directed compiler checks, not target execution or tagged
Option support. The cross-module Result control now sends both Ok and Err
through `?` on FreeBSD x86_64 and AArch64/RISC-V QEMU to guard the unchanged
Result path; that execution is pending too.

## Diagnostic degraded to "MIR error: nil" — fixed (2026-07-16, q_optiontry_dynload lane)

After the `Named("Option",[T]) -> HirTypeKind.Optional(T)` mapping landed
(hir_lowering/types.spl), the fail-closed Optional arm in `lower_try_expr`
became reachable for the `option_try_annotated_loud` / `option_try_direct_loud`
parity cases — the build DID refuse loudly (rc=1, no binary), but the
diagnostic printed as `[ERROR] MIR error: nil` instead of the expected
"native Option try operator requires the tagged Option ABI", failing the
parity harness diagnostic match.

Root cause: `lower_try_expr` passed the bare `base.span` into `error(message,
span: Span?)`. The seed interpreter does not auto-wrap a bare `Span` into the
`Span?` parameter, so `_format_mir_error`'s `match err.span` (driver_pipeline)
fell through BOTH the `Some(sp)` and `nil` arms and returned nil — the whole
formatted message became nil. Every other loud-fail error site passes
`Some(span)` explicitly.

Fix: wrap the span — `self.error("native Option try operator requires the
tagged Option ABI", Some(base.span))` (switch_operators_calls.spl). Both parity
cases now loud-fail with the expected diagnostic and no binary.

## Reproduce

`/tmp/wt_errhandling/` probes (Option `?` alongside Result `?`).

## Support and platform-gate update (2026-07-17)

The fail-closed boundary above is historical: `lower_try_expr` now supports
authoritatively typed flat and boxed Option locals/direct-call returns.
Resolved-method provenance is source-implemented. A third durable fixture
exercises the existing unresolved-method symbol-return path through `?`; it
does not guess a type for genuinely unknown late dispatch. The fixtures use
ordinary present payloads `5`, `4`, and `6`; payload `3` is deliberately
excluded because treating its collision with the flat nil sentinel as success
would encode the remaining ABI bug.

Hosted Linux/macOS/Windows and FreeBSD x86_64 select all three
native-authoritative cases under flagless LLVM and explicit Cranelift. ARM32
default LLVM and Windows ARM64 LLVM/Cranelift require successful nonempty target
objects and reject the retired fail-closed diagnostic. Static portability
coverage pins backend selection and the target-object contract. Execution is
pending; the payload-3 collision and uniform tagged Option ABI remain open.

The exact open ABI matrix is preserved in
`test/fixtures/compiler/native_option_uniform_tagged_abi_repro.spl`. It covers
raw and explicit `Some(3)`, raw and explicit absence with `unwrap_or(777)`,
raw/explicit `Some(0)` controls, annotated locals and aliases, typed calls,
provided/defaulted fields, direct and function-value calls, and Option-valued
`if`/`match` control-flow merges. Set
`NATIVE_OPEN_BUG_REPROS=1` on the native parity harness to run it under default
LLVM and explicit Cranelift; expected output is
`3377777700333777033777377737773777`. It stays opt-in until both backends pass the
current-source incremental run.

## Incremental tagged-return slice (2026-07-18)

The first no-bootstrap migration slice now uses one `i64` Option handle,
reserved enum id `1`, and ordinal `Some = 0` / `None = 1` for explicit
constructors and typed function returns. Direct-call return provenance marks
those handles so `unwrap`/`unwrap_or` extract `rt_enum_payload` without
double-wrapping or decoding raw `0`/`3` payloads as tagged integers.

The C, pure-Simple, Rust, and freestanding predicate owners now classify only
the raw nil sentinel or `(enum_id=1, discriminant=1)` as None. LLVM declarations
use the portable `rt_enum_new(i32, i32, i64)` ABI, and the new Rust LLVM emitter
reuses that API instead of nonexistent `rt_option_some`/`rt_option_none`
symbols. Focused Rust Option-map and C runtime contracts pass incrementally.

Typed lets, assignments, returns, parameters, and struct fields now share the
same promotion helper. Its unproven-local path is runtime-idempotent, which
also handles Option-valued control-flow merges without double-wrapping.
Focused runnable checks cover the Rust MIR interpreter's canonical encoding,
raw-bool `Option.map`, and pure-runtime rejection of raw 4097/-7 heap-tag
collisions without a crash. The strict dual-backend fixture remains opt-in
only until its current-source incremental LLVM and Cranelift executions pass.
