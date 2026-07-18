# native-build: `?` on `Option` silently miscompiles (treated as `Result`)

**Severity:** high (silent-wrong on BOTH oracle and native — no diagnostic)
**Found:** 2026-07-14, errhandling lane
**Status:** typed local/direct-call support implemented and execution-verified on native-build `--entry`; method-call support also implemented and verified for a method call whose RECEIVER has a statically recoverable declared type (a typed local/parameter) — chained calls and receivers with no recoverable static type still fall through to the Result decoder unrecognized; uniform tagged Option ABI (payload-3 collision) remains open
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
raw and explicit `Some(3)`, raw and explicit absence with `unwrap_or(777)`, and
raw/explicit `Some(0)` controls. Set `NATIVE_OPEN_BUG_REPROS=1` on the native
parity harness to run it under default LLVM and explicit Cranelift; expected
output is `3377777700`. It remains opt-in and red until all typed boundaries
share the uniform tagged representation.

## Regression re-fixed: resolved method-call Option try silently wrong again — root-caused + fixed + execution-verified (2026-07-18, P4 lane)

Reproduced with the exact repro this lane was assigned: native-build (stale
deployed seed, `native-build --entry`, no `SIMPLE_BOOTSTRAP`) of
`test/fixtures/compiler/native_option_try_unresolved_method_loud.spl`
(`source.maybe()?` where `maybe` is an ordinary struct method returning
`i64?`, expected value `6`) printed **`0`** with `rc=0` and no diagnostic —
the exact silent-wrong-value class this bug tracks, on a case the doc had
previously marked fixed.

**Root cause (regression, not a new defect):** `8b332df02b9` ("fix(mir):
reject resolved Option method try", 2026-07-16) added a
`case MethodCall(_, _, _, resolution):` arm to `enum_match_expr_type` in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` so a `?`
applied to a method call's Option return type would be recognized (at the
time, to fail closed; after `44cc66f0339` it feeds the real flat/boxed
decode path instead). The very next day, `ae57d190640` ("fix(compiler):
mirror seed struct-init order/nil-fill and Result/Option receiver fixes
into self-hosted compiler") — an unrelated struct-init-field-order fix —
included a hunk that silently deleted that 3-line arm as collateral damage
in a larger diff. No spec caught the loss: the source-contract spec that had
pinned the arm's exact text was itself replaced (by the same-era rewrite that
turned the old fail-closed guard into real Option decoding) without carrying
the assertion forward, so `option_variant_order_source_spec.spl` kept passing
with the arm gone. Confirmed via `git log -S"case MethodCall(_, _, _,
resolution)"` (only those two commits touch that string) and by reverting to
HEAD, rebuilding the fixture, and observing the wrong `0` reappear.

**Deeper finding — the reverted arm alone would not have been sufficient:**
restoring `8b332df02b9`'s exact 3 lines still produced `0` after rebuild.
`resolution.get_symbol_id()` is only non-nil once a type-inference pass
mutates `MethodResolution` from `Unresolved` to a resolved variant
(`src/compiler/35.semantics/resolve_strategies.spl`), but HIR lowering always
constructs `MethodCall` with `MethodResolution.Unresolved`
(`20.hir/hir_lowering/expressions.spl`), and native-build's `--entry` fast
path never runs that inference pass — `method_calls_literals.spl`'s own
docstring says as much, and it resolves the same calls a different way: a
name-keyed `self.struct_method_syms["StructName::method"]` map built at
HIR-lowering time. `enum_match_expr_type`'s `MethodCall` arm now mirrors that
second path as a fallback: recover the receiver's *declared* type (only for a
bare `Var`/`NamedVar` receiver — the exact shape `source.maybe()?` needs, `source`
being a typed parameter) via a new narrow helper, `receiver_declared_type`,
extract the struct name, and look up
`struct_method_syms["{struct_name}::{method}"]` when `resolution.get_symbol_id()`
comes back nil.

**New-crash finding, fixed before landing:** the first draft of the fallback
recovered the receiver type by recursing into `enum_match_expr_type(receiver)`
itself, and separately by mutating a `var receiver_type: HirType? = nil` across
match-arm branches and re-narrowing it with `if val found = receiver_type:`.
Both drafts built the target repro correctly but broke a *different*,
previously-working program: `match Src(v: 9).get(): case Ok(x): print(x) ...`
(a method call on a struct-literal receiver, `.get()` returning
`Result<i64, text>`) went from printing `9` to a hard build failure,
`error: semantic: undefined field 'kind': cannot access field on value of type
'nil'`, with zero code path logically reaching a nil dereference (traced by
bisecting the new code line-by-line against this exact case — see commit
history on this file). Root cause of *that*: `if val bound = <var>:` does not
reliably re-narrow a mutable `var`-declared `Optional` in this compiler/seed
pairing — `bound` can still be treated as unwrapped-to-nil, and the next
`.kind` access then dereferences nil. The fix avoids the pattern entirely:
`receiver_declared_type` is a plain helper that returns via `return Some(...)`
or falls through to a trailing `nil` (the same proven-safe idiom the adjacent
`Var`/`NamedVar` cases in `enum_match_expr_type` already use), and the call
site consumes it with the pre-existing `if x != nil: val found = x ?? ...`
idiom (mirroring the existing `Call` case), never `if val x = <var>:`. Also
recorded as a standalone landmine: prefer `val`-bound/return-based Option
narrowing over mutating a `var` across a match's branches in this codebase.

**Fix:** `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` —
`enum_match_expr_type`'s `MethodCall` case restores the `resolution`-based
recovery and adds the `struct_method_syms` name-keyed fallback via the new
`receiver_declared_type` helper described above.

**Verification (stale deployed seed
`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`,
`native-build --entry ... --clean`, `env -u SIMPLE_BOOTSTRAP
SIMPLE_NO_STUB_FALLBACK=1`):**
- `native_option_try_unresolved_method_loud.spl` (the regressed case): `0`
  (wrong, pre-fix) -> `6` (correct, post-fix).
- No regression on the neighboring matrix: `native_option_try_annotated_loud.spl`
  -> `5`, `native_option_try_direct_loud.spl` -> `4`, and a Result `?`
  cross-check (`leaf_ok`/`leaf_err` forwarding, mirroring
  `write_case_result_try` in `scripts/check/check-native-seed-parity.shs`)
  -> `8boom` — all unchanged and correct.
- No regression on `match <StructLiteral>.method(): case Ok(x)/case Some(x):
  ...` (the case that caught the first-draft fallback's crash, see above):
  `match Src(v: 9).get(): case Ok(x): print(x) ...` -> `9` (builds clean, no
  crash); `match Src(v: 11).maybe(): case Some(x): print(x) case nil: ...` ->
  `none` — unchanged from the pre-fix/pre-regression baseline (this specific
  flat-Option-via-match misread is a separate, pre-existing issue, not touched
  by this fix; out of scope here).
- `test/01_unit/compiler/mir/option_variant_order_source_spec.spl` (extended
  with source-content assertions pinning both the `resolution.get_symbol_id()`
  path and the new `struct_method_syms` fallback so this exact arm cannot be
  silently dropped again) run via the stale seed's `test` subcommand: 4
  examples, 0 failures with the fix; 1 failure (the new assertion) with the
  fix reverted, confirming the guard is load-bearing.

This closes the resolved-method-call flavor of the bug again (with a
regression-proof spec this time). The interpreted/oracle path was not
in scope for this pass (the fresh self-hosted `bin/simple run` currently
errors out unrelated to this bug — a lint diagnostic on explicit `self.`
usage in a different, pre-existing native-build regression — and the stale
seed's own `run` prints no output for this fixture either; neither was
usable as a clean oracle here). The uniform tagged Option ABI (payload-3
collision) remains the one genuinely open item.

**Scope note:** this fix is entirely in the *type-gating* layer
(`enum_match_expr_type`) that decides whether `lower_try_expr`'s Optional
decode arm runs at all for a given `?` base — it does not touch the decode
mechanics themselves (the None-vs-Some discriminant check or the Some-payload
slot/offset read, `try_opt_boxed`/`try_opt_flat`/`rt_enum_payload` in
`lower_try_expr`). Those were already verified correct once reached (this pass
empirically confirmed `try_opt_flat`/`try_opt_boxed` decode the right value —
output `6`, `5`, `4` above — the moment the resolved-method-call arm makes
them reachable). The regression fixed here is that a resolved method call's
Option return type was silently un-recognized so the base fell through to the
*unconditional Result decoder* instead — a wrong-decoder selection, not a
wrong offset inside the right decoder. The one place an actual payload-slot
ambiguity remains is the documented, separate, and still-open uniform tagged
Option ABI item (raw payload `3` colliding with the None sentinel) above.
