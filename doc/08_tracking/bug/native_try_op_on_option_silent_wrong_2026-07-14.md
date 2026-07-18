# native-build: `?` on `Option` silently miscompiles (treated as `Result`)

**Severity:** high (silent-wrong on BOTH oracle and native — no diagnostic)
**Found:** 2026-07-14, errhandling lane
**Status:** typed local/direct/method-call `?` support is source-implemented; the enum-id-1 Option migration now covers typed boundaries, true function-valued calls, and early `?` absence. The strict LLVM/Cranelift ABI matrix remains opt-in pending current-source execution; the separate `.?` consumer and legacy Cranelift generic-call shortcut remain follow-ups.
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
pending. The payload-3 producer collision is source-fixed by the enum-id-1
migration, but the full strict-dual ABI matrix remains opt-in until executed.

The exact open ABI matrix is preserved in
`test/fixtures/compiler/native_option_uniform_tagged_abi_repro.spl`. It covers
raw and explicit `Some(3)`, raw and explicit absence with `unwrap_or(777)`,
raw/explicit `Some(0)` controls, annotated locals/aliases, true function-valued
calls, parameters, returns, fields, `if`/`match` merges, and present/absent `?`
propagation. Set `NATIVE_OPEN_BUG_REPROS=1` on the native parity harness to run
it under default LLVM and explicit Cranelift; expected output is
`337777770033377703377737773777377737771`; the final `1` is the direct
`rt_enum_id(through_try(nil))` representation oracle, which distinguishes the
canonical None handle from legacy raw nil (`-1`). It remains opt-in until both backends
pass the current-source incremental run.

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
usable as a clean oracle here). The uniform tagged Option ABI was subsequently
source-migrated; its current-source strict-dual execution remains pending.

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
ambiguity was the documented uniform tagged Option ABI item above; the later
enum-id-1 migration removes that producer collision in source, pending its
strict-dual execution gate.

## Round-10 landing regression, fixed before re-land (2026-07-18, P4 lane)

Commit `affc31afd7d` above was dropped from the round-10 landing batch: the
coordinator's landing matrix hit
`error: semantic: method 'has' not found on type 'nil' (receiver value:
nil)` building `struct_field` (a struct with fields but NO methods —
`Point(x: 30, y: 41); return p.x + p.y`, the exact `native-smoke-matrix.shs`
case #6, rc 71) — i.e. every struct program, not just Option/method-call
ones, failed to native-build.

**Root cause:** the `struct_method_syms` fallback added in `affc31afd7d`
called `self.struct_method_syms.has(method_key)` unguarded. `struct_method_syms`
is declared as a plain (non-optional) `Dict<text, SymbolId>` field on
`MirLowering` (`mir_lowering_types.spl:105`) and is initialized to `{}` in the
constructors this lane inspected (`module_lowering.spl:82,425`) — but on the
coordinator's landing-matrix run it was still nil at the point
`enum_match_expr_type` ran for a struct with no methods, and calling `.has()`
on that nil field is a hard build-time error, not a graceful "key not found."
This lane's own local verification matrix (stale-seed `native-build --entry`
re-run of the full 19-case `native-smoke-matrix.shs`, including
`struct_field`) did **not** reproduce the crash — `struct_method_syms` came
back non-nil in every local run — so the exact nil-triggering condition
differs between this lane's environment and the landing pipeline's; the
matrix was too narrow regardless (it happened to never probe this field's
nil-ness directly) and is now widened per the fix below.

**Fix:** guard the same line with an explicit `!= nil` check, matching the
idiom already used everywhere else in this function (e.g. `if callee_type !=
nil:` in the `Call` arm) — `if self.struct_method_syms != nil and
self.struct_method_syms.has(method_key):`. When nil, the fallback is skipped
gracefully (same as the pre-`affc31afd7d` behavior for this shape) instead of
crashing. `option_variant_order_source_spec.spl`'s pinned-source assertion was
updated to match the new guarded line so it can't regress unguarded again.

**Verification (stale deployed seed
`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`,
`native-build --entry ... --clean`, `env -u SIMPLE_BOOTSTRAP
SIMPLE_NO_STUB_FALLBACK=1` unless noted):**
- Full `native-smoke-matrix.shs` (all 19 cases, `SIMPLE_BINARY=<stale seed>`):
  19/19 PASS, including `struct_field` -> rc 71 (own struct-with-no-methods
  case added to this lane's local checks too: `Point(x,y); return p.x+p.y`
  native-builds and exits 71).
- Original regression target still fixed: `native_option_try_unresolved_method_loud.spl`
  -> `6`.
- No regression on the rest of this lane's matrix: `annotated_loud`->5,
  `direct_loud`->4, Result `?` cross-check->`8boom`, `match Src(v:9).get():
  case Ok(x)`->9, `match source.label(): case Ok(s)` (Var receiver,
  `Result<text,_>`)->`hi`, `match Src(v:11).maybe()`->`none` (pre-existing,
  unrelated, unchanged).
- `test/01_unit/compiler/mir/option_variant_order_source_spec.spl`: 4
  examples, 0 failures.

**Honesty note on the guard's effectiveness (not just its safety):** every
verification above proves the guard is *safe* (no new crash, no behavior
change on any reachable path in this lane's environment) — it does NOT prove
the guard *fires*, because this lane could not reproduce
`struct_method_syms` actually being nil. Traced the field's only constructor,
`MirLowering.new_for_target` (`module_lowering.spl:60`), which
unconditionally sets `struct_method_syms: {}` (never nil) — every
`MirLowering` instance this lane's build creates, including the lambda-lift
child context (`lw = MirLowering.new_for_target(...)` at
`switch_operators_calls.spl:2230`, which then copies the parent's dict at
line 2240), starts non-nil. `!= nil` was chosen over the coordinator's
suggested `.?` because `.?` is this codebase's documented Option-unwrap
check (used on `Symbol?`/`HirType?` elsewhere in this same file), while
`struct_method_syms` is declared as a plain non-optional `Dict<text,
SymbolId>` — `!= nil` is the same idiom this exact function already uses
successfully for its other nil-checks (e.g. `if callee_type != nil:`) and is
a plain value comparison that does not depend on the field's static
optionality, so it should still correctly detect a genuinely-nil runtime
value if the interpreter's dynamic-typing leniency ever puts one there (a
documented interpreter-landmine class in this repo — see
`reference_interpreter_dict_and_value_quirks` — even though this lane could
not manufacture that exact condition from the constructor it could find).
**This guard has not been confirmed to fire in the specific case the
coordinator's landing matrix hit; only that it cannot make anything worse.
Please re-run the round-10 landing matrix against this new commit to confirm
`struct_field` (and the rest of the batch) actually passes there before
counting this closed** — if it still fails, the nil source is a construction
path this lane did not find, and the next lane should grep for other
`MirLowering(...)` struct-literal constructions or copy sites beyond
`new_for_target` and the one copy at line 2240.

Committed as a new SHA (see VCS log) for round-11 re-landing.

## Uniform ABI boundary follow-up (2026-07-18)

The expanded fixture exposed that its claimed function-value coverage was not
actually indirect: `through_function_value(f, value)` first promoted `value`
at that function's direct typed boundary, so the later `f(value)` never tested
a raw payload crossing a local function value. `lower_call` also discarded the
retained callee symbol's parameter types after classifying a local callee as
non-direct, so a real `f(3)` passed raw `3` and the callee mistook it for nil.
Parameter-type recovery now uses the retained symbol for direct and local
function-value calls, with the expression type as fallback.

The Optional `?` none block also emitted an early raw-sentinel return, bypassing
the normal function-return promotion. It now passes that nil local through
`ensure_option_handle` before terminating. The fixture uses genuine `f(3)` /
`f(nil)` calls and adds present/absent `?` propagation; the source contract
pins both lowering paths and the exact expanded output. A direct `rt_enum_id`
check makes the absent-`?` row representation-sensitive instead of relying on
`unwrap_or`, which intentionally accepts both canonical and migration nil. The matrix stays opt-in
until focused LLVM and Cranelift executions pass. A separate `.?` payload
consumer defect and the Cranelift adapter's legacy generic
`unwrap`/`unwrap_err`/`unwrap_or` identity shortcut are not claimed fixed here.
