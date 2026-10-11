# `mutex_lock` return-only generic requires an explicit call type

## Evidence

The Phase 3 native-build receipt at
`/dev/shm/simple-phase3-1000-object-attempt-20261010/execution-receipt.json`
records E-MONO-032 and E-MONO-033 for rows 2 and 3, compiling
`src/app/build/targets/action_identity.spl` and
`src/app/build/targets/artifact_receipt.spl`. Both fail at
`src/lib/nogc_sync_mut/rt_hal/boundary.spl:138:16` because the call has no
explicit type argument and its argument types do not determine the generic
result type.

The declaration in `src/lib/nogc_sync_mut/concurrent/mutex.spl` is
`fn mutex_lock<T>(mutex: Mutex) -> T?`. `Mutex` is not parameterized by its
stored value type, so `mutex_lock`'s only input cannot determine `T`. The
boundary lock is initialized by `mutex_new(0)` and all unlock paths restore
`0`; the supported protected value here is therefore `i64`.

## Minimal reproduction and prevention

```simple
val lock: Mutex = mutex_new(0)
val held = mutex_lock(lock)       # E-MONO-032: T appears only in the result
val held_i64 = mutex_lock<i64>(lock)  # explicit, contract-matched type
```

Keep the generic API for callers protecting arbitrary values, but provide a
type argument (or a typed result context where supported) when the protected
value cannot be inferred from an argument. The boundary call now states
`mutex_lock<i64>(owner_install_lock)` and carries an `@workaround` tag linking
this source-level finding. Standalone positive, negative, and non-sentinel text
controls are recorded in
`test/fixtures/compiler/mutex_lock_typeargs/manifest.json`; all remain
unexecuted. No compiler behavior change or native PASS is claimed by this
report.

## Linux ARM Stage 2 verification recurrence

The release `03acdb2a8c37afe108a3a66ea961cef18b6b1763` Stage 2 compiler
test-runner prerequisite passed HIR for all 217 modules, then failed with
E-MONO-032 at `mcdc/dynamic_probe.spl:227:16` and other calls using the same
lock. `_mcdc_dynamic_install_lock` is initialized with integer zero and every
unlock restores zero. All eight return-only generic calls now explicitly use
`mutex_lock<i64>`, matching the existing boundary repair and retaining lock
acquisition, nil checks and unlock order.

Native regression entry:
`test/fixtures/compiler/mcdc_dynamic_lock_sentinel.spl`. It calls the real
dynamic controller with an empty owner set, expects rejection and exit zero.
Its import closure exercises the actual MC/DC owner and generic lock calls.
Native ARM verification failed with the explicit source edit: the canonical
entry-closure build passed all 13 HIR modules but still reported eight
E-MONO-032 calls with no explicit type arguments and E-MONO-033. The changed
line positions confirm that the edited source entered the build. The explicit
call type is therefore an unsuccessful repair with this producer, not a native
PASS. Investigate where call type arguments are lost before monomorphization.
RISC-V verification remains pending; no Phase 3 or compiler-test admission is
claimed. Evidence: `build/native_probe/verifier-worker-budget/dynamic-arm-canonical.log`.

## Explicit-call type loss located

`core/parser_expr.spl::try_skip_ident_generic_args` consumes the type tokens
only for syntax disambiguation. Both bare-identifier postfix paths call it
without storing type arguments. `ExprKind.Call` then reaches HIR lowering
without that metadata; `expression_core.spl` constructs `HirExprKind.Call`
with an empty type argument list. This is a concrete compiler defect, not
an incorrect sentinel type. Preserve explicit type arguments through the flat
AST, bridge, AST and HIR call pipeline in a follow-up compiler repair.

The MC/DC calls additionally declare `held: i64?`, matching the actual protected
value. Monomorphization already supports expected-result context on `Let`.
Native ARM verification of this typed-context attempt also failed with the
same eight unresolved calls (see `dynamic-arm-context.log` beside the prior
evidence). Neither edit is a verified repair; investigate whether local type
annotations survive into the monomorphizer as well as preserving explicit
call types.

## Bounded diagnostic trace and next repair boundary

The third native investigation enabled `SIMPLE_MONO_DIAG=1` on the same
typed-context source snapshot. It terminated with the same eight unresolved
calls; it is diagnostic evidence, not another repair or PASS. The trace enters
`mcdc_dynamic_probe_controller_prepare_owners` with five statements and reaches
the edited call at line 135. Diagnostics serialize statement enum values as
addresses, so this trace cannot establish the initializer's HIR kind or the
expected-result type. Do not infer that annotations were lost solely from the
unchanged error message. The diagnostic producer is the runtime-bound native
compiler at `build/native_probe/named-variant-pattern/simple`.

A follow-up must preserve parsed explicit call types rather than silently
skipping them, prove exact HIR type arguments, and compile the real MC/DC
closure on ARM and RISC-V. Keep comparison disambiguation, nested type parsing,
const-generic rejection, AST reset/clone/cache transport and negative arity
controls intact. No stubs or monomorphization admission bypasses are acceptable.
The current call-site edits remain uncommitted and must not be presented as a
verified workaround.

Tracked upstream: https://github.com/ormastes/simple/issues/2847.

## Compiler repair candidate: flat transport

The isolated `fix/bootstrap-explicit-call-types-20261010` lane now adds
`expr_call_type_args` to the flat expression owner. Public getter/setter names
are `expr_get_call_type_args` and `expr_set_call_type_args`. Type handles are
stored separately from value argument expression handles, initialized for every
new node, cleared at reset, included in dump/restore and copied by AST cloning
without treating type handles as expression ids. The flat pool codec advances
from v3 to v4 to reject incompatible cached layouts.

This is preparatory source work only. Parser lookahead must retain confirmed
type arguments, bridge them into an AST representation, and HIR lowering must
forward lowered types into `HirExprKind.Call`. Semantic hashing and generated
visitor support must cover the AST representation. Direct generic calls,
comparison negatives, nesting, const-generic rejection, reset/clone/cache
transport, and real MC/DC ARM/RISC-V compilation remain acceptance criteria.
Only diff whitespace checking has passed; no native build or runtime test of
this compiler candidate is claimed. The earlier call-site edits remain
unverified and separate from the compiler transport mechanism.

## Compiler repair candidate: parser to HIR

Confirmed generic lookahead now returns parsed type handles using the normal
type parser after restoring its checkpoint. Comparison rollback and the
existing const-generic diagnostic remain intact. Both direct-call postfix
paths attach those handles to the call node and clear pending metadata after
the first call, so a later chained invocation cannot inherit it. The bridge
converts the handles into `Expr.explicit_call_types`; HIR lowers them into the
Call type-argument list. Member and receiver generic specialization remain
separate existing boundaries; no new qualification of them is claimed.

Added `explicit_call_type_arguments_spec.spl` with a real parser/HIR integer
type assertion, plus return-only positive and negative arity native entries.
These are authored, unexecuted tests. Generated AST traversal and semantic
hash output must be refreshed before admission.

The historical `bin/release/aarch64-unknown-linux-gnu/simple` identifies itself
as a Rust seed despite its release-path name. An attempted generator run failed
on current Windows process source syntax and is not verification evidence.
No further normal-tool use of that executable is permitted. Instead the
current bootstrap seed is building a pure-Simple schema tool as a bootstrap
preparation product; the log is retained at
`build/native_probe/explicit-call-types/schema-build.log`.

Schema-tool bootstrap terminated with timeout status 124 after 180 seconds,
without producing an executable. This is tracked in
`compiler_schema_native_bootstrap_timeout_2026-10-10.md`. Parser/HIR changes
and authored tests remain unverified; generated traversal and semantic hash
refresh is still required.

## Native compiler candidate preparation

The schema tool is now built and executed as a pure-Simple native bootstrap
product. The default-field scanner was corrected so `[Type] = []` means a
node-bearing `[Type]` field. Regenerated AST traversal walks explicit type
nodes and semantic hashing encodes their contents. Generator review also
retains fail-closed uncacheability for opaque BlockValue arena handles, instead
of treating handle ids as stable semantic integers. Generated output assertions
pass; artifacts come from the actual generator, not handwritten generated code.

The initial compiler rebuild compiled 1194 modules with zero build failures
in 97.4 seconds. A subsequent generator-semantic correction rebuilt three
modules and reused 1191 with zero build failures. These are candidate builds,
not a Phase 3 admission. The first native return-only probe was refused before
HIR because this auxiliary compiler omitted the canonical K1 composition
source root. The diagnostic build is being corrected with
`--source src/compositions/kernel_llvm_cranelift`, policy llvm-cranelift and
plugin policy simple-sdn. No refusal was disabled and no generic-call PASS
has yet been established. Logs live under
`build/native_probe/explicit-call-types/`.

The corrected K1-bound compiler build completed in 101.2 seconds: 1217
compiled, zero failed, linked with the canonical bound runtime. The direct
return-only generic probe is now executing through this producer. Its result
is pending; the prior missing-composition failure is retained separately.

## First generic-call codegen evidence

The K1-bound producer compiles the return-only integer/text fixture with
`generic_fns=1 call_sites=2 specializations=2 unresolved=0`. Its ARM object
header is EM_AARCH64 (183). Building the executable succeeds, but execution
crashes at address 0x3 while handling optional nil results, without success
output. This is tracked in
`native_return_only_generic_optional_nil_crash_2026-10-10.md`. Native execution
is FAIL; the disappearance of unresolved-generic diagnostics establishes only
monomorphization/codegen progress, not full qualification or a release PASS.

## Real MC/DC closure after explicit type transport

The new producer reaches monomorphization with 11 generic functions, 32 call
sites, two specializations, and zero unresolved generic calls. The original
eight mutex errors are cleared. The closure then fails MIR lowering on
`saturated`, `evaluation_at`, and `record`, called through optional class
payloads. Evidence: `build/native_probe/explicit-call-types/mcdc-arm.log` in
the isolated repair worktree. No MC/DC native execution or Stage 2 test-gate
PASS is claimed.

## Dynamic-library exclusion gate callers (2026-10-11)

The Caret build on release `f689e209d` reports six additional E-MONO-032 call sites in `dynlib_lifetime_owner_v1.spl` and `dynlib_snapshot_registry_v1.spl`. All discard the protected value and unlock with integer sentinel `0`; they therefore use the existing runtime-equivalent `mutex_lock_gate` entry. This repair preserves Simple-owned state, the same native lock handle, and the same unlock calls. Execution and full compiler/lib/MCP gates remain pending; source review and whitespace checks alone are not qualification.
