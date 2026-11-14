# Resident startup consumer seam

This is a source integration proposal. It grants no qualification and is not
evidence of a generated executable invoking the consumer.

## Existing compiler route

`compile_entry_point_c` in
`src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl` discovers
module initializers from actual user objects, calls the runtime initializer,
calls every module initializer, marks resident runtime readiness, and then
calls user main. The provider lane is adding a one-shot creation barrier and
unconditional window seal before main and returning startup failures.

`@export("C", name: "__simple_xray_resident_startup_v1")` is an existing
source attribute, carried by HIR/MIR export metadata. LLVM's
`_MirToLlvm/core_codegen.spl` records the authoritative export name before
emitting definitions and calls. A scalar `fn() -> i64` avoids an unqualified
aggregate ABI. Module names under `nogc_sync_mut.trace` are already on the
compiler-owned instrumentation exclusion list.

## Smallest fixture integration

1. The fixture imports the actual startup consumer/owner, so ordinary source
   closure discovery retains its implementation. It declares the fixed strong
   exported scalar startup function using the existing source attribute. Its
   source name also uses the compiler-reserved `__simple_xray` never-instrument
   prefix; the linked-profile review must verify the exclusion on the actual
   object, not infer it solely from an export string.
2. That function constructs bounded configuration and owner/key selection
   values in Simple source. These are requested behavior, never qualification
   evidence. No generated IR is patched and no native boolean grants admission.
3. The generated entry validates that the actual linked object closure contains
   the expected unique strong consumer export. Missing or ambiguous symbols
   fail; weak absence does not silently count as startup execution.
4. Entry takes control, begins the no-owned-spawn barrier, and records its
   native thread as the startup-window owner. It releases the control mutex
   while retaining the creation barrier, then calls the fixed consumer. The
   consumer uses the normal public facade, whose operations each acquire the
   control mutex and revalidate native window ownership. Entry reacquires
   control to end the barrier and unconditionally seals the one-shot window
   on every returning path, including paths with no consumer grant. The
   current ledger alone does not implement this thread-ownership protocol.
5. Public prepare registers the actual image and validates the loaded-image
   profile issuer under control ownership; it resolves the requested keys
   through the checked manifest and binds the exact prepared descriptor to
   that grant. Public start revalidates the same native issuer, startup thread,
   window phase, snapshot identity, descriptor and generation immediately
   before patching. A prepared handle by itself carries no patch authority.

The operation contract above is the proposed freeze; native symbol names are
pending provider ownership. The consumer must not accept a caller's
`qualified` flag or by invoking the native begin function from public main.
The retained snapshot identity in `XrayLlvmRegisteredImageV1.native_snapshot`
allows the future authority owner to bind the actual native snapshot rather
than copied build-ID text supplied by a caller. The structural integer itself
is forgeable and grants no authority by possession or secrecy; native retained
state must validate the association. The selection API does not expose it.

## Minimal real issuer prerequisite

The runtime must consume a compiler/link-owner qualification record derived
from an actual reviewed qualification receipt. The record identifies the exact
target, generated C/Simple ABI, compiler/runtime/LLVM-XRay components, runtime
thread-creation coverage, and permitted initialization/foreign-call closure.
The normal build must verify those immutable component and closure identities
before emitting the profile record. A source fixture cannot define its own
`qualified` constant or overwrite a reserved issuer symbol.

The native issuer additionally binds that admitted component profile to the
retained snapshot of this loaded image, its real build ID, validated semantic
map, and selected descriptor/generation. This is a runtime-issued association,
not an embedded self-hash of the final executable. Snapshot and profile
identity checks must happen under the same control owner as preparation and
start. A profile string, matching row schema, copied build-ID string or
creation-ledger result cannot stand in for the issuer.

No such reviewed component/profile receipt or issuer currently exists. The
next prerequisite is an independently executed generated Simple ABI/global
ownership probe plus the actual runtime thread-coverage and linked-closure
audit on the pinned compiler/runtime candidate. Those facts can support the
narrow profile record; they cannot be invented by an always-successful native
getter. No new always-deny getter is needed either: keep the existing public
closure until the real receipt consumer can be implemented.

## Startup-only lifecycle

The first admitted profile grants one startup activation only. After entry
seals the window, request_stop closes descriptor admission without calling
compiler-rt unpatch. Drain waits for descriptor pins, closes and polls channels,
and retains the armed sleds, handler, descriptor and maps. Logical release
invalidates the public session while preserving that resident state.

The separate adapter `request_recording_stop` now closes admission and keeps
the exact armed-site list in RECORDING_CLOSED state. The resident facade uses
this path; its Busy result preserves Active so closure can be retried. The
legacy quiescent stop still unpatches and is not used for normal resident stop.
New preparation, restart,
selection changes and repatching after startup remain unsupported. No startup
lease is recycled to authorize them. A later profile requires a separate real
quiescent owner before physical unpatch or reconfiguration.

Activation failure while the startup barrier is still held may roll back
patches under the still-valid startup authority; a failed rollback faults and
retains everything. Such a failure must prevent entry into user main. The
entry must seal the window before returning failure.

## Executable capture route after prerequisites

The ordinary driver builds the fixture and its strong startup export. In the
generated entry's owned window, that export invokes public prepare/start using
the admitted snapshot/profile issuer. User main executes selected real Simple
functions, then invokes public recording-stop, poll, drain and release. Tests
check actual entry/exit rows, canonical mapping, generation/context identity,
stale-handle rejection, loss reporting and retained-armed no-new-records after
stop. A second prepare/start must fail after the startup window is sealed.
The fixture must also fail before patching when the qualification record,
closure identity, snapshot association, thread ledger or startup ownership is
invalid. This route must use generated objects, not edited IR or a C-only
replacement observer.

## Explicit limits

The ledger proves absence of owned spawn attempts only. Every compiled runtime
creation route must participate; an idle/exited worker still prevents the
first pilot grant. Foreign and constructor threads require an actual qualified
closed-world linked profile. Runtime readiness, queue counts, metadata shape,
and the existence of the fixed export do not provide that qualification.

Until that issuer exists, startup attempts must return UnsupportedProfile
without activation. Executing that refusal through generated C and Simple is
ABI/order evidence only. Actual capture, generated global-carrier ownership,
resource bounds and all native acceptance gates remain separate requirements.
Generic compile-option trace metadata emission is subsequent work; the first
fixture's source configuration is an explicit narrow integration input.
