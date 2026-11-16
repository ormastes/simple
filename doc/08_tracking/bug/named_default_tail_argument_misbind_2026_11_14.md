# Named arguments skip omitted defaults and bind the wrong slot

Status: waiting for repaired-compiler verification; source-only repair accepted
by Astra. Severity: P1 silent wrong value. No full repair landing authorized.
Owner: codex-named-tail-20261114. Date: 2026-11-14.

Actual native RED is retained at
`/home/yoon/dev/simple-runtime-value-arity-20261114/build/target-profile/named-tail-minimal`.
Producer SHA256: `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
Its receipt records the exact immutable producer path and command. Compile
succeeded in 5.161 seconds, peak tree RSS 77459456 bytes; the executable returned
1 because `named_tail("head", q: "sentinel")` returned an empty string. The
function declares one required text parameter followed by sixteen defaulted
text parameters, ending in `q`. The explicit all-positional cache identity
probe succeeds; this is not a wide ABI limit.

The actual call-lowering owner evaluates free-call arguments in source order
and also passes them in that order. HIR checks names but does not normalize
the argument slots. MIR then appends defaults after the supplied operand count.
The named tail value lands in the second parameter and the tail gets its
default. The same mechanism affects middle slots and smaller arities.

Repair must retain source-order evaluation of supplied expressions, bind each
operand to its declared slot, and evaluate defaults only for missing slots in
declaration scope. Duplicate/unknown names and missing required slots must be
diagnosed before argument effects. No signature expansion or positional-only
caller workaround closes this bug. Existing declaration-default remapping,
type coercion, ownership, generic inference and extern ABI adaptation remain
owned by their established lowering paths.

Required evidence: small middle/tail cases, reversed named effects, typed
parameters and declaration-scoped defaults, negative duplicate/unknown/missing
cases, and a native real-call fixture. Projection execution alone is not a
rebuilt compiler or full bootstrap qualification. No fix or closure claimed.

## Bounded repair evidence

The actual new slot planner source was copied byte-for-byte into a tracked
private Git projection, then compiled and executed with the same pinned pure
producer. Compile exit 0, run exit 0, 4.941 seconds, peak tree RSS 77918208
bytes. Sparse/reversed mappings and duplicate/unknown/missing/excess rejection
passed. Planner SHA256:
`20ad33841eb8beeaec5d2cbcdb62eb03a9625ed258929f5432ca4e4b81f2855d`.
Receipt and logs:
`/tmp/simple-named-default-tail-20261114/build/named-default-slot-evidence/`.
An initial source-admission rejection from an untracked projection root is
retained separately; the retry corrected provenance without changing source.

This is planner evidence only. It does not execute the edited compiler's MIR
integration or demonstrate argument evaluation order at a real repaired call.
The full-call regression fixture remains UNRUN on a repaired compiler. The
declaration repository path uses the existing declaration-scoped default
frame. The legacy bootstrap path permits only scope-free primitive literals
for omitted named-call defaults; other defaults fail before supplied argument
lowering instead of borrowing caller lexical identities. Omitted defaults on
foreign/runtime calls are explicitly refused pending ABI qualification.
Existing HIR restrictions on some mixed positional/named calls remain intact;
this patch does not claim complete named-call language coverage or new method,
variadic, spread, or indirect-call support.
