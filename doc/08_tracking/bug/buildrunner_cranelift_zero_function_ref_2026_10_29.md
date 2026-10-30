# BuildRunner native emission supplies an invalid Cranelift function reference

Status: OPEN; Astra owns diagnosis, Lunar owns bounded native execution.

After the receiver-type and public-static corrections, recovered P2 reaches
307 successful MIR and AOP modules for the current BuildRunner entry. Native
emission repeatedly reports `cranelift: call missing func-ref handle 0`, then
the Cranelift verifier aborts. The coordinator returns 1 and publishes no
manager. The former non-public-static diagnostic is absent.

Producer SHA-256: `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
Source head: `199575f07beb67c7a5ab80aed6124cf8dfefb47d`.
Log: `/private/tmp/lunar-buildrunner-manager-20261029/buildrunner-final-sixth.log`.
Log SHA-256: `4fee15a6bb5c0e43d20e5891aef43f8829db56d822572811e669c4042ff2aea1`.

The last progress line names `lib.common.bytes.span`, but that is the first
uncached module, not evidence of the failing module. Subsequent object files
exist; the latest observed file is `lib.common.binary_inspect`. The queue
marks the entire crashed worker's ownership set failed. Neither observation
identifies the failing function.

The current SFFI declaration function discards Cranelift declaration errors
through `.ok()`. Its import function returns zero for absent declarations or
builder/module state. Pure call helpers pass returned handles onward without
identifying which preceding operation failed. These are investigation points,
not an established root cause. The producer statically links this runtime;
replacing a runtime archive does not modify the running compiler.

PR5290 preserves local function definitions in the Rust compiler's separate
instruction-context map. It does not change the active builder function-ref
registry that emitted this diagnostic. Its relevance is unproven. The internal
`run src/app/cli/native_build_worker.spl` CLI path dispatches a compiled worker
entry; it does not interpret changed compiler source.

The initial six-build diagnostic budget ended without an artifact. The user
then explicitly authorized twelve hours of continued work. The next diagnostic
requires debugger coverage of the actual native worker, retaining declaration
names and the first zero-handle call stack. A standalone ByteSpan native probe
passed under LLDB; it does not reproduce the full-closure failure.

Acceptance requires a precise reproducer, correction in the responsible owner,
adjacent regression evidence, successful current manager emission, and actual
strict BuildRunner execution. No seed-only test or direct compiler Hello
substitutes for that production path.

## Diagnostic boundary correction under review

The bridge now retains the actual declaration error and identifies module,
symbol, signature handle, signature shape, and linkage in stderr. Import
failures distinguish a missing declaration, active context, function builder,
JIT module, or AOT module. The exported ABI still returns zero on refusal;
no permissive fallback or altered function mapping is introduced. Successful
calls do not format diagnostic strings.

Three authored Rust bridge tests exercise conflicting i64/f64 declarations,
successful import of the valid original after that refusal, missing declaration
versus missing context, and missing signature versus missing module. These
tests passed on Linux arm64 after correcting the assertion for Cranelift's
uppercase `types::I64`/`types::F64` debug names. The original manager root cause remains OPEN;
the change makes a matching rebuilt producer report the earlier failure instead
of losing it at `.ok()`.

Debugger diagnosis did not establish codegen coverage. Attaching to the owned
MIR child caused a wait-error/kill sequence before declarations; substituting
a launcher through `SIMPLE_BINARY` was refused by producer identity checks.
No interposition or ownership bypass is used. A canonical rebuilt producer
with the diagnostic bridge is the next route.

## Focused execution evidence

The first native Rust library run reported two passing tests and one failed
assertion: the diagnostic retained both types, but the test expected lowercase
names while the underlying Cranelift Debug representation uses uppercase.
The follow-up changes only that assertion and still requires both distinct
types. The repeated focused run exited 0: 3 passed, 0 failed, 4527 filtered.
Log SHA-256: `71c0dbd22830d278b5b646e27d366ecb078d9618b15ce469fc1e37a9cd83c313`.

Review-lane code is `d66bf7342672059c9f78b687c8736fd94c34582e` plus the test
assertion correction `77d6489cb49f6596e11896a7d22a6a82a1491180`. The Linux
execution head `f444b9d502cb65ae271d0818c960fc39e1a42bec` rebases these changes
onto current release source; this is bridge
regression evidence, not a native Simple compiler or manager admission. The
canonical producer rebuild and exact original manager diagnosis remain pending.

Linux test log: `/work/bootstrap-seed-20261029/cranelift-function-handle-tests-lib-rerun.log`
in the dedicated container.
