# LLVM suffix-match fallback binds an untyped receiver to any same-name user method (2026-11-08)

**Status:** open, P1. Root hazard behind `stage2_new3_native_build_worker_av_c01_2026-11-07`.

## Problem
When MIR leaves a name-dispatched method call whose receiver type is ANY (owner unknown), the LLVM
codegen fallback resolves it by leaf name + arity across the whole link closure. If exactly one user
method matches (e.g. `StrictSdnReaderV1.byte_at(offset)`), the call is bound to it directly, even
though the receiver may be a text, array or unrelated object. The callee then reads the receiver as
its own class layout and access-violates (c01: read at 0x48).

## Why the c01 fix is not enough
#7857 makes `text?.unwrap()` typed STRING, closing that one source of ANY receivers. Any other path that
yields an ANY receiver plus a colliding leaf name still silently miscompiles into a wrong direct call.

## Expected
A name-dispatched call on an ANY receiver must use runtime dispatch (or fail the build loudly), never
a static bind chosen only by leaf + arity. Suggested gate: bind statically only when the receiver's
static owner is known and matches.

## Repro
Single file: a class with `fn byte_at(offset: i64)` and a function whose receiver is ANY
(e.g. via an untyped unwrap on a pre-fix seed) calling `.byte_at(i)`; `native-build --backend llvm`
emits a direct call to the class method (SEGV / 0xC0000005).
