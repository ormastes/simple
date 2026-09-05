# Secure-memory interpreter raw-pointer aliasing

**Status:** Open
**Date:** 2026-08-24

## Failure

The interpreter previously rejected `rt_memory_barrier` as an unknown extern.
After registering the native-equivalent acquire, release, and sequentially
consistent barriers, the credential zeroization specification reaches the
foreign volatile writes but the caller-visible packed byte array is unchanged.

Measured interpreter evidence for
`credential_zeroization_spec.spl --mode=interpreter`:

| State | Result | Elapsed | Peak RSS |
| --- | --- | ---: | ---: |
| Before barrier registration | 3/6 pass; two unknown-extern failures | 22.79 s | 175,232 KiB |
| Barrier registered | 3/6 pass; zeroization assertions fail | 21.01 s | 178,528 KiB |
| Direct packed `data_ptr` experiment | 3/6 pass; zeroization assertions still fail | 20.68 s | 177,808 KiB |

The remaining authentication failure is pre-existing and independent of the
two zeroization assertions.

## Root cause boundary

Interpreter packed arrays use `Value::ByteArray(Arc<Vec<u8>>)`. Exposing
`Vec::as_ptr()` and writing through it is not a sound mutable API: shared `Arc`
aliases exist and Rust has not granted mutable access to the allocation. A
method-only fast path avoids the old O(n) widening allocation, but does not
repair ownership or mutation propagation and therefore is not an acceptable
fix.

## Required fix

Add a compiler-owned mutable byte-array operation that:

1. identifies and updates the caller's actual place rather than a cloned value;
2. obtains exclusive storage through the interpreter's normal write-back path;
3. performs one O(n) volatile wipe with no per-element allocation;
4. returns a typed report/status while preserving boolean semantics;
5. keeps raw pointers inside the runtime boundary;
6. has differential interpreter/native coverage and allocation evidence.

Until that exists, interpreter secure zeroization is not verified and must not
be advertised as a safe foreign-pointer wrapper.
