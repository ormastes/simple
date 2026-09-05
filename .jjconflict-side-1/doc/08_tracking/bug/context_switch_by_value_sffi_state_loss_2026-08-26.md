# Context-switch SFFI saves into by-value copies

## Status

Open correctness and ABI design blocker. The affected ARM32, ARM64, RV32,
x86-32, and x86-64 context-switch methods must not be promoted to safe APIs.

## Evidence

Each method accepts `from_ctx` and `to_ctx` by value, takes the address of those
locals, and passes the addresses to a raw assembly provider. A provider can
load the target copy, but saving into the source copy does not establish that
the scheduler-owned context is updated after the suspended task resumes.
Several target declarations also lack maintained interpreter/native registry
closure and exact artifact admission.

## Required fix

Define one compiler-owned context ABI with exact layout/alignment hashes and a
non-returning restore contract. The switch surface must accept a stable mutable
owner for the source context and a stable borrow for the target, prove both
addresses remain live and aligned across transfer, and update every scheduler
caller. Providers must be target assembly objects admitted by exact artifact
digest; hosted lanes must reject the operation rather than fabricate a return.

Until that migration is complete, raw declarations, calls, and public wrapper
methods require `unsafe(ffi, raw_ptr)` authority. Unsafe tagging records the
unresolved obligation; it does not repair or verify state persistence.

## Performance constraint

The corrected switch remains O(1), allocation-free, lock-free, and direct. Do
not add per-switch hashing, signatures, symbol lookup, generic marshalling,
context copying, or heap indirection. Validate layout/artifact identity once at
admission and alignment/lifetime when the scheduler-owned context is created.
