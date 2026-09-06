# Stage 3 aggregate copy dereferences an unregistered tagged receiver

**Date:** 2026-08-15
**Status:** codegen fix present; focused/static verification and canonical retry pending
**Area:** Rust Cranelift/LLVM aggregate-copy lowering used to build the admitted
pure-Simple compiler

## Exact retained failure

The correctly routed Stage-3 recovery used admitted Stage-2 compiler SHA-256
`777846c39c688f192404f67ceb48ce8746e9e1309d0ce0482c9ec8b0300c0fef`.
It completed 604/604 parse files and emitted the terminal HIR progress event,
then exited 139 after 10m54.90s with 13,766,012 KiB maximum RSS. No Stage-3
candidate, hash, cache object, or sanity receipt exists.

The kernel retained the exact first fault:

```text
simple[879127]: segfault at 30 ip 00000000005e6eea
```

`0x5e6eea` resolves to
`MonomorphizationPass.scan_expr+0x263a`. The admitted binary disassembly shows
an `rt_struct_alloc(0x30)` followed by an aggregate-copy source check that tests
only low tag `1` and a nonzero masked payload. Source value `0x31` therefore
passes, masks to `0x30`, and faults at `mov (%rcx),%rsi`. This is not the old
registry-cap failure: the destination allocation succeeded.

Retained evidence:

- `build/native_probe/stage4-owner-20260815/canonical-stage3-routing-registry-fix-v2.{log,status,time}`
- `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- `build/bootstrap/bootstrap-build-progress.events`

## Root cause and bounded fix

Both Rust aggregate-copy emitters treated `tag == 1 && payload != 0` as proof
that the source was a live struct allocation. Scalar/special values can share
those low bits. The runtime already owns the authoritative allocation registry
and range validator.

The Cranelift and LLVM emitters now call
`rt_struct_receiver_valid(receiver, 0, copy_width)` before every source load and
before replacing a deep field with its recursive copy. The emitters explicitly
zero-initialize the fresh fallback words before any selected load because the
native runtime authority uses `malloc`. Invalid sources therefore produce a
zero-filled fresh block at the top level and preserve the original deep-field
word; no unregistered or indeterminate address is read. No production runtime symbol
was added. Repo-wide inspection found no pure-Simple `AggregateCopy` lowering;
its current struct constructor path is separate and already guards field
receivers.

The bad `0x31` value originated while scanning an `If`/nested `HirBlock.value`
path. This fix closes the unsafe dereference, but does not claim that the
upstream value is semantically correct. The next canonical Stage-3 receipt is
the arbiter; a later diagnostic must preserve that value's owner rather than
weakening HIR validation.

## Acceptance

1. Static/source-shape coverage proves both Rust backends use the full runtime
   receiver-range validator for shallow and recursive copies.
2. Rust formatting/type checks pass for the changed emitters.
3. A refreshed-manifest full-bootstrap republishes the Rust authority and
   admits Stage 2.
4. Exactly one cache-preserving canonical Stage-3 recovery advances beyond the
   retained fault; on failure, retain the new exact first diagnostic/IP.
