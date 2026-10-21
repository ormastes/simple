# Scoped public text-hash workaround for producer645

Actual failure: `canonical-batch27/unit-12` compiles
`src/lib/nogc_sync_mut/src/hash.spl` through the public LLVM object path and
reports unresolved method `hash` at line322:5 inside `hash_text_fnv1a`.
Source SHA256 is
`100aed3f6bc8efd3d0f5cedd92ed514a6a70a690af487d2d141de3fa701545ad`;
launch source head is `01be9cb018ca786feb827b95f7ff0e2e0df7f17b`.
Producer SHA256 is
`645e62a815d076d77a61b01daa6e86c1330632686c18ce4c56cccd860a4a714a`;
exact runtime/options and original diagnostics remain in that job's launch,
outcome and stderr receipts. Failure checkpoint SHA256:
`36ffd28ff41db9f9374c0a1e6c3761e3949908ac74965f1f3ff4a806d2ccf571`.

The same source declares `Hash for text` at lines59–75, but producer645 does
not resolve the public wrapper's `s.hash()` call. This establishes an actual
primitive trait-method resolution failure at that boundary, not its internal
compiler root cause. See existing
`doc/08_tracking/bug/primitive_receiver_trait_impl_dispatch_2026-08-07.md`.

Smallest scoped workaround: replace only the wrapper body with the exact
existing bytewise FNV-1a loop, preserving signed offset, wrapping multiply,
byte order, empty input, public signature and facade alias. Leave the trait
implementation and method resolver unchanged. This is not a compiler fix.
The exact existing bug ID is tagged in the candidate body; duplication is
temporary and must be removed after the compiler regression passes.

Compiler fix plan: reproduce the smallest same-module primitive `impl Hash
for text` plus wrapper `s.hash()` fixture through actual parser/HIR/MIR,
retain resolved receiver type/trait owner/symbol and first missing method
lookup boundary, then repair that compiler resolver owner. Regress both the
physical family import and configured `std.hash` facade without pinning a
different library family. Confirm known byte vectors through method dispatch
with actual interpreter and native LLVM/Cranelift producers before removing
the workaround; preserve negative unresolved-method diagnostics. The exact
resolver root cause is not established by this source workaround.

Regression candidate asserts independent signed-i64 vectors for empty, `a`,
`hello`, `foobar`, embedded zero and UTF-8 `é`, through the real public
function and existing facade alias. Existing `.hash()` regression remains
separate and unsupported on this producer; it must not be marked passing.
Expected constants were independently calculated with unsigned64 FNV-1a
arithmetic and signed64 conversion; runtime tests remain UNRUN.

All candidate artifacts are external. No live source, cache, worktree or
producer was modified. Application and native regression belong to the
operator after the active GEN3 input lease ends, with fresh source identity.
