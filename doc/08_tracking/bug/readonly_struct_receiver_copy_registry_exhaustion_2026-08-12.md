# Read-only struct receiver copies exhaust the receiver registry

Status: open, bootstrap blocking.

## Evidence

Build 8 admitted Stage 2 (`2a3ccce93e1d4f316d64194c732f0f7d759ea76d751bb33a9b226803e0dfebb5`) but Stage 3 crashed while parsing `driver.spl`. Its emitted `CoreLexer.peek` still calls `rt_struct_alloc(136)` on every invocation. Build 7 GDB evidence showed the struct registry at its 4,194,304-entry hard limit before that allocation returned null.

## Root cause

Both seed and pure-Simple MIR lowering defensively copy immutable by-value struct parameters. The implicit read-only method receiver is currently indistinguishable at the copy boundary, so hot accessor calls allocate registered aggregate copies that are never reclaimed during the call sequence.

Blanket receiver borrowing is not correct: `return self`, receiver-derived aggregate returns, nested mutable calls, closures, and async capture can change value semantics. A conservative whitelist prototype preserved four negative controls but could not prove the real typed `CoreLexer.peek` HIR shape within the three-cycle limit and was reverted.

## Required fix

Choose one architecture-complete owner:

1. Add explicit, unforgeable receiver kind to Rust and Simple HIR and a fail-closed escape/effect proof before copy elision; or
2. Give defensive aggregate copies function-scoped lifetime ownership so copies are unregistered and reclaimed on every return/error edge.

Do not raise the registry cap, weaken `rt_struct_receiver_valid`, or special-case `CoreLexer`.

## Rejected bounded experiments

- Blanket immutable-receiver borrowing was reverted because returning or indirectly mutating `self` can change struct value semantics.
- A fail-closed HIR escape/effect whitelist kept all four negative controls but did not prove the real unresolved `Array.len`/derived-index HIR shape within the three-cycle limit.
- Reclassifying `CoreLexer` as an identity class matched its mutable-cursor design and passed owner-to-alias plus two-instance/snapshot controls, but exposed the existing interpreter class copy-on-write asymmetry (reverse alias mutation did not reach the owner). The unverified change was reverted. Resume only with a cross-engine class identity fix or the scoped-copy design below.

The remaining architecture-complete alternative is a nestable function-copy scope: mark defensive parameter copies, allocate them through a scoped struct allocator, reclaim at every return/error edge, copy out returned parameter-derived values, and conservatively promote on uncertain escape. Existing transient/discard parse arenas are non-nestable and are not suitable for function calls.

The runtime-only copy-scope ABI is implemented and provider-tested, including nested ownership, cross-thread free refusal, outer promotion, and 4.3 million reclaim cycles. Compiler integration was reverted after final review found scalar-getter over-promotion, missing return copy-out, non-CFG provenance, and an incompletely threaded pure-MIR opcode. Resume from the dormant runtime API only after the compiler representation uses an existing exhaustively supported MIR instruction shape and a CFG fixed-point ownership proof.

A narrower capability correction was also prototyped: internal `CoreLexer` accessors become `me` receivers, which uses the existing alias ABI while keeping the struct tuple/rebind protocol. The production source audit was coherent, but the final focused Rust test fixture failed to parse before MIR assertions and its LLVM allocator oracle used a stale source spelling. The unverified changes were reverted at the two-cycle limit. Resume by repairing those test-only defects first, then require emitted `CoreLexer.peek` without `AggregateCopy`/`rt_struct_alloc`, adjacent free struct-parameter copy retention, and full lexer semantics before bootstrap.

Separately, interpreter class aliases still detach through `Arc::make_mut`. The correct language-wide repair is an `ObjectFields` storage split (struct COW versus class identity), but it touches about 42 direct field-map consumers and did not converge as a bounded patch. Keep this distinct from the bootstrap lexer fix; do not convert `CoreLexer` to class until the complete cross-engine class identity corpus passes and its snapshot/API protocol is intentionally redesigned.

## Acceptance

- Immutable scalar accessor: no receiver `AggregateCopy` and no `rt_struct_alloc` relocation.
- `return self`, `return self.inner`, receiver-to-unknown/mutable call, closure/async capture: defensive copy retained.
- Static/free first parameter named `self`: defensive copy retained.
- More than 4.2 million lexer accessor calls: exact token checksum and bounded live registry count.
- Canonical Stage 2 sanity, Stage 3 admission, full CLI Stage 4 admission, then the retained performance matrix.
