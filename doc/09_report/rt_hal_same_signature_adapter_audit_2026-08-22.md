# `@rt(hal)` same-signature adapter audit — 2026-08-22

## Landed safe subset

`compiler.mir.rt_hal_call_abi_proof` now derives the resolved MIR function-
pointer signature structurally and the call rewriter proves it against the
closed binding before changing any block. It also proves the actual argument
count. Unknown text layouts, optional layouts, fixed arrays, pointers,
variadics, and result shapes fail closed. The proof is compiler-cold and adds
no generated runtime dispatch, allocation, or copy.

The transaction is all-or-nothing: one mismatched matching call returns the
original `MirFunction`. Unit coverage exercises the before/after invariant and
all nine non-clock semantic signatures.

## Adapter admission result

No additional comparison rewrite flag is enabled by this change. A metadata
signature is not proof that a same-signature comparison leaf preserves the
public wrapper's result, errors, and ownership.

| Category | Exact ABI / ownership blocker |
|---|---|
| File read | `[u8]` is a tagged runtime value whose only located production implementation is the bootstrap Rust runtime. The V3 buffer owner accepts caller-owned bytes, not this owned return value. |
| Stream read | `rt_process_read_stdout` is declared as Simple `text` but the native C surface returns `const char *`; ownership/tagging parity is not frozen. |
| Process wait | The scalar is representable, but the public negative status space has no reserved comparison-failure code. Substituting a sentinel would change errors. |
| Environment get | Optional text is an owning tagged result; the V3 owner is bounded to 32 bytes and cannot represent absence plus arbitrary text without truncation or replacement allocation. |
| Random fill | The argument is a mutable runtime array handle. V3/device comparison consumes caller-owned byte regions; no frozen no-copy projection from `[u8]` to that region exists. |
| Socket connect | The scalar handle/error space has no reserved comparison-failure code, and the address is a fat text argument in MIR but a tagged/native value on existing runtime surfaces. |
| IRQ acknowledge | The result is representable, but `plic_claim` is target-local rather than one frozen external ABI. Claim is read-once and must be captured only after bounded-owner admission. |
| MMIO read | The result is representable, but the raw provider exists only on bare-metal startup surfaces while the sealed process owner is hosted. Address/grant capture must precede read-once consumption. |
| DMA map | A returned handle is owner- and generation-bearing, not a comparable scalar. Three providers cannot independently create interchangeable handles, and no reserved comparison-failure handle exists. |

Enabling any row requires a generated leaf with the exact MIR/native ABI, a
caller-ownership bridge to `HalDeviceCompareOwnerV1` or the V3 buffer owner,
and a category-specific fail-closed error that is already part of the public
contract. Oversized/text cases must reject before physical access; they may not
truncate.

## Performance and memory

The proof is `O(P)` in the bounded parameter count plus the existing `O(B*I)`
cold MIR scan. It retains no payload, performs no runtime work, and creates no
generated hot-path allocation. Rewriting remains a direct symbol substitution
when admitted, so normal mode can remain zero-dispatch-overhead.
