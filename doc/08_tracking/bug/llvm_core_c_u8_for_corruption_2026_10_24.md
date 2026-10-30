# LLVM/core-C byte iteration corrupted persisted manifests

A focused native identity fixture computed the correct source-text SHA-256,
then wrote different manifest bytes. ASCII values divisible by eight were
shifted right by three (p to 14, x to 15, h to 13, 0 to 6, 8 to 7).

Retained executable disassembly proves external_copy_bytes called generic
rt_array_get, then rt_value_unbox_int, before a correct typed-byte push. The
core-C generic getter returned packed bytes raw. Rust's generic getter boxed
them, so existing Cranelift-only coverage did not expose the mismatch.

The MIR repair makes typed u8 FOR iteration use rt_typed_bytes_u8_at followed by
UnitNarrow, matching indexed access and supporting packed and slot layouts.
Writer, SHA, runtime ABI and other element types remain unchanged.

Added checks cover MIR accessor/narrowing structure and LLVM/core-C execution:
all 256 values in both byte layouts, repeated external-text copies and exact
published manifest bytes with an independently fixed digest filename. These new
checks are authored but UNRUN until the fresh reviewed build executes them.

Bounded parity review found the self-hosted Simple FOR/index lowering already
uses its typed byte accessor and raw-to-U8 cast without generic decoding. It
needs no source change. This is source evidence; actual P2→P3 and P3 self-rebuild
remain unverified.

The new MIR regression and LLVM/core-C native regression both passed on source
49d094ff3c3f4db5ed4b02073536711ad771d5d9. The latter verified both byte layouts,
all 256 values, repeated external-text copies and exact independently pinned
manifest bytes. Enforced 8 GiB watchdogs completed quiescent with no observer
errors. Source runtime/writer ABI remains unchanged; full compiler-chain and
whole-suite verification is still pending.
