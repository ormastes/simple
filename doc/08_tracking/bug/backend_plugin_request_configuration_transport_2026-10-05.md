# Backend plugin request configuration transport

Status: implementation authored; native C ABI fixtures PASS, Simple specs UNRUN.
Parent: windows_production_dynamic_backend_provider_incomplete_2026-10-05.

The old16byte request carried ABI, role and capability bits only. The runtime
zero-initialized all six configuration slices, silently dropping backend,
target, CPU, ordered features, optimization and MIR ABI digest. The new bounded
SBQ1 packet carries and validates every field; legacy/unsupported packets reject.
The implementation and exact field limits are in the existing versioned plugin
design and C ABI header. Selection-only path remains local.

Validation on2026-10-05: Windows clang23 MSVC ABI fixture suite completed37
actual host invocations:13 existing single/batch path/borrowed-handle, operation
failure, descriptor and input cases;24 added malformed single/batch requests.
The successful provider asserts every configuration field and exact feature
wire bytes. Malformed cases cover legacy packet, version, ABI, role, unknown
capabilities, overflow length, empty required field, invalid UTF8/NUL, trailing
and truncated data, oversized feature count. Existing unload/session/release
assertions remain: single3buffers, batch4buffers, exactly one session close,
borrowed handles released only by the caller.

Evidence: isolated simple-plugin-request-config-20261005/request-native-cycle2.log
exit0. Cycle1 failed during environment setup because a tracked setup dependency
was absent from the partial checkout; no test executed then. That failed log is
preserved. No previous thirteen-case receipt was replaced or reused as new proof.

Pure-Simple request roundtrip/malformed specs are authored and UNRUN; no seed
was used. Decoder cost is O(packet bytes), bounded64KiB/128features, with fixed
stack storage and no decoder heap allocation. Lifecycle checks cover buffer
release and handle retention. No measured request latency/RSS target is claimed;
those require the eventual production provider qualification. This repair does
not close production provider, MIR fidelity or dynamic admission gaps.

Peer review follow-up: the Simple decoder originally used a raw byte/text
roundtrip as its UTF-8 check. Those conversions may preserve malformed bytes,
so that check could accept requests rejected by the C bridge. It now uses
`validated_utf8_bytes_to_text_linear`, the canonical strict validator, then
applies the existing NUL rejection. Added Simple cases cover eleven malformed
encodings (overlong forms, surrogate, above U+10FFFF, invalid lead/continuation
and truncated sequences), NUL, multibyte fields/features and the upper scalar
boundary. These Simple cases remain UNRUN. The prior 37 native C cases are
unchanged and were not rerun; their PASS does not qualify the Simple decoder.
This removes one roundtrip byte allocation while retaining linear validation;
no measured performance or memory improvement is claimed.
