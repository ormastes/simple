# LLVM semantic map validation

Source: `test/01_unit/lib/trace/xray_llvm_semantic_map_v1_spec.spl`.
Requirements: A01 (prepared function binding), C04 (canonical identity), T02 (bounded failure).

This manual describes the authored unit scenarios. The full SSpec runner has not executed them. A native exact-source projection passed 57 combined map, runtime-policy and link-normalization assertions; its synthetic image addresses do not qualify a loaded executable or observer session.

| Scenario | Setup and action | Required result |
|---|---|---|
| Decode a relocated row | Supply the compiler's little-endian byte layout and a checked executable interval. | Recover the exact owner/key, signed PC-relative function address and extent. No aligned native struct cast is used. |
| Reject corrupt metadata | Change header values, UTF-8, reserved flags or padding. | Fail before issuing a manifest or patching any function. |
| Bind actual identities | Provide semantic rows and an address table with LLVM IDs 7 and 12. | Match by exact address; issue independent manifest-local canonical IDs. Missing/ambiguous bindings and missing build identity fail. |
| Preserve identity under permutation | Reverse two semantic rows while retaining their owner/key pairs. | Both runs assign the same canonical ID to each semantic key. Caller input remains unchanged. |
| Reject arithmetic overflow | Supply an executable interval whose end would wrap. | Return an invalid-map failure before membership checking. |

The public observer remains unavailable until native image registration, lifecycle, ABI, memory and real Simple pipeline qualification are complete.
