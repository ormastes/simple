# Missing disk headroom provider returns three bytes

The frozen provisional a2 compiler (`a2c241a9...352b55`) reports three bytes free and refuses cache publication in the retained direct Hello attempts and import gate. Its actual `rt_host_disk_headroom_bytes_v1` machine body is `mov eax,3; ret`; the linked Rust058 archive has no definition. This is a generated fallback value, not a measurement of host storage.

Confirmed affected owners are frontend parse-cache publication, shared parse-CAS publication, and module TLDR atomic publication through `disk_publish_admitted`. This does not establish that HIR/native-object/runtime caches all use this gate. The separate full Phase3 diagnostic timed out without a complete worker log; its exact cache refusal scope remains unconfirmed.

The repair moves the sole real implementation from `runtime_native.c` into a narrow C translation unit also compiled into the Rust runtime archive. It uses the public boxed-text accessors, rejects empty/oversized/NUL paths, uses strict UTF-8 conversion on Windows, obtains caller-available bytes via the OS, and saturates checked positive counts at INT64_MAX. POSIX paths retain native-byte semantics. Every canonical source roster and the capsule sole-owner check includes this owner.

A real ABI probe is authored for genuine Rust058 plus the new owner and separately for the canonical C profile. Its fourteen checks include an OS oracle, actual boxed text, invalid values/paths, a created Unicode directory containing a space, and overflow bounds. Native execution is pending. No cache policy, reserve, keys, or admission checks are disabled.

A future a2 relink must use genuine retained object inputs and regenerate fallback stubs excluding exactly this now-provided symbol. Other provisional stubs remain disclosed. The exact historical temporary object directory is absent; reconstruction and relink are not yet admitted. The old compiler, archive, source, and failed receipts remain unchanged.
