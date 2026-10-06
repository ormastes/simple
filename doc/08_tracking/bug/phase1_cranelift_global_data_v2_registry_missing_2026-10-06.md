# Seed registry omits Cranelift typed-global ABI

The original runtime_std_native_static_only_v2_spec.spl reports unknown extern rt_cranelift_declare_global_data_v2. The validated interpreter handler and actual codegen bridge already exist; only its EXTERN_DISPATCH registration is absent. Register the existing handler beside the legacy global-data ABI. Preserve all argument/span checks, linkage and alignment semantics.

A Linux parsed-Simple regression creates a real AOT module with zero functions, declares a public i64 initialized to 29 at alignment 16, emits an object and frees the module. Rust object parsing requires the real named global symbol, eight-byte storage, section alignment at least 16 and exact little-endian initializer bytes. This regression fails with the missing extern before registration and passes afterward. Guarded repaired receipt: exit 0, quiescent 1, peak 4672772 KiB, maximum observation gap 3072 ms. Baseline and repaired logs/receipts: /tmp/simple-cranelift-global-v2-repair.

This proves the registered native data path, not an entire compiler generation. Original owner and whole/Phase2-4 qualification remain pending. Windows and other object formats are not claimed by this Linux-only regression.
