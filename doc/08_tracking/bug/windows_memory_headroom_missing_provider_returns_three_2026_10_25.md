# Windows memory headroom provider returns three bytes

The frozen `13d` producer PE at SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b` has `rt_host_memory_headroom_bytes_v1` machine code `mov eax, 3; ret`. In `windows_available_memory_headroom_v1`, that positive sentinel passes the success check, converts to zero available KiB, and reduces the inner worker pool to one. The outer RSS monitor remains enabled; the two controls measure different quantities.

The implementation previously lived in `runtime_native.c`, which is compiled in the canonical core-C runtime but excluded from the Rust058 runtime archive because it owns many other symbols. The fix moves its `GlobalMemoryStatusEx` query into the narrow `runtime_memory_headroom.c` owner and registers that owner in both runtime source families, the core-C capsule, the public runtime header, and the source-list parity manifest. Query semantics remain `min(ullAvailPhys, ullAvailPageFile)`; failure still returns zero.

The native OS-oracle probe passed in both bounded diagnostic profiles, with four assertions per profile:

- Genuine Rust058 archive SHA256 `0586070170670ea3c5bd20655b40366568b2485d7138326c42da11d9f045989c` plus the new provider TU. The archive had zero provider definitions and the TU had exactly one. Provider value and OS oracle were all `16,146,329,600` bytes.
- Canonical core-C archive built from the exact 30-file `tools.rs` runtime roster. It had exactly one provider definition. Provider value and OS oracle were all `16,148,529,152` bytes.

Each probe linked the runtime string ABI, confirmed the provider returned a measured value above three, and compared it against `GlobalMemoryStatusEx` sampled before and after the call. Both probe executables exited zero and reported `assertions=4`. Tool, source, archive, object, PE, full link-argv, and eight stage guard-receipt hashes are sealed in [the diagnostic evidence record](windows_memory_headroom_native_probe_evidence_2026_10_25.sdn). The retained run manifest SHA256 is `279d278d0abe1139af1be5126d7d4522a22525faf21154712640dab958bf06f6`; the full stage argv SHA256 is `23006ec3d76de82f9df61938b9f10d2198d7bdfceb08b3bb70199b99b4fb6719`.

This was a functional diagnostic, not a normal resource-admission pass. RSS was monitored with enforcement disabled; all eight stage guards completed and quiesced with no hard-limit events or changed inputs. Fresh available physical memory stayed between `16,003,366,912` and `16,167,993,344` bytes, below the normal `19,516,192,768`-byte floor. The source fix has not been qualified by a full Phase 3 build, and the frozen `13d` producer PE remains unchanged until a future build consumes the provider.

Until that build, the tested temporary workaround for the first critical build engine is `SIMPLE_SHARD_MEM_CLAMP=0` plus `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` set from the fresh minimum of available physical and commit memory. No Phase 2 rebuild is needed before the first Phase 3 retry.
