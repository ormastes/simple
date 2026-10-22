# Pure-Simple native codegen exceeds bounded memory

Status: observed, unresolved; canonical bug-database reconciliation pending.

Producer r17 SHA256 `29dd8539f3fe8e01df9b227e0621b20953fd736e239dafef8bafae8918abb3c2`; frozenv12 core source manifest and full command are retained in `/home/yoon/dev/simple-pure-redeploy-20261021/build/nogc-hardening/`. Manual module attempt10 passed HIR421/421, MIR421/421, and native-cache preparation421/421. Native codegen reported380 uncached modules, sequential execution, and checkpoint41/421 (current enum_constructor_payload). No further completion checkpoint or requested entry object appeared before memory termination.

Verified owned parent+worker RSS reached42,817,428 KiB against41,943,040 KiB bound. Both were SIGTERM terminated/reaped; command exit143. This is RESOURCE_ABORTED, not a compiler assertion failure, OOM, or successful object build. No comparative baseline establishes a regression. The preceding two invalid MirBinOp.Or variants were corrected to BitOr with Astra approval; all MIR failures are now cleared.

Retain compatible completed cache objects and frozen sources. Investigate native backend per-module lifetimes and retained allocator state across callbacks before another authorized attempt. Do not infer failure cause merely from the progress label, bypass memory/source-admission policy, fabricate cache identities, or deploy partial toolsets. No product workaround applied. Final bounded attempt10 is exhausted.

## Retained-output correction

A bounded filesystem inspection found336 `.o` files (14,436,392 bytes total) written within the attempt10 time window. The console checkpoint41/421 was stale and does not identify the active codegen module or prove a first-module stall. Offline ELF ET_REL/header and adjacent receipt path/size/SHA256 checks are recorded separately in `manual-module10-object-receipt-consistency.json`; these checks do not establish source authority, cache admission, or acceptance.

Read-only source audit identifies overlapping per-callback capsule/MIR, storage-lowered MIR, optimized MIR, full LLVM IR and object-byte lifetimes in `backend_helpers.spl`, `llvm_codegen_adapter.spl` and `driver_aot_native_output.spl`. Source alone cannot prove deep copying, leakage or allocator retention. MIR identity serialization already has a transient scratch scope. Any future diagnosis must distinguish live heap growth from allocator RSS high-water and record per-module completion independently of stale console checkpoints. No speculative transient-scope cleanup was applied because backend state that may escape the scope has not been proven.

## Scratch-scope safety review

A candidate translation-wide transient scope must account for `_llvm_bootstrap_string_globals_text_cache` in `backend/_MirToLlvm/asm_constraints_helpers.spl`: `llvm_bootstrap_string_globals_text()` publishes newly allocated `out` to process-global state, and legacy `translate_module` permits bootstrap shortcuts. Promoting only returned IR is not sufficient proof that this state survives scope teardown. The explicit-target grouped path disables those shortcuts, but substituting it for canonical translation has not been shown behavior-preserving. No speculative scope change has been made.

Working-source SHA comparisons: candidate `llvm_codegen_adapter.spl`, `backend_helpers.spl`, and `asm_constraints_helpers.spl` match boot7 working files; `core_codegen.spl` differs. This comparison does not authenticate those files as the exact r17 binary build inputs. The ten-attempt verification bound remains exhausted, so no replacement producer or redeploy qualification can currently be claimed.

Astra bounded review: **REQUEST CHANGES** for IR-only promotion. Repeat reads/late appends require cache lifetime ownership; input-alias isolation and other escapes are unproven, and transient runtime scopes reject nesting. No safe implementation subset approved; no product cleanup or extra build applied. The same codegen/verification-bound blocker persisted over three goal turns. Goal blocked pending newly authorized bounded verification or a compatible externally qualified producer. No acceptance closure, deployment, commit or landing.
