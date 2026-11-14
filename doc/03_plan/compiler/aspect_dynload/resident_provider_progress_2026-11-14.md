# Linux LLVM resident provider integration checkpoint

Status: implementation in progress; public LLVM/Auto observer admission remains closed.

The compiler semantic-row producer is integrated. The decoder copies/validates the byte-aligned row contract, rejects overflow and ambiguous identities, sorts semantic keys before issuing manifest-local IDs, and binds those keys to actual LLVM addresses. Final linker options require SHA1 build identity and start/stop GC; both executable routes use the same policy, including the real Clang fallback conversion. Off remains unchanged.

The actual C adapter now has a separate resident mode, process control admission, immutable canonical map lookup, bounded thread attachment, per-context attempted-event sequence, and mandatory initial context transition. Thread entry and outer worker task-root hooks are selected by a default-false source-runtime option. The legacy private harness mode is mutually exclusive. This source is not yet a qualified observer provider.

Evidence retained at `/tmp/xray-resident-map-probe-20261114`: first attempt rejected a truncated fixture extraction; corrected second attempt compiled and ran 39 assertions; Astra then identified semantic ordering and overflow gaps. Third changed-source attempt compiled in 6.96s and ran 57 real native assertions with exit0, including those fixes and actual linker normalization owners. All extracted production bodies were checked byte-for-byte. Synthetic addresses test decoder/binder semantics, not loaded-image registration. Core-C producer SHA256 is `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`. Each compile was bounded to 60s and 2GiB process-tree RSS; no Rust seed was used. The authored SSpecs have not run through the full runner.

The C adapter passes Clang 18 syntax validation only. Its new dispatcher still requires real native event, loss, lifecycle, register-preservation and disassembly tests. The separate thread-header fixture proves actual packed admission plus two-thread attachment only; it does not establish runtime hook/provider integration.

The actual ELF snapshot leaf, Simple caller and singleton session source are now integrated. Remaining work: qualify session allocation and lifecycle, complete typed runtime-option/readiness integration, and test a real Simple-generated instrumented image through the normal driver/facade. The cold metadata reservation in the image wrapper is provisional and requires actual runtime-carrier memory qualification; it is not a proved process-memory bound. No external-writer immutability, hot unload, task-local spans, cross-platform support, or full feature completion is claimed.


The first changed-adapter check did not execute a binary: Clang 23 rejected deprecated `ATOMIC_VAR_INIT` under `-Werror`. The initializer now uses ordinary C atomic aggregate constants, accepted by Astra as a protocol-preserving source change. The first launch wrapper also failed to stop after its memory precheck rejected the run; this wrapper error was reported and corrected. A later separate precheck returned failure with 31,232,336 KiB available, and no compiler ran. Native retry requires the root owner's 36 GiB admission threshold.

The actual Linux image locator passed 33 present-image and three absent-image checks on native AArch64 with LLVM 23. That evidence is separate from the new manual Linux x64/LLVM 18 workflow, which has not executed. The singleton Simple session candidate remains source-only and requires its public admission entry to reject every unqualified profile; a private candidate name is not authority to activate it.


## Next end-to-end qualification route

Public `prepare` and `start` now consult one closed qualification authority before native control acquisition. The candidate profile string cannot authorize activation. This is a temporary safety gate, not the completed feature.

1. Freeze an integrated compiler source containing semantic-row emission, actual runtime link inputs, typed thread-runtime option and post-initializer readiness marker. Build/admit that producer through the bootstrap owner; the older producer's `--xray` rejection cannot exercise this source.
2. Compile a small real Simple application with a selected callee through the normal LLVM driver. Retain command/receipt, LLVM instrumentation and semantic rows, GNU build identity, linked adapter/runtime objects, and executable identity. Check its arguments/results before interpreting trace evidence.
3. Exercise the actual session implementation with validated main-image metadata and an owner-established startup quiescent handoff. The private qualification route must use the same decoder, allocation, publication, patch, collector and drain implementations; it must not substitute aliases, synthetic IDs or hand-edited IR. Runtime-ready alone is not that handoff.
4. Qualify the resident handler ABI and bounded allocation on that target, including precreated worker attachment, restart at cold task roots, loss and stop/drain races. Establish module-global initialization ownership and actual Simple metadata-carrier memory costs.
5. Replace the closed authority only for the resulting qualified target/toolchain/profile, using the real main-image registration and owned quiescence state. Repeat the application operator scenario through public `TraceObserverV1`: prepare, start, poll canonical transitions/edges, stop, drain and release. Unsupported profiles and forged handles must still fail explicitly.

Steps 1–5 are pending. The locator C fixture, projected map tests and source reviews do not substitute for this final public-facade scenario. LLVM stage 1 completion remains separate from native Linux stage 2, Windows stage 3, folder-policy consumers, and the broader visibility/accessor/plugin plan.
