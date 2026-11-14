# Linux LLVM resident provider integration checkpoint

Status: implementation in progress; public LLVM/Auto observer admission remains closed.

The compiler semantic-row producer is integrated. The decoder copies/validates the byte-aligned row contract, rejects overflow and ambiguous identities, sorts semantic keys before issuing manifest-local IDs, and binds those keys to actual LLVM addresses. Final linker options require SHA1 build identity and start/stop GC; both executable routes use the same policy, including the real Clang fallback conversion. Off remains unchanged.

The actual C adapter now has a separate resident mode, process control admission, immutable canonical map lookup, bounded thread attachment, per-context attempted-event sequence, and mandatory initial context transition. Thread entry and outer worker task-root hooks are selected by a default-false source-runtime option. The legacy private harness mode is mutually exclusive. This source is not yet a qualified observer provider.

Evidence retained at `/tmp/xray-resident-map-probe-20261114`: first attempt rejected a truncated fixture extraction; corrected second attempt compiled and ran 39 assertions; Astra then identified semantic ordering and overflow gaps. Third changed-source attempt compiled in 6.96s and ran 57 real native assertions with exit0, including those fixes and actual linker normalization owners. All extracted production bodies were checked byte-for-byte. Synthetic addresses test decoder/binder semantics, not loaded-image registration. Core-C producer SHA256 is `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`. Each compile was bounded to 60s and 2GiB process-tree RSS; no Rust seed was used. The authored SSpecs have not run through the full runner.

The initial checkpoint had only Clang 18 syntax validation. The native CI evidence below now covers real worker/dispatcher event, loss and lifecycle cases; complete register-preservation, admitted-callback close races and patched Simple-generated execution remain pending. The separate thread-header fixture proves actual packed admission plus two-thread attachment only; it does not establish runtime hook/provider integration.

The actual ELF snapshot leaf, Simple caller and singleton session source are now integrated. Remaining work: qualify session allocation and lifecycle, qualify the integrated typed runtime-option/readiness path, and test a real Simple-generated instrumented image through the normal driver/facade. The cold metadata reservation in the image wrapper is provisional and requires actual runtime-carrier memory qualification; it is not a proved process-memory bound. No external-writer immutability, hot unload, task-local spans, cross-platform support, or full feature completion is claimed.


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

The typed link option now reaches the source-built runtime compiler and hosted entry generator from both Linux LLVM executable branches. Enabled receipts include the context schema token; Stage4, prebuilt archives and SimpleOS bypasses reject the request. The entry emits its observational ready marker only after runtime initialization and all discovered module initializers return. These narrow hunks derive from the initializer owner checkpoint `c61149c73b48585560b6733955039cea10e84636`; this branch preserves the existing text-return entry API and does not import the separate typed initializer-receipt dependency stack. Actual driver execution of this integration remains pending.

## Native Linux x64 CI qualification update

[Run 43603983255](https://github.com/ormastes/simple/actions/runs/43603983255) passed on PR head `2d3ceb691bea3e8edb8701221e1efc3f778b66e2`, checked merge snapshot `50bb2035bf20cc067185255716198164d7dbb825`. Ubuntu Clang 18.1.3 executed the real `runtime_thread.c`, `runtime_native.c`, `runtime_memory.c` and resident adapter fixture: **39 assertions passed, exit 0**. Recorded live cgroup limits were `memory.max=2147483648` and `memory.swap.max=0`; the transient service enforced 180 seconds and control-group cleanup. All nine recorded fixture/source/header hashes match this feature checkpoint's owned files.

Executed cases include precreated workers attaching at cold roots, generation restart and retired-slot nonreuse, distinct worker arenas, `pthread_exit` cleanup, exhausted/unknown-thread loss, and callbacks attempted after close leaving arenas unchanged. The close case pauses workers before their callback attempts; it does not establish a close race against an already admitted callback. Compiler-rt registration/patch APIs are fixture scaffolding; no sled is patched by this worker test, and no public Simple facade is exercised.

The same run's independent actual-image locator job passed **33 present-image plus 3 absent-image assertions** on Linux x64 LLVM 18. It complements the earlier native AArch64 LLVM 23 locator evidence without equating their ABI profiles.

Artifacts include checked source identity, compiler hash, per-step command/stdout/stderr/status, native source hashes, linker map, binary identity and live cgroup limits. Downloaded retained evidence is under `/tmp/xray-ci-43603983255/artifacts`. These new passes replace the earlier fixture-unrun status only for their exact scope. Public activation still requires the real loaded-map/profile authority, owner-established startup handoff, actual Simple-produced binary, carrier-memory and ABI qualification described above.

## Startup owned-thread ledger (source only)

The optional core-C runtime now routes its seven owned POSIX spawn sites through one typed boundary: five source sites in `runtime_thread.c` (including alternative preprocessor branches), one native HTTP resolver and one SIMD dispatch site. The admitted core-C source list excludes the separate `runtime_pool.c` owner. Off preprocessing still calls the original `pthread_create`. Enabled object identity includes the startup-ledger schema token.

The process owner records every admitted spawn attempt before invoking the OS, even when the OS later fails. A bounded CAS admits a startup window only from never-attempted, unspent state, under runtime readiness and process-control ownership. Held windows refuse creation with the existing pthread failure return path. End seals the window, and the actual entry wrapper unconditionally marks it spent before user main or a returning startup failure; idle windows cannot be acquired later in user code. These facts describe owned-thread attempts only. They do not exclude foreign/constructor threads or issue profile/map authority.

This ledger has source review only. The preceding 39 native CI assertions predate it and are not its qualification. Authored follow-up tests and an actual post-initializer Simple startup consumer, strong-symbol closure retention, loaded-snapshot/profile proof, and genuine public capture remain required.

The actual Simple materializer also needs the LLVM 18 archive layout, not only the CI locator script. Its source now falls back from the literal unresolved generic filename to the same compiler's exact-target architecture-suffixed archive query. It still rejects failed queries, unexpected paths and absent files; no ambient directory scan or compiler substitution is used. Read-only Clang 18 lookup confirms the native AArch64 archive path. Revised policy specs are authored but unexecuted, and the earlier materializer execution is not claimed for this new branch.
