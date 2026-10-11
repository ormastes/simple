# Item 5 linker-pack static plugin ownership

Status: PARTIAL. Structural kernel closure improved; native and performance admission remain open.

## Change

- Move the optional linker-pack session and generation-pinned lifecycle to plugins.linker_pack.
- Keep the old compiler module paths as P_STATIC compatibility facades for existing clients.
- Keep linker wire/config imports pointed from the plugin to the compiler, and provider-loader imports pointed from the plugin to OS.
- Route the pre-admission artifact hash through the SOSIX host facade.
- Add a focused invalid-identity fixture that exercises both compiler facades and returns before native provider open.

## Evidence

- Before: check-kernel-closure reported 3 kernel-to-app/OS imports, including the linker-pack provider-loader import.
- After: the same checker reports 2240 classified files, 0 unclassified, 0 K0-to-P, 0 K1-to-P, 2 K0-to-OS, 0 unresolved. The remaining imports are module_loader_compat to dynsmf_owned_v2 and smf_dynlib. The gate remains FAIL.
- The first no-stub pure-Simple Stage 2 native build (old temporary OS owner) reached 577 MIR units after HIR/monomorphization reported 0 unresolved generic calls. Its worker terminated with signal 11 before producing a binary. Log: build/mini_builds/item5_linker_pack_os_owner_native.log.
- The first corrected-plugin build stopped at SCV snapshot admission before parsing: snapshot-read-failed for the moved src/os/smf/linker_lifecycle.spl. The inventory listed that removed tracked path. A retry after commit still failed at the same path: CURRENT advanced to c7c4db75056 but its generation retained both the old and new paths. The Stage 2 producer uses a V3 cursor without tracked-path membership, so it cannot notice the staged intermediate path disappearing; current source has a V4 record and fail-closed cold-init requirement.
- Explicit cold inventory rebuild removed the old OS path and admitted the new plugin path. The corrected closure selected 577 modules and completed HIR 577/577. The 600-second wrapper timed out during later work; its orphan worker subsequently exited without an executable or terminal source diagnostic. Log: build/mini_builds/item5_linker_pack_plugin_owner_cold_native.log.
- git diff --check, direct-env-runtime-guard --working, numbered-artifact-guard --working passed; doc/06_spec contains 0 executable .spl specs.

## Remaining gates

The two K0 module-loader OS imports need a typed release port preserving final-unpin and retry semantics. The corrected plugin fixture must finish native build and run; Item 5 then still needs default-demand loading and paired executable size/startup/RSS evidence. Item 6 compile work is separate and not qualified by this ownership move.
