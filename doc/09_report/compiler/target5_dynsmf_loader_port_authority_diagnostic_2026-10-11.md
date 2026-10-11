# Target 5 dynSMF loader port authority diagnostic

Status: OPEN. The attempted typed port was removed before commit because its installer was callable by an ordinary importer. The kernel closure remains red with two direct `os.smf` imports; a green count from an unauthorized callback registry would not qualify Item 5.

## Evidence

- The starting `check-kernel-closure.shs` run found 2240 classified files, zero unclassified/K0-to-P/K1-to-P, and two K0-to-OS imports, both in `module_loader_compat.spl`.
- A draft K0 port and `os.sosix` adapter replaced those imports. The closure checker then reported 2241 classified files and zero forbidden edges. The port-only SMF compile succeeded.
- A two-module native fixture imported the draft port's non-`pub` `install_loader_dynsmf_port_v1`, installed arbitrary callback functions, exercised all eight operations, and exited zero with `DYNSMF_LOADER_PORT_PASS`. The native build completed in about 17 seconds. Thus the current compiler/runtime did not enforce the issuer boundary required by `aspect_dynsmf_loader_port.md`. A hostile package could install a fake adapter before the trusted one.
- The full SOSIX adapter SMF compile selected 339 modules and timed out after 180 seconds during HIR at 211/339. This gives no adapter or V3 final-unpin runtime proof.
- The draft source, adapter, fixture, and V3 test edits were removed. No insecure callback port is committed.

## Required repair

Preserve the current V3 owner sequencing and two explicit K0-to-OS violations until a composition-bound adapter has a language-enforced, nonforgeable issuer. First add a negative importer fixture that must fail to install a fake adapter; then bind the trusted SOSIX adapter and rerun the V3 final-unpin authority spec. The kernel closure audit, current-source core/MCP native smoke, no-import size/startup/RSS cohorts, and Target 6 compile cohorts remain separate open gates. No release landing is justified by this diagnostic.
