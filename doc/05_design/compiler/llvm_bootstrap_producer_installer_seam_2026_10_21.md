# LLVM bootstrap producer installer seam

Source-only implementation of the frozen Astra guide (SHA-256
`5ef6ce5f0ae4b2617673f16c362741a1490952f7e8f18ffc28475ed610dfaff2`).
Parent source is `dd59f45ed50165edbc82b20b9592c8617a61083d`, tree
`59da74d742a9d59bdc97113114a7c7a718c0105b`. All ten guide source pins were
checked before editing. Existing prescan, reverse-index, parallel-worker and
syntax fixes remain inherited byte-for-byte except the reviewed CLI seam.

The command body remains `app.cli.bootstrap_main` at its canonical logical
entry `src/app/cli/bootstrap_main.spl`. No bootstrap builtin helper was moved,
renamed, retyped or replaced. The native coordinator, parse worker allowlist,
policy handoff opener, context ownership and compilation pipeline remain the
existing implementations. Canonical startup calls
`bootstrap_install_worker_backends_v1`, whose default module preserves selected
K1 followed by full-table installation and the original admission diagnostic.
The default policy adds no restrictions to existing downstream validation and
preserves the previous help/version strings.

The restricted producer has two explicit physical source projections:

| Logical module | Sole physical owner in the restricted source view |
|---|---|
| `app.cli.bootstrap_backend_installer` | `src/compositions/llvm_bootstrap_producer/app/cli/bootstrap_backend_installer.spl` |
| `compiler.driver.bootstrap_k1_selected` | `src/compositions/kernel_llvm/compiler/driver/bootstrap_k1_selected.spl` |

The build owner must materialize these projections into one isolated frozen
source view and bind every logical module to exactly one hashed physical
owner. Ambient source-root ordering is not authority. The canonical full
entry and installer remain the default repository product. The restricted
installer checks the real selected LLVM policy and validates the active table
as exactly the interpreter/LLVM K1 table, refusing an already widened table.
These projections apply only while building the intermediate producer. That
executable must subsequently compile the complete CLI from a separate full
source view with the canonical full installer and required full compositions;
propagating the producer-only projection into the final product is forbidden.

`bootstrap_backend_request_error_v1(backend, plugin_path)` consumes existing
argument-owner values. Native direct, grouped and focused routes check it
before dispatch; compile checks it before deleting output or building a
driver. The shared worker's native argument owner checks its parsed backend
after the internal policy handoff has been opened. Existing native option
validation already rejects plugin flags. No second argument parser or closure
callback ABI is introduced. LLVM/default output is accepted; unavailable
output backends and plugin overrides receive explicit errors. Source inputs
may include every backend implementation and the full CLI.
Composition refusals retain failure status 1. Body-routing tests require an
existing valid hello source rather than relying on a missing-input failure.

The VHDL and public-driver dependency roots still exist. This step establishes
a statically selected installer seam, not a measured closure saving. The sole
build owner must obtain the actual canonical closure census before another
expensive producer build. Any further VHDL factoring needs a concrete reviewed
call-surface proposal preserving the entire frontend/AOT pipeline.

Executable unit and system specs exercise real table installation, registry
selection errors, request policy and bootstrap-body refusal. Full and LLVM
registration specs require separate fresh processes and their respective
source views because the registry is intentionally process-owned. Their
execution and generated manuals are UNRUN: no admitted general test/docgen
runtime is available. Static review does not establish a working producer.
Source-level guard checks do not replace LLVM hello, focused compiler-fix
fixtures, the complete CLI build, full feature smoke or executable provenance.
