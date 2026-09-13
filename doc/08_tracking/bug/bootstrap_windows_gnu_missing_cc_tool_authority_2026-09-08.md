# Windows GNU bootstrap tool authority assumes an absent cc alias
**Status:** OPEN (unverified 2026-09-12)

Owner: Astra Phase 1 continuation. Status: focused repair verified; canonical Stage 2 continuation pending.

The strict full bootstrap published the fresh Rust seed and runtime tuple on
2026-09-08, then exited before Stage 2 with `could not bind bootstrap tool
authority`. The published seed SHA-256 is
`6d7dee165170d839c569288c7171d81118857e19026db95553a3aad97fde1e52`.
The full run is retained under
`build/native_probe/astra_toolchain/resumed-full/` (exec 63519, exit 1).

`bootstrap_stage3_tool_authority_snapshot` in
`scripts/check/lib/bootstrap-stage3/authority.shs` selects `cc` on every host
except Windows MSVC. This Windows GNU toolchain provides `gcc.exe` but no
`cc.exe`. The actual Rust build already uses the shared
`bootstrap_stage3_target_c_compiler` owner, which correctly selects `gcc`.
The snapshot instead passes an empty path for the `cc` row and rejects it.

The exact failed-run PATH reproduces this deterministically: the snapshot
successfully binds cargo and rustc, calls
`bootstrap_stage3_tool_requested_path cc cc ''`, and returns 1 for the empty
result. The trace and source-bound receipt are
`build/native_probe/astra_toolchain/tool-authority/{trace.log,receipt.env}`;
helper SHA-256 before repair is
`392180ad0edf314f83cbbc0a7a740bb830badb02c86c0cff18f060c8d139a378`.

Repair belongs to the shell tool-authority boundary before a pure-Simple
compiler exists. No language or Rust/runtime implementation change is needed.
Use the existing target C-compiler owner for Windows GNU as for MSVC, and bind
the selected executable name and bytes. A missing explicitly selected compiler
must remain a failure. The focused regression must inject a missing `cc` alias,
cover default gcc and a target-specific compiler override, and reject a missing
override. Then run the exact live snapshot and resume canonical Stage 2 using
the newly published seed; another full Rust rebuild is unnecessary.

The missing-cc behavioral test failed before the fix and passed after the GNU
Windows case was routed through the existing compiler owner. It covers default
gcc, an explicit `gcc-selected` override, and rejection of a missing override.
The exact failed-run live snapshot now also passes (exec 56213, exit 0) with
helper SHA-256
`bf300b5f3dd9cdb0cd4e6db9cd8b5d12ff76027d945fba0718b676b0aa8dcdf5`.
Its retained `tool-authority/snapshot` binds gcc and every other required tool,
including installed Rust/Cargo and LLVM. The pre-fix trace and receipt remain
as `trace.before.log` and `receipt.before.env`. This is tool-authority evidence,
not Phase 2 compiler admission.

Subsequent canonical trust-root continuations stopped before Stage 2 in Rust
input fingerprint metadata probes (first installed Cargo, then the later native
toolchain block). Neither failure re-entered the repaired missing-cc snapshot
path. The metadata evidence and bounded recovery contract are tracked in
`bootstrap_rust_toolchain_sysroot_resolution_2026-09-08.md`. No Stage 2 artifact
or release admission is claimed by this focused repair.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and has no cheap repro reachable within budget; left open with an explicit unverified status line.
