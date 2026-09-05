<!-- codex-architecture -->
# LLVM 23.1 bootstrap binding architecture

## Status

Proposed — blocked on an internal or upstream LLVM-23.1 Rust binding.

## Context

The bootstrap currently couples three distinct version boundaries: Rust seed
bindings (Inkwell/llvm-sys 18), host tool discovery, and pure-Simple LLVM
subprocess tooling. Changing only one produces an ABI-incompatible build or a
mixed-version backend. No released Inkwell/llvm-sys binding supports LLVM
23.1, so selecting a 23 prefix today cannot be accepted.

## Decision

Introduce one fail-closed toolchain identity contract at the existing platform
resolver boundary. It carries major/minor version, prefix, `llvm-config`,
`clang`, `llvm-as`, `opt`, `llc`, library path, and binary hashes. The Rust
binding adapter and the pure-Simple backend consume this identity; neither
independently discovers a fallback tool.

The LLVM-23 binding is a virtual capsule with three owners:

1. vendored/forked `llvm-sys` 231 bindings and generated C API surface;
2. a compatible Inkwell feature (`llvm23-1`) and Rust backend API adapter;
3. platform discovery and pure-Simple tool probes.

All three must advertise the same 23.1 identity before `bootstrap-from-scratch`
can enable `--backend=llvm`. LLVM 18/20 remains diagnostic-only.

## Boundaries and invalidation

- `scripts/setup/platform-detect.shs` owns resolution and exports only the
  selected toolchain identity.
- `src/compiler_rust/compiler` owns the Rust C-API binding adapter.
- `src/compiler/70.backend` and `95.interp` consume tool paths only through
  that identity.
- A version, prefix, library, or binary-hash change invalidates all Rust seed,
  Stage-2, Stage-3, Stage-4, and SDK-capsule artifacts.
- SimpleOS toolchain ports remain a separate target-specific patch series;
  they must be rebased onto 23.1, not copied from the LLVM-20 fork blindly.

## Admission sequence

1. Build/install a pinned 23.1 host toolchain and prove all six tool identities.
2. Compile the Rust seed with the 231 binding; repair API changes without
   weakening LLVM validation.
3. Run pure-Simple LLVM text/bitcode/replay probes against the same identity.
4. Run x86 Stage 2, Stage 3, Stage 4, essential-tools smoke, and SDK capsule
   admission.
5. Run FreeBSD and SimpleOS QEMU current-host rows; native macOS ARM and
   AArch64 rows require their prepared hosts.

## Rejected alternatives

- `LLVM_VERSIONS=23` with an LLVM-18 Rust binding.
- Running an LLVM-18/20 candidate and relabeling it 23.1.
- Per-backend fallback discovery or a seed-only acceptance path.

## Review ownership

- Sidecars: binding generation/API audit; host toolchain build; platform and CI
  discovery; SimpleOS 23.1 port. Merge owner: Stage-4 SPipe lane. Final review:
  independent high-capability reviewer after executable evidence.

## References

- `scripts/setup/platform-detect.shs`
- `src/compiler_rust/compiler/Cargo.toml`
- `doc/03_plan/infra/agent_sessions/stage4_spdev.md`
- `doc/03_plan/design/bootstrap_sdk_capsule.md`
