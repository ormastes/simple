# Equivalent policy relocation forces a Rust seed rebuild

## Observed cause

Linux candidate 6772 moved unchanged Rust/runtime input bytes from the retained 668
checkout into a separate worktree. Both canonical resolver observations selected
the same installed sysroot and tool identities and policy SHA
`c6d07759f89d3d37e3e50a1567a22edddbe4fb2d2ea4fe386c26efaeb43f0371`.
Only `rust-policy-path` differed. The seed aggregate and toolchain category hashes
changed; every other category hash and all membership counts remained identical.
The four successful Cargo phases consequently cost 617.25 seconds. This is a proven
Linux relocation delay; the separately observed Windows Rust 877s/Stage2 749s
timings do not by themselves prove the same cause for all Windows work.

Retained causal record:
`D:/dev/simple-wsl-recovery-20260928/BUG_RUST_POLICY_RELOCATION_FULL_REBUILD_20260929.md`.
The actual old/new resolver difference and fingerprint details remain under the
recorded D-backed Linux output directories. No live stamp, cache or authority was
modified to manufacture reuse.

## Correction

The seed fingerprint alone projects the resolver's exactly validated root-owned
policy location to `rust-policy-id=repo:src/compiler_rust/rust-toolchain.toml`.
It requires one matching actual policy-content hash and rejects missing,
duplicate, wrong-owner or conflicting identity records before accepted output.
The resolver and tool provenance still report the absolute observed location.
Policy content/channel, actual executable/sysroot paths, tool settings,
binary hashes/versions, source/runtime/SDK-header membership and content,
backend/features/target/ABI and recipe identity remain bound.

Old path-sensitive stamps are not rewritten or reinterpreted. The algorithm
transition can invalidate an old fingerprint once. Subsequent equivalent policy
relocations use a stable identity; content or tool changes still invalidate.

## Verification scope

Focused authored shell contracts exercise the production projection helper with
canonical roots containing spaces, refusal controls and preserved non-location
records, plus the complete production fingerprint over minimal real source
fixtures. Fixture tools support metadata only and reject build invocations;
provider discovery is substituted in the complete fixture. These are fingerprint
contracts, not an admitted compiler, native artifact, bootstrap or release claim.
Cycle 1 passed once on Ubuntu 22.04: the complete production fingerprint stayed
equal after relocation and changed for the authored content, membership,
ABI/backend/target/features and tool hash/version controls. Actual Windows/MSYS
projection-only execution also passed once with forward-slash canonical paths,
space-containing roots and strict refusal controls. Both raw statuses were 0;
the implementation and test hashes matched their captured pre-execution inputs.

Logs, raw statuses and immutable input capture:
`D:/dev/simple-wsl-recovery-20260928/rust-policy-relocation-contract-cycle1-20260929`.
No compiler/bootstrap execution or live cache/stamp modification was performed.
