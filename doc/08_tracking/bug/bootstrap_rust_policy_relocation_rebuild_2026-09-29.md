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

## Windows recurrence on the older frozen producer, 2026-09-30

The isolated Windows `4a5a4ca15761` producer retained the older `f9bdea7b3238`
bootstrap scripts, before the correction in `ff04909dfac0`. Its copied seed,
Cargo cache and native objects matched their donor bytes and modification times.
Nevertheless, the recorded aggregate changed from `fbd46ef1726e` to
`cd6cdfba059c`: only the toolchain category changed. Compiler sources (42,875
records), Cargo path dependencies (2), runtime sources (256), policy (525),
native tools (22), recipes and unclassified records remained identical.

A bounded resolver-only replay reproduced both complete 16-record toolchain
category hashes exactly. The sole differing record was `rust-policy-path`, from
`/d/dev/simple-windows-positional-snapshot-producer-20260930/src/compiler_rust/rust-toolchain.toml`
to `/d/dev/simple-windows-hir-shared-fixes-20260930/src/compiler_rust/rust-toolchain.toml`.
The policy hash, selected binaries and versions were unchanged. The live build
was preserved. Its first Rust invocation subsequently passed in 9m22s and
reported 253 `Compiling` records; no cache-hit count was reported.

Windows/MSYS execution of the production Rust fingerprint block reproduced the
relocation failure against the frozen implementation. The same block from
current main passed relocation equality and policy-content, tool-path,
tool-bytes, tool-version, foreign-policy, duplicate-policy and missing-policy
controls. This supplements the existing full fingerprint regression; it does
not create another permanent duplicate suite. Evidence and the finite diagnostic
harness are retained in
`D:/dev/simple-windows-hir-shared-recovery-20260930/`:
`toolchain-differential.log`, `old-toolchain.records`, `new-toolchain.records`,
`policy-relocation-f9b-negative.log`, `policy-relocation-baseline.log`, and
`bootstrap_seed_policy_relocation_test.shs`. The historically named
`policy-relocation-baseline.log` is the current-main **PASS**, not the negative.

The bootstrap status text now reports a changed seed input fingerprint instead
of asserting that Rust source content changed. Future frozen source generations
must include the existing correction. Old stamps remain untouched. Reusing the
same canonical source root also avoids relocation costs in Cargo's separate
freshness checks: for example, the copied cache predates the new checkout's
`vendor/regex-syntax/src/lib.rs` timestamp (09:00:51 versus 10:52:06). Fixing this
fingerprint record alone does not prove that Cargo will reuse every artifact.
