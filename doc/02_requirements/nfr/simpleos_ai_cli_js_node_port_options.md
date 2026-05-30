<!-- codex-research -->
# NFR Options: SimpleOS AI CLI JS/Node Port

## Option 1: Security-First Gate

Every file, process, network, terminal, and credential operation must be denied
unless declared by the CLI manifest and backed by a SimpleOS capability grant.

Pros:
- Matches the risk profile of AI coding agents.
- Produces strong tests for host escape and credential safety.

Cons:
- Slower initial CLI bring-up because permissions must be modeled explicitly.

Effort: Medium.

## Option 2: Portability-First Gate

Prioritize getting a CLI smoke to start under QEMU, with hardening denials added
after basic Node/runtime compatibility is stable.

Pros:
- Faster feedback on Node/V8/libuv feasibility.
- Useful for discovering missing syscalls and ABI expectations.

Cons:
- Risk of normalizing ambient authority paths that later need removal.

Effort: Medium.

## Option 3: Reproducibility-First Gate

Require offline package inputs, pinned CLI versions, checksums, serial evidence,
and deterministic QEMU logs before expanding runtime features.

Pros:
- Avoids npm/network drift in CI and QEMU validation.
- Makes multi-arch evidence easier to compare.

Cons:
- Adds artifact-management work before user-visible CLI behavior.

Effort: Medium.

## Selection Needed

Choose the primary NFR gate. Recommended pairing with Feature Option A is
Option 1 plus the reproducibility pieces from Option 3.
