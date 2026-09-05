# Target-bound installed-artifact lookup v1

## Purpose

Filesystem launchers for servers, Simple tooling, Clang/LLVM, and primary
utilities must not consume authenticated metadata for a different SimpleOS
architecture or ABI. The installed-artifact catalog previously exposed only a
path lookup, leaving this check to every launcher.

## Contract

`installed_artifact_catalog_lookup_target_v1(path, target)` is package-private
to the loader. Its target must come from the loader/platform owner's current
admission context, never from the candidate manifest or an app request. It
returns a snapshot only when both the catalog record target and signed manifest
target exactly equal that OS, architecture, and ABI tuple.

The operation is metadata-only. It does not mint or replace an executable
authority token. Invalid or mismatched loader-context targets return `nil`
without quarantining a sound sealed catalog. Existing path-only lookup remains
for diagnostics and compatibility but fails closed when the path is retained
for multiple target tuples. If the catalog record target and its
signed manifest target disagree, the owner quarantines the catalog before
considering the request because that is retained-state corruption.

## Safety and cost

The key lookup is expected `O(path + os + arch + abi)` and bounded by 2048
open-addressing probes. It
runs against the immutable sealed slot before nested copying, canonical
serialization, and hashing, so a mismatch cannot amplify that work. It adds no
permanent allocation, cache, scan, or mutable state. A match returns the same
bounded deep copy already produced by the catalog owner.

## Remaining integration

Each filesystem launcher still needs its own loader-owned consume-once
authority flow. Loader code must call this target-bound lookup with its
platform-owned admission target before artifact adoption.
No x86, ARM, or RISC-V launch is claimed by this prerequisite alone.
