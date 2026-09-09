# Vulkan 2D C/Simple immutable-run protocol — 2026-09-10

This change makes the C Vulkan / Simple comparator publish each live
invocation once under:

```text
build/vulkan-2d-c-compare/runs/<run_id>/
```

`VK2D_RUN_ID` is validated as a bounded path-safe identifier.  If it is
omitted, the wrapper generates a UTC timestamp plus process identifier.  A
pre-existing run identifier is a hard collision; the producer does not reuse,
truncate, or overwrite that directory. A deterministic private 0700 staging
directory is also the atomic reservation for that run identifier. Receipts are
published with one same-directory rename after all producer streams,
runtime/toolchain receipts, rows, framebuffers, and aggregate output are
closed. Trapped failures remove partial staging; an untrappable crash may leave
a non-authoritative hidden reservation, which fails closed instead of allowing
that identifier to be reused.

The `latest` file is an atomic convenience pointer with
`authoritative=false`.  It is never accepted by `--aggregate`; only a direct
published `runs/<run_id>` directory can be an aggregate input. Inability to
update `latest` does not invalidate an already-published run. Aggregation
checks the manifest identity, canonical run path, regular-file constraints,
and hashes for both projected rows, the combined raw row, aggregate output,
producer streams, and runtime or toolchain receipts. This prevents stale,
copied, linked, mutated, or mutable pointer input from becoming performance
evidence.

Each live run retains C and Simple stdout/stderr, runtime receipts, the C
toolchain receipt, and both framebuffer paths, including explicit empty raw
streams for a leg skipped before launch. Receipt rows bind source,
binary, fixture/config, device/ICD, and artifact hashes where a leg ran; the
run manifest records the explicit scene-fixture, shader, workload-config, and
ICD digests even when a leg is skipped.

No Vulkan or benchmark process was launched for this change.  The focused
contract test forces the C leg to skip before launch and verifies two distinct
runs, collision refusal, stale/latest rejection, and direct-run aggregation:

```text
vulkan_2d_c_evidence_contract=pass
vulkan_2d_c_immutable_runs_contract=pass
```
