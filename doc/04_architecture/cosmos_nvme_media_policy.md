# Cosmos NVMe Media Policy Evidence Boundary

## Scope

`cosmos_nvme_media_policy.spl` is the allocation-free scalar owner for the
Cosmos NVMe command, dispatch, retry, and FTL-media decisions. C continues to
own pointer storage, volatile DMA/MMIO, callback invocation, byte codecs, and
the media single-flight atomic. This split supports REQ-004/REQ-011 and
NFR-006/NFR-010 without treating host evidence as board acceptance.

The stable ABI is version 1 with 36 exported functions. Its three consumers
are intentionally separate:

- `cosmos_nvme_firmware.c`: 11 policy imports and 3 public service exports.
- `cosmos_nvme_dispatch.c`: 2 policy imports and 2 public dispatch exports.
- `cosmos_nvme_ftl_media.c`: 16 policy imports and 8 public media exports.

The checker links those unchanged ARM C objects with the generated ARM Simple
object and rejects any unresolved `cosmos_nvme_media_policy_*` relocation.
Shared Cosmos build, link, and receipt scripts are outside this lane.

## Independent evidence

The frozen C oracle uses only `cosmos_nvme_media_oracle_*` names and does not
include, import, or define the production policy ABI. The integration runner
contains exactly 196 boundary rows, including signed lookup-status input, and
pins digest `b6a2f693699eb752`. The digest binds each function identifier,
argument count, runtime argument value, result, and row. In normal mode it
compares the independent C result with the generated Simple export; in C-only
mode the same rows drive the oracle's 259 LLVM branches. C11 compile-time type
assertions pin all 36 production and all 36 oracle function signatures.

Production Simple coverage has no handwritten counters. Sixty-three stable
`# @decision` markers are bound by source hash and name/order in
`cosmos_nvme_media_policy_decision_audit.sdn`. An admitted Stage-4 compiler
instruments the production owner, and the checker maps its 63 runtime rows to
the marker line and requires both edges for all 126 outcomes.

## Trust and failure states

Source, C-oracle, vector, C-coverage, and ARM consumer-object checks may run as
transient diagnostics without a Simple runtime, but they do not publish or
retain a PASS receipt on their own. Simple parity, compiler edge coverage,
focused unit execution, host/ARM object identity, and the final link receipt
are `BLOCKED` unless `SIMPLE_STAGE4_BIN` names an admitted current-tree Stage-4
compiler with adjacent valid provenance. Seed, Stage-2, and Stage-3 fallback
is forbidden. The completed receipt is policy-only evidence; it makes no QEMU,
silicon, endurance, or whole-NVMe claim.
