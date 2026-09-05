# Architecture Folder — TLDR

`doc/04_architecture/` holds long-lived architecture decisions, system
structure, runtime boundaries, subsystem architecture, ADRs, and format
architecture.

## Organization

| Location | Purpose |
|----------|---------|
| `README.md` | Folder index and policy |
| `<feature>.md` | Architecture for a feature, subsystem, platform, or runtime |
| `<feature>_tldr.md` | One-screen summary beside the source doc |
| `adr/` | ADRs only |
| `format/` | File/wire format architecture |
| `rule/` | Engineering and architecture rules |

## TLDR Rule

For any long architecture doc, create a companion with the same base name:

```text
xxxxx.md -> xxxxx_tldr.md
README.md -> README_tldr.md
format/smf_specification.md -> format/smf_specification_tldr.md
```

Skip files already ending in `_tldr.md`.

## TLDR Contents

A TLDR should fit on one screen and cover:

- purpose of the source doc
- core decision or structure
- startup, hot path, cache/index, invalidation, and perf/RSS notes if relevant
- links to the few source/test/report paths a maintainer should open next

Do not move existing architecture files just to reorganize the folder. Update the
index and add TLDR companions first.
