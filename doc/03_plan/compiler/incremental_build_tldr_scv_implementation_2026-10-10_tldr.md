# Incremental compiler implementation plan — TLDR

The selected 2026-10-08 design is mapped to 28 requirements and twelve work
packages. Implementation and native qualification are incomplete. This plan
does not claim a compiler speedup or successful full bootstrap.

- Reuse one SourceChange service, the existing SCV metadata/WAL, compiler cache
  gateway and scheduler; avoid separate durable stores and edit algorithms.
- Keep canonical `.tld`/`__init__.tld` package summaries. Adapt experimental
  `.tldr` data through an explicit versioned compatibility boundary.
- Preserve bootstrap's physical authority checks on a captured source
  projection, including changed inputs. Keep caches outside that projection.
- Source/header/AST/artifact reuse requires matching content, generation,
  producer, configuration and complete dependency coverage. Timestamps are hints.
- Publish a usable binary before optional postchecks, while mandatory checks
  remain necessary for qualified CI/release success.
- Production metadata uses SDN and framed binary. Private JSON diagnostic
  manifests are evidence tooling, not the production control plane.

The first shared byte-transition validator and its fifteen tests are authored
but unrun. The index diagnostic has seven passing cases, two failed fixtures,
and one topology timeout with unknown outcome. Native performance and complete
consumer integration remain unverified. The separate SIMD/GPU/SOSIX document
is unavailable and is not covered by this plan.

See [implementation plan](incremental_build_tldr_scv_implementation_2026-10-10.md)
and [acceptance matrix](../sys_test/incremental_build_tldr_scv_acceptance_2026-10-10.md).
