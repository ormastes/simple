<!-- codex-architecture -->
# Windows Bootstrap on Separate Hosts — TLDR

Run MSVC and MinGW Phase2 -> Phase3 -> next-compiler chains on separate native
Windows hosts. Linux cross-builds are diagnostic only. Each lane has immutable
producer/provider receipts and its own writable cache.

## Core shape

- Pin one clean source revision and exact seed/provider/tool identities.
- Never share Windows ABI objects or mutable caches; transfer only verified,
  immutable entries whose target/schema/action keys match.
- Reverse-reference/performance owns cache-key semantics; Windows owns host
  execution, cache transport, PE evidence, and admission. macOS remains separate.
- Promote tested digests without rebuilding; failed candidates preserve evidence
  and cannot replace the previous admitted manifest.

## Gates

- Phase 2 starts natively, compiles a file, and passes focused positive/negative contracts.
- Phase 3 is produced only by admitted Phase 2; next compiler is produced by Phase 3.
- Full CLI, test runner, lint/fmt/doc, MCP, and LSP build and pass minimal native sanity.
- Inspect PE machine/subsystem/sections/imports, ABI-specific linker policy,
  signatures, provenance, cold/warm time, cache counts, and peak RSS.
- No stubs, fallback, Rust-seed artifact substitution, cross-ABI object reuse, or
  shared cache writer.

## Ownership

- Sidecars: MSVC, MinGW, cache adversarial, PE/signing/rollback, tools sanity.
- Merge owner: Windows bootstrap integration owner.
- Final reviewer: independent normal/highest-capability reviewer.

## Open next

- [Full plan](windows_bootstrap_separate_hosts_nonconflicting_plan_2026-08-30.md)
- [macOS harmonization](macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md)
- [Canonical bootstrap](../../../scripts/bootstrap/bootstrap-from-scratch.sh)
- [Windows workflow](../../../.github/workflows/windows-build.yml)

