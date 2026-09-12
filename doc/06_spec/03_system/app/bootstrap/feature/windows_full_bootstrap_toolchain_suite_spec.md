# Windows Full Bootstrap and Toolchain Suite

> Authored design mirror. Regenerate from the executable SSpec with the admitted Stage 4 CLI before verification; zero stubs is required. Current status: intentionally RED because production evidence helpers are not yet wired.

## Purpose and audience

This manual guides the Windows bootstrap operator through exact phase admission, compiler/interpreter checks, interpreter/native tool verification, integrated suites, protected publication, local deployment, and rollback.

## Primary workflow

1. **Admit the phase compiler and provenance** — freeze conflict-free source; retain absolute subject path/hash, source/toolchain/parent identity, command, bounded logs, and typed admission.
2. **Check compiler and interpreter behavior** — execute focused compiler and authenticated interpreter oracles against the same exact subject.
3. **Run essential tools in interpreter and native modes** — verify supported tool commands, native artifacts, and primary features without fallback.
4. **Verify integrated tool suites** — exercise MCP/LSP protocol flows, SPipe/docgen, DevHub, Caret, IDE, and T32; keep unavailable provider rows BLOCKED.
5. **Review and publish the exact phase head** — fetch/rebase, identify invalidated evidence, perform exact-head SPipe self-review admission, and push linearly.
6. **Deploy and prove rollback** — atomically select one immutable Stage 4 generation, smoke it, compare-select the predecessor, and verify the restored digest.
7. **Run bootstrap platform handoff readiness** — retain Gate 1 through Gate 6 in order; preparation never substitutes for admission.

## Evidence and failure handling

Each step links typed `exec`, `log`, `binary`, `artifact`, or `protocol` evidence under `build/bootstrap/evidence/windows/<generation>/`. Missing verdicts or changing binary identity are INCONCLUSIVE. Missing prerequisites are BLOCKED with owner and resume command. Invalid hashes, fallbacks, mixed generations, unauthorized review, or behavioral mismatches are FAIL.

## Troubleshooting

- Do not run while jj conflict markers remain.
- Do not use the Rust seed, `bin/simple`, a raw source entrypoint, or an old build as phase evidence.
- Do not repeat an identical failed command; stop after three distinct fix cycles.
- Regenerate this manual with `bin/simple spipe-docgen test/03_system/app/bootstrap/feature/windows_full_bootstrap_toolchain_suite_spec.spl --output doc/06_spec --no-index` only after an admitted Stage 4 CLI exists.
