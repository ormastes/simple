# Software Development Plan (SDP)

Companion to `psac.md`; describes HOW the software is built (DO-178C §11.2). Target
grade: aero-d/auto-a nearest-achievable, assessed against aero-a for gap visibility.

## Development environment

- **Toolchain:** self-hosted `bin/simple` (built by bootstrap: Rust seed →
  `src/compiler_rust/target/bootstrap/simple` → compiles `src/compiler`+`src/lib`+
  `src/app` → self-hosted binary at `bin/release/<triple>/simple`). Per
  `.claude/rules/bootstrap.md` and `CLAUDE.md`: the self-hosted binary is the default
  tool for build/test/lint/fmt/MCP/LSP; the seed is bootstrap-only and never the
  shipped/certified artifact.
- **Build entry points:** `bin/simple build` (debug + bootstrap by default),
  `bin/simple build bootstrap` (3-stage self-compilation fixpoint check),
  `scripts/setup/setup.shs` (environment setup / symlink).
- **Host platforms:** Linux (primary CI), FreeBSD (QEMU-verified via
  `scripts/check/check-freebsd-bootstrap-qemu.shs`), plus riscv/arm64 embedded targets
  under `src/app/os`/`examples/09_embedded`.
- **VCS:** jj (Jujutsu) colocated with git, single `main` line, no branches
  (`.claude/rules/vcs.md`). Configuration management identity = commit id; no parallel
  branch-based release lines to reconcile for certification baselines.

## Coding and design standards

| Standard area | Artifact |
|---|---|
| Language rules (no inheritance, `Result`/`?`, generics `<>`, reserved words) | `.claude/rules/language.md` |
| Code style (no over-engineering, no dead code, report policy) | `.claude/rules/code-style.md` |
| Test discipline (BDD spec structure, import pattern) | `.claude/rules/testing.md` |
| Bootstrap discipline (extern additions require rebuild, pure-Simple-first) | `.claude/rules/bootstrap.md` |
| Repo structure / directory contract | `.claude/rules/structure.md`, root + child `FILE.md` manifests |
| Per-domain architecture rules | `doc/04_architecture/<domain>/<topic>/+rule/*.md` |
| VCS process | `.claude/rules/vcs.md` |

Enforcement: `bin/simple build lint` / `bin/simple build fmt` / `bin/simple build check`
run these as machine-checked gates, not just documentation; `scripts/check-workspace-root-guard.shs`
enforces the FILE.md manifest contract as a pre-commit hook.

## Development lifecycle

Follows the repo's numbered doc-phase pipeline (`.claude/rules/structure.md`), which
doubles as the DO-178C life-cycle-process mapping:

1. **Research** (`doc/01_research/<domain>/<topic>/`) — problem/prior-art capture.
2. **Requirements** (`doc/02_requirements/<domain>/<topic>/`) — `REQ-NNN` ids (620 defined
   repo-wide), `+nfr/`, `+feature/` auto-generated rollups.
3. **Plan** (`doc/03_plan/<domain>/<topic>/`) — this document's own layer; cert plans live
   under `doc/03_plan/cert/`.
4. **Architecture** (`doc/04_architecture/<domain>/<topic>/`) — includes `+adr/`
   (decision records), `+format/`, `+rule/` (the design-standards artifacts above).
5. **Design** (`doc/05_design/<domain>/<topic>/`) — detail design docs.
6. **Spec** (`doc/06_spec/`) — generated from executable SSpec `*_spec.spl`, mirrors
   `test/` paths; never hand-refactored (it is a derived artifact).
7. Implementation lands in `src/`; each change is expected to trace back to a `REQ-NNN`
   via `@req` links checked by `scripts/check/cert/check-req-traceability.shs`.
8. Tracking/reporting layers (`doc/08_tracking`, `doc/09_report`, `doc/10_metrics`,
   `doc/11_archive`) are auto-generated or auto-appended, never hand-refactored.

## Transition criteria

- **Research → Requirements:** problem statement + prior art documented; no code started.
- **Requirements → Plan:** `REQ-NNN` ids assigned and stable enough to plan against.
- **Plan → Architecture:** plan reviewed (this SDP/PSAC/SVP triad, or domain plan doc)
  and does not require re-scoping.
- **Architecture → Design → Implementation:** `+rule/` constraints exist for the domain;
  no implementation merges to `main` without passing `bin/simple build check`
  (lint + fmt --check + tests) — this is the de facto DO-178C transition-criteria gate
  since there are no separate release branches to gate.
- **Implementation → Verified:** requirements-based `*_spec.spl` exist and pass under
  `bin/simple test`; traceability checker shows the change's REQs are not new orphans.

## Gap

1. Transition criteria above are process convention enforced by hooks/CI, not a
   documented, liaison-reviewed DO-178C SDP with formal review-record sign-off per
   transition — no independent (non-author) review gate is currently machine-enforced.
2. No configuration management **baseline/label** step tied to certification milestones
   (e.g., "SOI-2 baseline = commit X") — jj commit ids are used ad hoc, not formally
   tagged for cert purposes.
3. Tool qualification of `bin/simple` itself (the development tool) per DO-330 is only
   partial (bootstrap fixpoint, no qualified validation corpus) — see `svp.md` and
   `cert_roadmap.md` Phase 7 / task C7.
4. No externally audited SDP review; this document is self-authored pending a real
   liaison/DER engagement (mirrors the PSAC gap).
