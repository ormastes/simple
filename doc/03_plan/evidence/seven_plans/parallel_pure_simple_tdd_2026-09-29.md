# Seven-plan pure-Simple TDD progress

This is implementation progress, not a production verification report. No item
is certified complete on Windows or WSL. The canonical requirements and host
matrix remain in `doc/03_plan/seven_plans_host_completion_2026-09-29.md`.

| Item | Evidence-based implementation status | Remaining completion gates |
|---|---|---|
| 1. Platform unification | 22 umbrella requirements plus inherited parser/dynload/SimpleOS contracts; existing source slices | Authority convergence, qualified bootstrap, parser/provider scenarios, immutable release and live guest evidence |
| 2. Distributed textual databases | 36 requirements; identity validation plus a new pure candidate identity map | Durable settlement, authority/receipt integration, two-clone recovery; five system checkers remain fail-fast |
| 3. Typed collections and optimizer | 11 requirements; planner source exists | Production typed extraction/MIR integration, semantic prerequisites, cross-engine and performance evidence |
| 4. Linker | Contracts, ELF/COFF work, relocation and working-set owners exist; spill extent overflow fixed | Exact-head executable/compiler corpus, supported-format admission and performance evidence |
| 5. Optional providers and size | Metadata admission exists; terminal metadata overwrite fixed | Native provider qualification, real exclusion/size/startup/RSS evidence; synthetic fixtures cannot close these gates |
| 6. Compile optimization | All ten persistent-index matrix areas remain incomplete; cache-marker rejection fixed | Production graph publisher, full entrypoint cutover, invalidation and end-to-end performance; index plan is only part of umbrella scope |
| 7. Profile-selected containers | Eight requirements; containers, profile capture and explanation exist; initializer explanation corrected | Typed lowering, broader metrics, cross-backend execution; collision metric regression remains open |

Counts describe retained requirements, not implementation percentages. No
percentage is reported because source presence and isolated diagnostic passes
cannot determine completion of these mixed requirements.

## Test-first changes

All feature logic in this work is `.spl`. No C, C++, Rust, GCC, or cl.exe feature
implementation was added. Native toolchain selection remains Clang 23.1 and
clang-cl. Diagnostic interpreter runs do not establish native compiler use.

| Scope | Pre-fix failure | Post-fix diagnostic |
|---|---|---|
| Item 2 identity-map state | High-water retry regression; later duplicate/foreign bindings | 7/7 Windows, Phase 1; all three cycles used |
| Item 4 spill extent | Overflowing logical output range admitted | 6/6 Windows, Phase 1 |
| Item 5 provider finalization | Duplicate publication/rejection mutates terminal metadata | 13/13 Windows, Phase 1; native concurrency unverified |
| Item 6 compatibility markers | Rejected generation leaves old producer marker | 2/2 Windows and 2/2 WSL, Phase 1 |
| Item 7 constructor explanation | Factory/instance `.new()` falsely receives default policy explanation | New regression passes; file 8/9, collision value expected 40 but observed 100 |

The new identity map is a candidate-state transition owner. It does not persist,
authorize, or settle batches. Its duplicate validation is quadratic and no NFR
claim is made. Provider finalization reserves atomic state 3 before writing
metadata and exposes it as admitting; terminal publication uses release ordering.
Readers must use the existing acquire-based state API.

## Blockers and resume ownership

- Parent: Windows clang-cl still lacks Visual C++ runtime headers after installer
  exit 1602. Complete Build Tools setup, then validate the real native path.
- Parent: checked Windows/WSL lanes have no qualified deployed Stage 4 runner.
  WSL bootstrap previously stopped at compiler-test admission. Fix/admit that
  gate without a fabricated waiver before general SPipe or release execution.
- Item 7 owner: retain the collision-profile failure and diagnose in a new bounded
  task; its three-cycle allowance is exhausted. Do not weaken the expected metric.
- Parent: earlier runtime-compiler spec remains 10/12 and has exhausted its own
  three-cycle allowance. No rerun was performed by this parallel implementation.
- Parent: required compiler/lib/MCP/LSP checks, native runtime/MCP smoke,
  admitted SPipe/docgen/sspec-maintain, coverage and retained NFR gates remain open.
  A bounded `sspec-maintain scan` attempt on the known Phase 1 binary exited 1
  with `file not found: sspec-maintain`; no maintenance score is claimed and
  the unavailable command is not retried through a different fallback.

See `.spipe/seven_plans_parallel_pure_simple/state.md` for ownership. Agent
findings were reviewed by the parent; independent code review is retained in
the session. Publication is an implementation handoff, never release admission.
