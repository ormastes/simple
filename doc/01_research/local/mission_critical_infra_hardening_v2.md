<!-- codex-research -->
# Local Research: Mission-Critical Infrastructure Hardening V2

Date: 2026-08-11

## Scope and baseline

This lane joins production Simple compiler/tooling, SimpleOS, rendering, and a narrowly bounded relaxed-allocation policy. The one permitted baseline run of `scripts/check/check-simpleos-hardening-evidence-matrix.shs` stopped fail-closed with nine stale reports (37–43 days old), covering WM/renderer unification, SIMD, LLVM, RenderDoc, GUI/Web parity, Engine2D/JS, and QEMU/WM capture. Evidence was retained at `/tmp/simpleos-hardening-v2-baseline.out`; the unchanged command must not be rerun until a blocker is changed.

The older `.spipe/mission_critical_harden` lane covers a narrower compiler campaign and must not be treated as completion evidence for this V2 scope. The V2 acceptance contract is `.spipe/mission_critical_infra_hardening_v2/state.md`.

## Compiler and tooling

- `scripts/check/check-compiler-provenance.shs` distinguishes compiler lineage using resolved identity, symbols, and optional executable probes. The currently deployed `bin/simple` identifies as the Rust bootstrap seed with hybrid lineage, so it is not the required production pure-Simple self-host.
- Substantial fail-closed checks already exist for bootstrap essential tools, portability, seed/native parity, provenance, Stage-4 parsing/multifile/RSS, runtime contracts, emitted functions, environment/process facades, and pre-push conflict/vacuity checks.
- The current hardening matrix does not aggregate all compiler, library, MCP/LSP, lint, duplication, whole-suite, latency, and RSS evidence required by AC-3.
- Current blockers include an unresolved index conflict in `src/compiler/70.backend/backend/runtime_compiler.spl`, concurrent compiler edits, Stage-3 native-build crashes after successful parsing, missing Stage-3 MIR entry accumulation, insufficient native-build artifact-success validation, and incomplete discriminating regressions for silent miscompiles.
- Formal compiler models cover selected properties but do not prove semantic preservation across parser, HIR, MIR, backend, linker, and executed artifact.

## SimpleOS, storage, and formal evidence

- `scripts/check/check-simpleos-hardening-evidence-matrix.shs` owns a 26-row aggregate. Mission release further depends on prerequisite classification, RTL/SBY, QEMU scheduler handoffs, NVMe wrapper coverage, async hardening, and stale-report rejection.
- `src/os/sosix/qemu_evidence/matrix_contract.spl` enforces exactly 24 unique host/guest cells, evidence for PASS, and reason/artifact/resume/ownership data for nonpass rows. `scripts/qemu/simple-big-storage-root.shs` owns storage-root resolution and isolation.
- Existing critical, memory, storage, boundary, and RISC-V formal gates are substantive and mutation-tested, but their assumptions and platform scope remain part of the claim.
- Linux diagnostic guests cover five ISAs, but release admission is blocked by pure-Simple compiler lineage, source identity, nonce correlation, missing x86_64 filesystem executable, ARM64 zero-byte execution plus fabricated weak stubs, incomplete macOS/Windows host preparation, and unavailable genuine virtio-GPU/Venus evidence on this host.
- No named/versioned relaxed-allocation profile currently joins quotas, prohibited contexts, deterministic exhaustion recovery, telemetry, fault injection, and proof.

## Rendering and memory/concurrency

- `src/lib/common/ui/draw_ir.spl` is the canonical immutable semantic boundary. GUI/Web producers should emit `DrawIrComposition`; Engine2D consumes it. Durable Draw IR excludes renderer handles, atlases, and caches, while text uses transient `FontRenderBatch` material.
- Existing Engine2D paths include a fresh-device font-work limit and strict Vulkan validation. GPU readback uses generation guards and bounded phase drains.
- Draw IR commands and nested payloads remain growable without a composition-wide capacity manifest or overflow receipt. The GPU event queue limits packet size/drain count but has no queue-depth admission/backpressure cap. `GenArena` is generation-safe but grows on exhaustion.
- Existing designs already specify the likely owner path: a pre-reserved packed DrawIR-v3 arena, count/scan/verify admission, explicit rejection, and growth only between generations.
- Current reports explicitly block Simple 2D RenderDoc equivalence, live SimpleOS GPU submit/readback, QEMU on-screen WM rendering, Windows Vulkan/D3D12, and broad render-decision coverage. Stage-4 has also reached roughly 111 GiB RSS, while an eviction path reclaimed zero memory.
- Formal concurrency models cover Acquire/Release/SeqCst and selected DRF properties. There is no established relaxed-atomic contract; any use must be confined to telemetry/monotonic counters with no publication, lifetime, ownership, or isolation role.

## Canonical evidence set

After ownership conflicts and blockers change, run each applicable command once: compiler provenance with probe; bootstrap essential/portability/seed invariants; native parity; compiler/lib/MCP/LSP checks; MCP stdio integration; runtime-contract and emitted-function gates; Stage-4 parse/multifile/RSS; changed-file lint and owned-directory duplication; whole interpreter tests; direct-env working/staged audits; SimpleOS prerequisite/release/matrix/formal/NVMe/QEMU contracts; production GUI/Web parity, Vulkan readback, RenderDoc, 2D backend equivalence, Engine2D scheduling, and memory-deallocation ownership checks. Evidence must execute discriminating artifacts and retain provenance, not merely report file existence or exit zero.

## Research conclusion

The repository has strong gate infrastructure and architecture direction, but current evidence contradicts an umbrella mission-critical claim. The most defensible path is staged: first establish an exact-current fail-closed compiler/tooling baseline and freshness recovery; then introduce bounded arena/queue allocation with explicit receipts; then close certified SimpleOS/rendering platform rows; finally add diverse/reproducible bootstrap and semantic-preservation evidence.
