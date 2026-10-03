# Seven-item 06 pending umbrella acceptance

Status: NOT_IMPLEMENTED applies to these new scenario bodies only. Existing implementation and coverage remain intact. No runtime execution or completion is claimed.

Sources: `doc/03_plan/seven_plans_host_completion_2026-09-29.md` section 6; `doc/04_architecture/compiler/perf/persistent_package_module_index_compile_optimization.md`. The umbrella explicitly requires locating the canonical final optimization plan; the related index architecture alone cannot certify that full scope. No numbered requirements are invented.

## S7-I06-AC01 — Retain the full canonical compile optimization scope

- Requirement source: seven-item plan section 6 scope inventory.
- Status: NOT_IMPLEMENTED.
- Setup: Pin the requested final optimization plan and its research, architecture and implementation inventory; retain unresolved canonical-plan discovery explicitly.
- Action: Map every retained requirement to its actual pipeline stage and decisive acceptance evidence.
- Observable: No requirement is replaced by the related package-index document; every missing stage or authority has a named pending gate.

## S7-I06-AC02 — Measure clean warm no-op and single-module builds

- Requirement source: seven-item plan section 6 baseline and NFR gate.
- Status: NOT_IMPLEMENTED.
- Setup: Pin source/toolchain hashes, fixture sizes and architecture-specific admitted baselines.
- Action: Perform clean, warm, no-op and single-module-edit builds while recording parse/type/lower/codegen/link phases.
- Observable: Timing, CPU and peak RSS records identify each mode and stage; retained performance targets are compared against admitted baselines with no guessed thresholds.

## S7-I06-AC03 — Compile only the reached dependency closure without recursive scanning

- Requirement source: persistent index invariants 1-4 and no-scan enforcement.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare an immutable package index with reached and unrelated packages, bounded TLDR headers and lazily indexed export sections.
- Action: Compile the selected package from the pinned source view.
- Observable: Receipts show only reached graph nodes/sections, no unrelated source opens or recursive discovery and the expected executable behavior.

## S7-I06-AC04 — Invalidate exact import and public-interface consumers

- Requirement source: seven-item plan section 6 semantic invalidation.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a dependency graph with typed reverse consumers and unrelated packages plus import and public-interface edits.
- Action: Compile each frozen edited snapshot through incremental planning.
- Observable: Changed owners and required consumer SCCs rebuild; unrelated SCCs remain reused; results equal a clean uncached build.

## S7-I06-AC05 — Reject stale configuration target compiler and provider witnesses

- Requirement source: persistent index invariant 7 and seven-item semantic invalidation.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare warm receipts then independently change configuration, selected target, compiler bytes and provider/tool witnesses.
- Action: Request incremental compilation for each changed cohort.
- Observable: Old cache admissions refuse or rebuild affected work; receipts bind the actual new cohort and resulting behavior matches uncached compilation.

## S7-I06-AC06 — Invalidate generated sources without consuming live workspace drift

- Requirement source: persistent index generated sources and SCV freeze boundary.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare generated-source recipes and a pinned SCV source view while another writer changes live files.
- Action: Change a declared generator input and compile through the source-view owner.
- Observable: Declared generated-source owners and exact consumers invalidate; the pinned request consumes only frozen identities and concurrent edits affect a later request.

## S7-I06-AC07 — Recover corrupt and hostile cache content without partial success

- Requirement source: seven-item corrupt-cache recovery and persistent cache boundary.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare local and remote content records with corrupted bytes, stale witnesses and a prior complete index generation.
- Action: Request warm compilation and exercise explicit bounded rebuild recovery.
- Observable: Corrupt/untrusted records never authorize dependencies or outputs; valid fallback rebuild equals uncached behavior and prior complete state remains recoverable.

## S7-I06-AC08 — Publish deterministic generations across interruption and concurrent writers

- Requirement source: persistent index atomicity recovery and invariant 6.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare two private writers, pinned readers and prior complete CURRENT state.
- Action: Interrupt staging/publication and race complete writers, then restart the daemon.
- Observable: Readers observe exactly a complete prior or new generation, never mixed state; pins survive cleanup and parent-authoritative commit order is deterministic.

## S7-I06-AC09 — Preserve bootstrap core MCP and LSP behavior across hosts

- Requirement source: seven-item section 6 product and host completion gates.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare affected full compiler/core runtime/MCP/LSP fixtures on separate Windows, WSL, Linux, macOS, FreeBSD and admitted target rows.
- Action: Build using optimized and uncached paths and run each required host-specific product smoke.
- Observable: Output/status and language/tool behavior match; each host/architecture has its own evidence, missing runners remain pending and no host is certified by another lane.
