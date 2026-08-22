# MC/DC and HAL Runtime Hardening Requirements

**Selection:** full canonical feature (`B`), unique-cause with validated masking fallback (`M2`), isolated parallel providers (`P2`), governed REQ-018 exclusions (`E1`, expanded to the five explicitly selected causes below), immediate strictness for new/changed code (`R3`), mission-critical performance/memory tier (`NFR-C`).

- REQ-001: The compiler shall enumerate every eligible Boolean decision and atomic condition in a stable static manifest before execution.
- REQ-002: Interpreter, JIT, and supported native backends shall record correlated condition-evaluation vectors and final decision outcomes while preserving language short-circuit semantics.
- REQ-003: The analyzer shall prove unique-cause independence where possible and permit masking only when it proves all changed non-target conditions cannot influence the decision.
- REQ-004: Reports shall include gross, eligible, excluded, covered, and uncovered decision/condition totals, witnessed independence pairs, source locations, mode, binary identity, and deterministic cross-process merge provenance; an empty eligible denominator is not 100%.
- REQ-005: Every coverage-enabled promotion mode (`normal`, `alpha`, and
  `beta`) shall fail unless eligible MC/DC is exactly 100%; static-off and
  explicitly diagnostic reporting do not invoke the promotion gate.
- REQ-006: Static-off builds shall contain no coverage probes, branches, tables, symbols, sections, allocations, logging calls, dynload checks, or linked coverage payload.
- REQ-007: Static-on builds shall use direct bounded instrumentation, while dynamic builds shall use the canonical aspect/dynload loader with disarmable patchpoints and lazy pack activation.
- REQ-008: Dynamic-disarmed execution shall not map the coverage pack or allocate event/log buffers; activation, settlement, shutdown, overflow, and failure behavior shall be deterministic and bounded.
- REQ-009: A canonical `rt(hal)` declaration shall identify operation, assurance level, providers, capabilities, comparison/normalization semantics, side-effect authority, environment requirements, capacity contract, and error contract.
- REQ-010: Unqualified `rt(hal)` operations shall default to mission-critical assurance or higher; explicit lower assurance requires rationale and shall be rejected when reachable from a mission-critical entry closure.
- REQ-011: Mission-critical-or-higher entry closures shall perform zero dynamic allocations after their declared initialization boundary, including coverage, provider dispatch/comparison, environment capture/replay, log, error, timeout, and shutdown paths.
- REQ-012: Provider interfaces shall accept caller-owned or fixed-capacity storage and return typed overflow/capability/error results; hidden growth and silent evidence loss are forbidden.
- REQ-013: Pure Simple, C, and Rust providers shall run concurrently only in isolated provider environments and shall commit normalized comparison results through a deterministic parent authority.
- REQ-014: `alpha` shall stop on any applicable provider difference, `beta` shall emit a bounded critical difference report, and `normal` shall execute only the configured preferred provider; no configuration shall select the documented safe default.
- REQ-015: Existing I/O comparison shall migrate to the tagged provider path and compare representative file, stream, process, environment, clock, randomness, socket, interrupt, MMIO, and DMA result/error/interaction semantics.
- REQ-016: Runtime/HAL tests shall extract typed, versioned, bounded environment-access instructions, and isolated executors shall perform and record each interaction for deterministic provider replay/comparison.
- REQ-017: Unknown, malformed, missing, extra, reordered, duplicated, unsafe, timed-out, or overflowing environment instructions shall fail closed with structured evidence.
- REQ-018: A scenario may be excluded only for a validated unavailable capability, unavailable fixture, platform inapplicability, safety prohibition, or uncontrollable nondeterminism; the expression shall include stable code, human reason, predicate evidence, owner, and review/expiry, appear as excluded rather than PASS, and affect only the eligible denominator.
- REQ-019: New/changed runtime/HAL code shall immediately error on missing assurance classification, forbidden allocation, or obsolete interfaces; untouched legacy shall emit actionable warnings until the next release, when the same findings become repository-wide errors and compatibility shims are removed.
