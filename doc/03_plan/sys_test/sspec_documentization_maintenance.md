# SSpec Documentization Maintenance — System Test Plan

## Scope and traceability

The acceptance suite covers `REQ-001` through `REQ-012` and `NFR-001` through
`NFR-012` from the selected requirements. Unit tests own rule witnesses,
scoring, rendering, cache invalidation, fix conflicts, scaffold mapping, and
mirror derivation. Integration tests own CLI exit codes and machine-output
purity. The system specification owns the operator flow and generated manual.

## Fixed operator flow

1. Inspect the SSpec documentization baseline.
2. Review scored improvement findings.
3. Preview safe mechanical changes.
4. Confirm selected maintenance changes.
5. Generate and inspect the professional specification manual.

The executable scenario uses literal `step("...")` calls so SPipe docgen can
extract them. Helpers that are not implemented must call
`fail("TODO: replace generated placeholder with an executable assertion")`.

## Test inventory

- Unit: analyzer/rules, score, renderers, improvements, scaffold, cache, mirror.
- Integration: `simple sspec-maintain` help, operations, formats, gates, and
  preview/apply behavior.
- System: professional scoring, safe improvement, reference scaffolding,
  complete manual generation, compatibility/workflow inventory.
- Performance: warm single-pair p95 and deterministic 1,000-pair corpus.
- Rule coverage: `test/01_unit/app/sspec_maintain/rule_coverage_spec.spl` owns
  catalog completeness, practical false-positive limits, mirror structure,
  normalized ordering, and whitespace-stable fingerprints.
- Compatibility: `test/02_integration/app/sspec_maintain_compatibility_spec.spl`
  owns read-only help parity and isolated SPipe generation. Public
  `documentize` remains uninvoked until a subprocess-cwd harness prevents
  canonical repository manual replacement.

## Requirement-by-requirement evidence audit

| Requirement | Current executable evidence | Completion state |
|---|---|---|
| REQ-SSDOC-001 | CLI help/error, all operations, and isolated public `documentize` routing cases | Executable evidence present; self-hosted receipt pending |
| REQ-SSDOC-002 | Unit model, rule-catalog, finding, score, and baseline assertions | Covered by focused unit evidence |
| REQ-SSDOC-003 | Seven typed scores, deductions, blocker cap, tautology rejection | Covered by unit and system evidence |
| REQ-SSDOC-004 | Catalog-equality witnesses, professional no-finding fixture, and per-rule false-positive policy checks | Test source complete; focused runtime receipt remains required |
| REQ-SSDOC-005 | File/directory scans, byte-identical normalized public path order, policy exits, deterministic renderers, and machine purity | Executable evidence present; self-hosted receipt pending |
| REQ-SSDOC-006 | Missing/stale/current pairs, manual facts, and current-hash structurally incomplete mirror | Test source complete; focused runtime receipt remains required |
| REQ-SSDOC-007 | Preview, explicit apply, permission preservation, rollback, no-op repeat, overlap, stale helper, failed rollback write | Partial: a deterministic concurrent stale-file CLI fixture and exact once-only post-edit gate observation remain open |
| REQ-SSDOC-008 | Structured reference parse, source line/hash, mapping, visible steps/capture, deterministic fail-fast scaffold | Covered by unit, integration, and system evidence |
| REQ-SSDOC-009 | Idempotent SPipe-body composition plus isolated canonical public `documentize` staging/output | Partial until the public case and zero-stub canonical docgen receipt execute self-hosted |
| REQ-SSDOC-010 | Read-only help parity, isolated canonical `spipe-docgen` generation, and lint-owned SPIPE IDs | Partial until focused runtime and MCP metadata parity receipts exist |
| REQ-SSDOC-011 | Workflow guide/skill/template synchronization, eight-surface manifest, and system-manual review | Structural evidence present; final manual review receipt pending |
| REQ-SSDOC-012 | Unit, integration, system, and performance suites | Partial while the gaps above and branch-coverage receipt remain open |

| NFR | Current executable evidence | Completion state |
|---|---|---|
| NFR-SSDOC-001 | Repeated JSON/SARIF/scaffold/cache identities | Covered for pure owners; public directory byte ordering remains under REQ-005 |
| NFR-SSDOC-002 | Twenty-sample warm p95, 1,000 source/manual pairs, elapsed bound, Linux high-water RSS | Covered by the retained performance spec on Linux |
| NFR-SSDOC-003 | Per-pair reuse plus create/edit/delete/move/rename/manual/rule/config/tool invalidation and bypass parity | Executable evidence present; self-hosted receipt pending |
| NFR-SSDOC-004 | One report model renderers and public JSON/SARIF stdout/stderr purity | Covered by unit and integration evidence |
| NFR-SSDOC-005 | Stable fingerprints across line movement and whitespace, baseline states, reviewed suppression metadata, blocker refusal | Test source complete; focused runtime receipt remains required |
| NFR-SSDOC-006 | Read-only preview, atomic apply, mode preservation, rollback, overlap rejection, failed-write preservation, idempotence | Partial: concurrent stale-write rejection is not deterministically exercised |
| NFR-SSDOC-007 | Exactly one canonical isolated reparse per changed source before write, rollback, restore, and phase timing | Executable evidence present; failure-path self-hosted receipt pending |
| NFR-SSDOC-008 | No LLM dependency in core modules; guidance forbids automatic advice/apply | Partial: offline/no-network and opt-in advice isolation lack executable evidence |
| NFR-SSDOC-009 | Existing SSpec, stable SPIPE references, help parity, and isolated canonical docgen output | Partial until the compatibility spec runs successfully |
| NFR-SSDOC-010 | Cohesive files below 800 lines, public complexity table, one-enumeration/per-pair hot-path design | Static evidence present; retained runtime profile pending |
| NFR-SSDOC-011 | Separate scan parse/mirror/rule/render/cache and improve preview/conflict/reparse/write timings | Executable evidence present; self-hosted stderr-purity receipt pending |
| NFR-SSDOC-012 | Four test levels and reviewed manual | Blocked until >=80% branch-coverage and canonical zero-stub docgen receipts exist |

Current fixtures are inline deterministic text or isolated `/tmp` files removed
by their integration scenario. If retained generated SSpec goldens are added,
store them as `.txt` under `test/fixtures/sspec_documentization_maintenance/`
so test discovery cannot execute them.

## Required evidence

Assertions compare exact rule IDs, dimensions, scores, exit codes, fingerprints,
paths, byte strings, and parsed JSON/SARIF fields. Preview and declined fixes
leave bytes unchanged; apply preserves permissions, writes rollback material,
rejects overlap/staleness, reparses, and is idempotent. The scaffold records the
reference hash and emits visible fail-fast placeholders for unresolved facts.

The generated manual must contain Purpose and audience, Preconditions,
Operator workflow, Scenario narratives, Scorecard, Findings and remediation,
Evidence and provenance, and Compatibility and limitations. Native acceptance
uses the self-hosted runtime with stub fallback disabled.

## Performance and stop rule

Measure in-process warm p95 excluding startup, total time and maximum RSS for a
1,000-pair manifest, cache hit/miss counts, and phase timings. Run each gate once
per verification session and stop after convergence.

Retain these exact focused commands with their runtime identity and logs:

```text
bin/simple test test/01_unit/app/sspec_maintain/scoring_spec.spl --mode=interpreter
bin/simple test test/02_integration/app/sspec_maintain_cli_spec.spl --mode=interpreter
bin/simple test test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl --mode=interpreter
bin/simple test test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl --no-cache --min-score 80
```
