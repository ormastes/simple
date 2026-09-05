<!-- codex-research -->
# NFR Requirements: SSpec Documentization Maintenance

Status: Selected
Date: 2026-08-03
Selection: NFR Option B — CI-ready and LLM-friendly

## NFR-SSDOC-001 — Determinism

Identical inputs, configuration, tool version, and cache state shall produce
byte-identical JSON/SARIF reports, scores, finding order, fingerprints, preview
patches, and reference scaffolds. Human timestamps/history may appear only in
explicit nondeterministic presentation fields excluded from identity checks.

## NFR-SSDOC-002 — Performance

On the standard Linux verification host:

- warm analysis of one representative changed SSpec shall have p95 <= 500 ms,
  excluding initial CLI process startup;
- analysis of 1,000 representative SSpec/manual pairs shall complete in <= 30
  seconds;
- max RSS for that scope shall be <= 384 MiB.

The benchmark fixture and exact command shall be retained. If the current
runtime cannot meet a target after three measured fix cycles, record a concrete
performance bug rather than weakening or omitting the target.

## NFR-SSDOC-003 — Incremental invalidation

Content identities shall permit unchanged SSpec/manual pairs to reuse cached
analysis. Create, edit, move, rename, delete, generated-manual refresh, rule
version, configuration, and tool-version changes shall invalidate precisely.
`--no-cache` shall reproduce the same report as a valid cached run.

## NFR-SSDOC-004 — Machine output

Human, JSON, and SARIF-compatible forms shall serialize one report model. JSON
and SARIF stdout shall contain no banners, progress, logs, color, or patch text.
Schema version, rule version, tool version, normalized path, source identity,
and cache disposition shall be explicit.

## NFR-SSDOC-005 — Stable baselines

Findings shall carry stable fingerprints and baseline state at least `new`,
`unchanged`, and `resolved`. Normal whitespace edits or unrelated line movement
shall not create a new fingerprint when the same rule/evidence remains
identifiable. Suppressions shall require rule ID, owner, and reason.

## NFR-SSDOC-006 — Safety and recoverability

Scan and default improve shall perform no writes. Interactive/apply changes
shall be conflict-checked and atomic, retain a rollback patch, preserve file
permissions, reparse before replacement, and leave the source unchanged on any
failure. Applying the same safe set twice shall be a no-op the second time.

## NFR-SSDOC-007 — Verification after change

Each applied safe edit shall run the smallest applicable reparse/format/check
gate exactly once. An edit shall not automatically launch a full repository
test. Verification failure shall return nonzero, preserve diagnostic evidence,
and leave an actionable rollback path.

## NFR-SSDOC-008 — Offline and LLM safety

Core scan, score, improve, scaffold, and documentize behavior shall work fully
offline and shall not transmit source. Future LLM advice shall be opt-in,
identified as nondeterministic, source-evidenced, and preview-only until an
explicit human confirms an exact patch. LLM output shall not affect the
deterministic score or invent passing assertions.

## NFR-SSDOC-009 — Compatibility

Existing valid SSpec shall continue to run unchanged. Existing
`simple spipe-docgen` invocations shall preserve default output/exit behavior
unless this feature's new flags are used. Existing `SPIPE001..007` IDs and lint
configuration shall remain stable.

## NFR-SSDOC-010 — Maintainability

Production files shall remain <= 800 lines unless explicitly justified. The
CLI shall be a thin adapter; analyzer, score rules, renderers, cache, scaffold,
and improvement application shall be cohesive modules. Public functions shall
state complexity; the hot analyzer shall avoid repeated full-file reads,
subprocesses, and quadratic concatenation.

## NFR-SSDOC-011 — Observability

Debug/perf diagnostics shall expose parse, mirror lookup, rule evaluation,
rendering, cache hit/miss/invalidation, and apply/verification timing without
polluting machine stdout. Full-tree maintenance scans may enumerate the tree
once; changed-file or cached analysis shall not repeat full-tree scans.

## NFR-SSDOC-012 — Coverage and documentation quality

New analyzer/scaffold/improve/docgen branches shall target >= 80% branch
coverage. Focused system scenarios and their generated manual shall cover every
feature REQ and NFR mechanism. The manual shall be independently reviewed as an
operator specification and the generator shall report zero stubs for completed
tool scenarios.
