# Migrating an old-style SSpec capture onto typed evidence

Task: E8 "legacy adapter migration",
`doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`.

The old `ScenarioEvidenceArtifact` API (`scenario_evidence.spl` /
`scenario_helpers.spl`) is frozen and not being rewritten. The new typed-evidence
pipeline (`src/lib/common/spec/evidence/model.spl` — `CanonicalEvidence`,
`OracleSpec`, `compare_evidence`) is fail-closed: it rejects vacuous oracles,
unresolved selectors, and ignore-without-reason. `legacy_facade.spl` is the
one-way adapter that lets an old-style capture flow into that pipeline, so an
existing spec can gain a real typed-evidence check without being rewritten.

This is an **additive** migration pattern: keep every existing assertion
exactly as it is, and add a new block right after the artifact capture that
converts it and checks it again through the new comparator.

## The three calls you need

```spl
use std.common.spec.evidence.legacy_facade.{legacy_evidence_to_canonical}
use std.common.spec.evidence.model.{oracle_spec_open, check_exact, EvidenceStatus}
use std.common.spec.evidence.evidence_comparator.{compare_evidence}
```

1. `legacy_evidence_to_canonical(artifact: ScenarioEvidenceArtifact) -> CanonicalEvidence`
   — converts the artifact you already captured into 8 named nodes:
   `kind`, `title`, `mime`, `path`, `body`, `scenario_id`, `step_id`,
   `redacted`. Every field the old API defines becomes its own node.
2. `oracle_spec_open(profile_id, checks)` — builds an **open** oracle (not
   `oracle_spec`, which is `closed: true` and would fail on every node you
   don't explicitly check — you almost never want to enumerate all 8 legacy
   fields). Use `check_exact(path, expected)` per node you want to assert.
3. `compare_evidence(canonical, oracle) -> ComparisonResult` — fail-closed
   evaluation. Assert `comparison.status == EvidenceStatus.passed`.

## What NOT to change

- Do not delete or weaken any assertion the spec already has.
- Do not touch `it` blocks you are not migrating.
- Do not use `oracle_spec` (closed) unless you genuinely list every node —
  otherwise the closed-mode check fails on the fields you didn't mention,
  which is a *different* bug than the one you're testing.
- Every `check_exact("body", ...)` must match the **exact** string the
  underlying `scenario_*_evidence` constructor builds (see
  `src/lib/common/spec/scenario_evidence.spl`), not a paraphrase — the
  comparator does exact string equality, not "contains".

## Worked example 1 — `test/01_unit/app/simple_lab/lab_html_render_spec.spl`

Before (existing, untouched):

```spl
val evidence = capture_html(
    "Simple Lab fresh notebook page",
    html,
    "cell editor, Run button, lane status",
    ""
)
expect(evidence.mime).to_equal("text/html")
```

After (added directly below, same `it` block):

```spl
val canonical = legacy_evidence_to_canonical(evidence)
val oracle = oracle_spec_open("lab_fresh_notebook_page_evidence", [
    check_exact("kind", "html"),
    check_exact("title", "Simple Lab fresh notebook page"),
    check_exact("mime", "text/html")
])
val comparison = compare_evidence(canonical, oracle)
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

The same pattern was applied a second time in the "document shell" `it`
block, checking the `capture_html(...)` call there (renamed the previously
unused `_evidence` binding to `page_evidence` so it could be referenced).

## Worked example 2 — `test/01_unit/lib/common/spec/scenario_helpers_spec.spl`

Before (existing, untouched):

```spl
val artifact = capture_exec_response(
    "MCP stdio command",
    "simple_mcp_server --stdio",
    0,
    "stdout: initialize result"
)
expect(artifact.kind).to_equal(ScenarioCaptureKind.exec)
expect(artifact.body).to_contain("$ simple_mcp_server --stdio")
expect(artifact.body).to_contain("exit: 0")
expect(artifact.body).to_contain("stdout: initialize result")
```

After (added directly below):

```spl
val canonical = legacy_evidence_to_canonical(artifact)
val oracle = oracle_spec_open("capture_exec_response_evidence", [
    check_exact("kind", "exec"),
    check_exact("title", "MCP stdio command"),
    check_exact(
        "body",
        "$ simple_mcp_server --stdio\nexit: 0\nstdout: initialize result"
    )
])
val comparison = compare_evidence(canonical, oracle)
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

Note the `body` check is exact and derived from `scenario_exec_evidence`'s
own format string (`"$ " + command + "\nexit: " + "{exit_code}" + "\n" +
output_summary`), not the `.to_contain(...)` substrings the pre-existing
assertions use — typed evidence checks the whole node value, not a fragment.

The same pattern was applied a second time to the "captures basic API
response evidence" `it` block, checking a `capture_api_response(...)`
artifact instead of an exec one (`kind == "api"`, exact `body` built from
`scenario_api_evidence`'s `method + " " + path + "\nstatus: " + status +
"\n" + response_summary` format).

## Verifying the migration is a real check, not decoration

Temporarily change one `check_exact("title", ...)` expected value to
something wrong and re-run the file — exactly one example should fail with
a `ComparisonResult.status != passed` (surfaced as `expected ... to equal
...` on the `EvidenceStatus.passed` assertion). Revert and re-run to confirm
green again. Both worked examples above were verified this way.

## Sweep progress

Migrated so far (typed-evidence checks added, additive, all pre-existing
assertions kept):

1. `test/01_unit/app/simple_lab/lab_html_render_spec.spl`
2. `test/01_unit/lib/common/spec/scenario_helpers_spec.spl`
3. `test/01_unit/lib/common/spec/evidence/legacy_facade_spec.spl`
4. `test/01_unit/lib/common/spec/scenario_evidence_spec.spl`

**Corpus note (2026-08-08):** a full search of `test/01_unit/` and
`test/02_integration/` for `scenario_helpers`/`scenario_evidence` usage turns
up exactly 5 files total. With the 4 above migrated, only one file remains:
`test/02_integration/app/mcp_stdio_integration_spec.spl`. It imports
`capture_api_protocol_fields`/`capture_exec_detailed` but never calls them —
no artifact exists there to convert — and, independent of that, the spec
does not currently pass in this checkout (`bin/simple_mcp_server` is not
built, so 2 of 3 examples fail before any edit, confirmed by re-running the
unmodified file). It was rejected as a candidate rather than migrated onto a
already-failing baseline. The next migrator should either build the MCP
server binary and add a real `capture_exec_detailed` call there, or widen
the search (e.g. `test/03_system/`) to find further real candidates — the
"five more" target could not be reached from this corpus as scoped.
