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

## Untyped-capture adapter (`untyped_capture.spl`)

Design: `doc/05_design/infra/sspec/untyped_evidence_migration_design.md`.

`legacy_facade.spl` above adapts specs that already build a
`ScenarioEvidenceArtifact`. Most existing specs never do that — they assert on
a raw captured value (process stdout, rendered UI/terminal text, a log line)
directly with `to_contain`/`to_equal`, with no evidence envelope at all.
`src/lib/common/spec/evidence/untyped_capture.spl` is the adapter for exactly
that shape:

```spl
use std.common.spec.evidence.untyped_capture.{untyped_capture, untyped_capture_to_canonical}
use std.common.spec.evidence.model.{oracle_spec_open, check_exact, EvidenceStatus}
use std.common.spec.evidence.evidence_comparator.{compare_evidence}

val capture = untyped_capture("status line", raw_output, "stdout")   # source_kind: "stdout" | "rendered_text" | "log_line"
val evidence = untyped_capture_to_canonical(capture, "my_profile_id")
val comparison = compare_evidence(evidence, oracle_spec_open("my_profile_id", [
    check_exact("value", raw_output)
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

It wraps the raw value into exactly one `EvidenceNode` at path `"value"`,
tagged by `source_kind` — no structure inference. An empty `raw_value` still
produces a valid node (a legitimate captured value, e.g. no stdout produced,
not the same as a missing capture). An unrecognized `source_kind` fails
closed via `canonical_evidence_parse_error` instead of silently mislabeling
the evidence.

**Triage rule (do not skip this) — per the design doc's three categories:**

1. **Category 1 (in scope):** a real captured value (process stdout, rendered
   text) asserted with `to_contain`/`to_equal`, never wrapped in any evidence
   artifact. Convert this.
2. **Category 2 (out of scope):** an in-memory value the spec computed
   directly, with no external capture. Do not touch — forcing a
   `CanonicalEvidence` wrapper around a plain value comparison adds no value.
3. **Category 3 (out of scope):** print-only output with no real assertion.
   This is a correctness gap (`SSDOC-ORA-001`), not a migration; track it
   separately via `sspec-maintain scan`, do not "fix" it here.

Convert a category-1 candidate only when a `check_exact`/`check_full_pattern`/
`check_multiset` would express the assertion more precisely than substring
containment (e.g. an exact value embedded in free text, or a field that could
legitimately repeat). Leave the substring check alone when it is already the
right precision — this is judgment per spec, not a scripted sweep.

**Migrated candidate (2026-08-08): `test/01_unit/app/io/process_ops_ext_spec.spl`**

`describe "shell" / it "returns ProcessResult with stdout"` spawns a real
subprocess (`shell("echo hello")`) and asserts `result.stdout` with
`to_contain("hello")` — a genuine category-1 shape: a real captured value
(actual child-process stdout), never wrapped in any evidence artifact. Added,
additively, right after the existing assertion:

```spl
val capture = untyped_capture("shell echo stdout", result.stdout, "stdout")
val evidence = untyped_capture_to_canonical(capture, "process_ops_shell_echo_hello")
val comparison = compare_evidence(evidence, oracle_spec_open("process_ops_shell_echo_hello", [
    check_exact("value", "hello\n")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

Note this uses `check_exact`, not `check_full_pattern` — `echo hello`'s stdout
is a fixed literal (`"hello\n"`), so exact match is the correct precision
here per the triage rule; `check_full_pattern`/`check_multiset` apply when the
value has a shape (hex id, repeatable field) rather than a fixed literal.

Other specs found in the same sweep that call `to_contain`/`to_equal` on
subprocess-looking output (`test/01_unit/app/io/timeout_spec.spl`) are further
genuine category-1 candidates left for a future pass; several look-alikes
(`t32_cli_render_spec.spl`, `chat_tui_spec.spl`,
`cli_run_output_owner_spec.spl`) were checked and rejected as category 2 —
they assert on in-memory-constructed values or `rt_file_read_text` source
reads, not on an external process/render capture.

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

## Worked example 3 — print-based `fn test_*` specs (`test/01_unit/os/smux*`)

A second legacy shape, distinct from the untyped-capture case above: specs
written as `fn test_*` bodies that `print("PASS: ...")` / `print("FAIL: ...")`
and are driven by `main()`.

These are worse than untyped captures, because they are **not checks at all**:

- The runner executes **zero examples**, so the fail-closed zero-examples gate
  holds the file permanently RED — `declared>=1 executed=0 passed=0 failed=1
  reason=zero-examples` — no matter how many `PASS` lines it prints.
- A `FAIL` print does not fail the process. The verdict and the printed output
  can disagree completely, and the printed side is the one humans read.

### How to convert

Turn each `fn test_*` body into an `it` block and each `if`-guarded print into
an `expect(...)` oracle. Keep the module-level type definitions as they are.

```simple
# before — executes zero examples, prints a verdict nobody enforces
fn test_pane_area():
    val p = PaneId.create(0, 80, 24)
    if p.area() == 1920:
        print("PASS: test_pane_area")
    else:
        print("FAIL: test_pane_area")

# after — one executed example with a real oracle
describe "smux panes":
    it "computes area as width times height":
        val p = PaneId.create(0, 80, 24)
        expect(p.area()).to_equal(1920)
```

Convert the whole file: a leftover `main()` that still calls the old helpers
keeps the print-based path alive alongside the examples.

### Two traps this conversion hits

**Mirror trees.** `test/01_unit/**` and `test/unit/**` are duplicated. Convert
both copies identically or `check-test-tree-divergence` turns red. Verify with
`cmp`, not by eye.

**Do not chain off a static factory.** Writing the natural compact form

```simple
expect(PaneId.create(0, 80, 24).area()).to_equal(1920)   # fails to resolve
```

currently fails with `semantic: method 'area' not found on value of type object
in nested call context` — the receiver's declared type is erased to `object`
inside a nested call. Bind a `val` first. This is a compiler defect, filed as
`doc/08_tracking/bug/static_factory_method_chain_wrong_value_2026-08-16.md`,
not a style rule; 9 of 20 examples in one file failed for this reason alone
during the smux conversion.

### Verifying the conversion is real

The verdict line is the evidence, and the number that matters is `executed`:

```
SPEC FILE VERDICT: test/01_unit/os/smux_spec.spl declared>=20 executed=20 passed=20 failed=0 dropped=0
```

`executed=0` means the conversion did not take, whatever the file prints. A
regression guard for this lane lives at
`test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`, which reads the
committed sources and fails if a legacy construct reappears or a mirror drifts.

### Remaining candidate

`test/03_system/tools/smux_system_spec.spl` is still in this shape — 858 lines,
56 `fn test_*`, zero `describe`/`it`. It was left alone rather than converted
half-way; it is the obvious next candidate for this recipe.
