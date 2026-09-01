# env_get_dead_fallback_class_spec

> Class-detection spec for env_get_nil_coalesce_dead_fallback_2026-07-25.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# env_get_dead_fallback_class_spec

Class-detection spec for env_get_nil_coalesce_dead_fallback_2026-07-25.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Class-detection spec for env_get_nil_coalesce_dead_fallback_2026-07-25.

`env_get` (both `std.io_runtime.env_get` and `std.nogc_sync_mut.io.env_ops.env_get`,
the latter re-exported as `app.io.mod.env_get`) returns a NON-nullable `text`.
`env_get(k) ?? default` is therefore a DEAD fallback: an unset variable arrives
as `""`, `??` never fires, and the caller silently receives the empty string.

A `?? ""` site is harmless (the dead default equals the value produced anyway).
A site whose default is NON-empty is a live wrong-value defect. The correct-by-
construction sibling is `std.io_runtime.env_get_opt`.

Scope is deliberately `src/app/llm_caret/messaging/**` plus `bridgeConfig.spl`, the sites this lane migrated and
verified import-by-import. The bug record warns that a blind tree-wide sweep
would be WRONG, because some `env_get` names in scope elsewhere (`rt_env_get`,
local `*_env_get` wrappers) genuinely return `text?` and their `??` is correct.
Widening this root requires doing that per-file import audit first.

## Scenarios

### env_get dead-fallback class detection

#### detects the known-bad shape and ignores the benign one (detector control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects the known-bad shape and ignores the benign one (detector control)
   - Expected: found.len() equals `1`
   - Expected: found[0] equals `fixture:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects the known-bad shape and ignores the benign one (detector control)")
# Without this control a scan that silently matched nothing would look
# identical to a clean tree.
val fixture = "val a = env_get(\"X\") ?? \"default\"\n" +
    "val b = env_get(\"Y\") ?? \"\"\n" +
    "val c = env_get_opt(\"Z\") ?? \"default\"\n" +
    "val d = env_get(\"W\") ?? \"\",\n" +
    "val e = (env_get(\"V\") ?? \"\") != \"\"\n"
val found = live_dead_fallback_lines(fixture, "fixture")
expect(found.len()).to_equal(1)
expect(found[0]).to_equal("fixture:1")
```

</details>

#### scans a non-empty set of source files (non-vacuity control)

- scans a non-empty set of source files (non-vacuity control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("scans a non-empty set of source files (non-vacuity control)")
val files = collect_spl(SCAN_ROOT, [])
expect(files.len()).to_be_greater_than(40)
```

</details>

#### has no env_get(...) ?? <non-empty-default> site in the migrated subtree

- has no env_get(...) ?? <non-empty-default> site in the migrated subtree
   - Expected: offenders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has no env_get(...) ?? <non-empty-default> site in the migrated subtree")
var offenders: [text] = []
for f in collect_spl(SCAN_ROOT, EXTRA_FILES):
    for hit in live_dead_fallback_lines(file_read(f), f):
        offenders.push(hit)
expect(offenders.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e912afe8065243f166d6a84380318e7be828b0142e92bcfc127144027a9f6ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e912afe8065243f166d6a84380318e7be828b0142e92bcfc127144027a9f6ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e912afe8065243f166d6a84380318e7be828b0142e92bcfc127144027a9f6ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the known-bad shape and ignores the benign one (detector control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans a non-empty set of source files (non-vacuity control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/env_get_dead_fallback_class_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no env_get(...) ?? <non-empty-default> site in the migrated subtree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
