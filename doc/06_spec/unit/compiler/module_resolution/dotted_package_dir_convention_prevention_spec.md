# Dotted Directory Convention Is General, Not A Hardcoded List

> The dotted-directory convention broke once because each compiler encoded it

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dotted Directory Convention Is General, Not A Hardcoded List

The dotted-directory convention broke once because each compiler encoded it

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Implemented |
| Source | `test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The dotted-directory convention broke once because each compiler encoded it
differently: the pure-Simple driver carried a hand-maintained rewrite table with
four entries, and the Rust seed could only ever join the current directory's own
name with a single following segment. Both mechanisms happen to cover the
directories that were listed or that were one level deep; neither covers the
convention.

This spec exists to make that drift fail loudly. It is aimed at anyone touching
either resolver, and it deliberately exercises directories that no hardcoded
four-entry list mentions.

## Scope and Preconditions

Two independent dotted directories are imported, chosen for the two shapes the
old implementations could not handle:

- `src/app/package.registry/` -- two segments joined by one dot, sitting under a
  parent (`src/app/package/`) that does not exist at all, so no plain per-segment
  walk can reach it.
- `src/app/ui.chromium.acid2/` -- three segments joined by two dots, reachable
  only by joining three pending segments at once. Additionally, the prefixes
  `src/app/ui/` and `src/app/ui.chromium/` both exist, so a resolver must
  backtrack out of two plausible wrong turns before it finds this one.

## Primary Workflow

Each import resolves and yields a real value from the module behind it. Nothing
here asserts on source text or file existence -- the modules are loaded and used.

## Recovery and Troubleshooting

If only the `package.registry` scenario passes, the resolver most likely regained
a single-level or list-based rule. If neither passes, resolution of dotted
directories is broken outright. Fix the resolver; do not rename directories and
do not add entries to a list.

## Compatibility and Limitations

Behavior is shared by both compilers, but the seed's half is Rust, so a seed
predating the fix fails these scenarios until it is rebuilt and redeployed.

## Scenarios

### Dotted directory resolution generalises beyond any listed set

#### reaches a dotted directory whose plain-path parent does not exist

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reaches a dotted directory whose plain-path parent does not exist
- Import app.package.registry.config; there is no src/app/package/ directory to walk through
- Read values the module composes itself, proving the real module loaded
   - Expected: cfg.registry_url equals `ghcr.io/simple-lang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches a dotted directory whose plain-path parent does not exist")
step("Import app.package.registry.config; there is no src/app/package/ directory to walk through")
val cfg = default_config()

step("Read values the module composes itself, proving the real module loaded")
expect(cfg.cache_dir).to_contain(".simple/cache/registry")
expect(cfg.registry_url).to_equal("ghcr.io/simple-lang")
```

</details>

#### joins three segments at once, past two prefixes that also exist as directories

- joins three segments at once, past two prefixes that also exist as directories
- Import app.ui.chromium.acid2, whose directory name carries two dots
- Both src/app/ui/ and src/app/ui.chromium/ exist, so the resolver must backtrack out of each
- Read the Acid2 grid geometry the module declares
   - Expected: ACID2_GRID_WIDTH equals `16`
   - Expected: ACID2_GRID_HEIGHT equals `16`
- Confirm the constants are internally consistent, not defaults from an empty stand-in
   - Expected: ACID2_GRID_CELLS equals `ACID2_GRID_WIDTH * ACID2_GRID_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins three segments at once, past two prefixes that also exist as directories")
step("Import app.ui.chromium.acid2, whose directory name carries two dots")
step("Both src/app/ui/ and src/app/ui.chromium/ exist, so the resolver must backtrack out of each")
step("Read the Acid2 grid geometry the module declares")

expect(ACID2_GRID_WIDTH).to_equal(16)
expect(ACID2_GRID_HEIGHT).to_equal(16)

step("Confirm the constants are internally consistent, not defaults from an empty stand-in")
expect(ACID2_GRID_CELLS).to_equal(ACID2_GRID_WIDTH * ACID2_GRID_HEIGHT)
```

</details>

#### serves both dotted shapes from one resolver rather than two special cases

- serves both dotted shapes from one resolver rather than two special cases
- Use a value from each dotted directory in the same example
   - Expected: ACID2_GRID_CELLS equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serves both dotted shapes from one resolver rather than two special cases")
step("Use a value from each dotted directory in the same example")
val cfg = default_config()

expect(cfg.index_url).to_contain("://")
expect(ACID2_GRID_CELLS).to_equal(256)
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

- `REQ-SSPEC-UNIT`
- `REQ-MODRES-DOTTED-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0002e31ec970bb84eae961059ebb346698dd09b6bd5efe72b8597cd695955efa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0002e31ec970bb84eae961059ebb346698dd09b6bd5efe72b8597cd695955efa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0002e31ec970bb84eae961059ebb346698dd09b6bd5efe72b8597cd695955efa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl
mirror: doc/06_spec/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches a dotted directory whose plain-path parent does not exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins three segments at once, past two prefixes that also exist as directories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves both dotted shapes from one resolver rather than two special cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
