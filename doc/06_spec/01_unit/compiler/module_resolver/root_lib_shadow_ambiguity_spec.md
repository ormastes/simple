# root_lib_shadow_ambiguity_spec

> Reproducer: a tier-less `use std.<path>` that collides with a ROOT

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# root_lib_shadow_ambiguity_spec

Reproducer: a tier-less `use std.<path>` that collides with a ROOT

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproducer: a tier-less `use std.<path>` that collides with a ROOT
`src/lib/<name>/` module was never flagged at all.

`_resolve_module_path_uncached` tries `src/lib/<path>` (step 3) BEFORE the
lib/*/ tier search (step 4), so `use std.js.types` lands on
`src/lib/js/types.spl` deterministically and shadows
`src/lib/common/js/types.spl` from every importer. The stage-1 multiplicity
map walked only the five tier directories, so this class produced a stable
WRONG symbol with no diagnostic whatsoever. See
doc/08_tracking/bug/tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md
(narrowing dated 2026-08-01).

## Scenarios

### root src/lib/<name>/ shadowing is flagged

#### warns when a tier-less path also exists at the lib root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warns when a tier-less path also exists at the lib root
   - Expected: resolver.tier_warn_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns when a tier-less path also exists at the lib root")
setup_fixture()
rt_env_set("SIMPLE_AMBIGUOUS_IMPORT_WARN", "1")
var resolver = moduleresolver_new(FIXTURE, FIXTURE + "/src")
val lib_dir = FIXTURE + "/src/lib"
resolver.maybe_warn_tier_ambiguity(lib_dir, ["js", "types"], FIXTURE + "/src/main.spl")
expect(resolver.tier_warn_count).to_equal(1)
```

</details>

#### records the lib root as a distinct source in the multiplicity map

- records the lib root as a distinct source in the multiplicity map
   - Expected: resolver.tier_multiplicity["js.types"].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records the lib root as a distinct source in the multiplicity map")
setup_fixture()
var resolver = moduleresolver_new(FIXTURE, FIXTURE + "/src")
resolver.build_tier_multiplicity(FIXTURE + "/src/lib")
expect(resolver.tier_multiplicity["js.types"].len()).to_equal(2)
expect(resolver.tier_multiplicity["js.types"]).to_contain("<lib-root>")
expect(resolver.tier_multiplicity["js.types"]).to_contain("common")
```

</details>

#### does not warn for a path that exists in only one place

- does not warn for a path that exists in only one place
   - Expected: resolver.tier_warn_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not warn for a path that exists in only one place")
setup_fixture()
rt_env_set("SIMPLE_AMBIGUOUS_IMPORT_WARN", "1")
var resolver = moduleresolver_new(FIXTURE, FIXTURE + "/src")
resolver.maybe_warn_tier_ambiguity(FIXTURE + "/src/lib", ["solo", "only"], FIXTURE + "/src/main.spl")
expect(resolver.tier_warn_count).to_equal(0)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `454e126a86aabf83cdc40c061afc616029434c530d18331cc400d86f352ddb2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `454e126a86aabf83cdc40c061afc616029434c530d18331cc400d86f352ddb2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `454e126a86aabf83cdc40c061afc616029434c530d18331cc400d86f352ddb2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl
mirror: doc/06_spec/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns when a tier-less path also exists at the lib root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the lib root as a distinct source in the multiplicity map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not warn for a path that exists in only one place' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
