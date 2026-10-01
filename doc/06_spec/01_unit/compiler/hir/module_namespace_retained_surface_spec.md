# Module Namespace Retained-Surface Unit Spec

> Module-only imports may resolve through a canonical alias whose key differs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Namespace Retained-Surface Unit Spec

Module-only imports may resolve through a canonical alias whose key differs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Module-only imports may resolve through a canonical alias whose key differs
from the retained physical ModuleSurface name. The namespace receiver and its
imported callables must share the retained owner so qualified calls lower
before MIR rather than escaping as LoadGlobal.

## Scenarios

### module namespace retained surface ownership

#### lowers async env path namespaces through retained lib owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers async env path namespaces through retained lib owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers async env path namespaces through retained lib owners")
verify_namespace_owner_lowering(false, "nogc_async_mut")
```

</details>

#### lowers the same namespaces after reverse overlay discovery

- lowers the same namespaces after reverse overlay discovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers the same namespaces after reverse overlay discovery")
verify_namespace_owner_lowering(true, "nogc_async_mut")
```

</details>

#### keeps sync env path namespaces on their retained owners

- keeps sync env path namespaces on their retained owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps sync env path namespaces on their retained owners")
verify_namespace_owner_lowering(false, "nogc_sync_mut")
```

</details>

#### lowers the env paths selective import without a variables global

- lowers the env paths selective import without a variables global


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers the env paths selective import without a variables global")
verify_selective_env_import_lowering(false)
```

</details>

#### keeps the adjacent aliased selective import on the env_get owner

- keeps the adjacent aliased selective import on the env_get owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the adjacent aliased selective import on the env_get owner")
verify_selective_env_import_lowering(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc6d118313ca1eacf830fcaff10eddde903eb0b002668aead4efb5eee9a4ffff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc6d118313ca1eacf830fcaff10eddde903eb0b002668aead4efb5eee9a4ffff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc6d118313ca1eacf830fcaff10eddde903eb0b002668aead4efb5eee9a4ffff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_namespace_retained_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/module_namespace_retained_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_namespace_retained_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers async env path namespaces through retained lib owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers the same namespaces after reverse overlay discovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl:216:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps sync env path namespaces on their retained owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
