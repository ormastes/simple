# Module Loader Lazy Services

> Phase D (startup perf plan 2026-08-17): ModuleLoader construction must not

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Lazy Services

Phase D (startup perf plan 2026-08-17): ModuleLoader construction must not

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/module_loader_lazy_services_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Phase D (startup perf plan 2026-08-17): ModuleLoader construction must not
build heavy services (compiler ctx, ObjTaker, provider, JIT, mapper,
lifecycle/cache). Services are created on first use by ensure_* helpers, and
a disabled JIT config never creates the JIT service through symbol lookup.

## Scenarios

### Module Loader Lazy Services

#### creates no heavy services at construction

- creates no heavy services at construction
   - Expected: moduleloader_any_heavy_service_created(loader) is false
   - Expected: moduleloader_compiler_ctx_created(loader) is false
   - Expected: moduleloader_obj_taker_created(loader) is false
   - Expected: moduleloader_provider_created(loader) is false
   - Expected: moduleloader_jit_service_created(loader) is false
   - Expected: moduleloader_loader_mapper_created(loader) is false
   - Expected: moduleloader_lifecycle_created(loader) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates no heavy services at construction")
val loader = lazymoduleloader_new(lazy_default_config())
expect(moduleloader_any_heavy_service_created(loader)).to_equal(false)
expect(moduleloader_compiler_ctx_created(loader)).to_equal(false)
expect(moduleloader_obj_taker_created(loader)).to_equal(false)
expect(moduleloader_provider_created(loader)).to_equal(false)
expect(moduleloader_jit_service_created(loader)).to_equal(false)
expect(moduleloader_loader_mapper_created(loader)).to_equal(false)
expect(moduleloader_lifecycle_created(loader)).to_equal(false)
```

</details>

#### creates no heavy services via with_defaults either

- creates no heavy services via with_defaults either
   - Expected: moduleloader_any_heavy_service_created(loader) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates no heavy services via with_defaults either")
val loader = lazymoduleloader_with_defaults()
expect(moduleloader_any_heavy_service_created(loader)).to_equal(false)
```

</details>

#### symbol lookup creates exactly lifecycle and jit, not provider or obj_taker

- symbol lookup creates exactly lifecycle and jit, not provider or obj_taker
   - Expected: true is true
   - Expected: "unexpected resolve result" equals `NotFound`
   - Expected: moduleloader_lifecycle_created(loader) is true
   - Expected: moduleloader_jit_service_created(loader) is true
   - Expected: moduleloader_provider_created(loader) is false
   - Expected: moduleloader_obj_taker_created(loader) is false
   - Expected: moduleloader_compiler_ctx_created(loader) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("symbol lookup creates exactly lifecycle and jit, not provider or obj_taker")
val loader = lazymoduleloader_new(lazy_default_config())
match moduleloader_resolve_symbol(loader, "no_such_symbol_lazy_spec"):
    case NotFound(_):
        expect(true).to_equal(true)
    case _:
        expect("unexpected resolve result").to_equal("NotFound")
expect(moduleloader_lifecycle_created(loader)).to_equal(true)
expect(moduleloader_jit_service_created(loader)).to_equal(true)
expect(moduleloader_provider_created(loader)).to_equal(false)
expect(moduleloader_obj_taker_created(loader)).to_equal(false)
expect(moduleloader_compiler_ctx_created(loader)).to_equal(false)
```

</details>

#### module load attempt creates provider, lifecycle, and exec-mapper host

- module load attempt creates provider, lifecycle, and exec-mapper host
   - Expected: true is true
   - Expected: "unexpected load result" equals `Error`
   - Expected: moduleloader_provider_created(loader) is true
   - Expected: moduleloader_lifecycle_created(loader) is true
   - Expected: moduleloader_jit_service_created(loader) is true
   - Expected: moduleloader_obj_taker_created(loader) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module load attempt creates provider, lifecycle, and exec-mapper host")
val loader = lazymoduleloader_new(lazy_default_config())
match moduleloader_load(loader, "/nonexistent/lazy_spec_module.smf"):
    case Error(_):
        expect(true).to_equal(true)
    case _:
        expect("unexpected load result").to_equal("Error")
expect(moduleloader_provider_created(loader)).to_equal(true)
expect(moduleloader_lifecycle_created(loader)).to_equal(true)
expect(moduleloader_jit_service_created(loader)).to_equal(true)
expect(moduleloader_obj_taker_created(loader)).to_equal(false)
```

</details>

#### disabled jit config never creates the JIT service on lookup (fail-closed)

- disabled jit config never creates the JIT service on lookup (fail-closed)
   - Expected: true is true
   - Expected: "unexpected resolve result" equals `NotFound`
   - Expected: moduleloader_jit_service_created(loader) is false
   - Expected: moduleloader_lifecycle_created(loader) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disabled jit config never creates the JIT service on lookup (fail-closed)")
val loader = lazymoduleloader_new(lazy_no_jit_config())
match moduleloader_resolve_symbol(loader, "no_such_symbol_nojit_spec"):
    case NotFound(_):
        expect(true).to_equal(true)
    case _:
        expect("unexpected resolve result").to_equal("NotFound")
expect(moduleloader_jit_service_created(loader)).to_equal(false)
expect(moduleloader_lifecycle_created(loader)).to_equal(true)
```

</details>

#### repeated lookups keep working and do not duplicate services

- repeated lookups keep working and do not duplicate services
   - Expected: moduleloader_jit_service_created(loader) is true
   - Expected: moduleloader_lifecycle_created(loader) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated lookups keep working and do not duplicate services")
val loader = lazymoduleloader_new(lazy_default_config())
val _r1 = moduleloader_resolve_symbol(loader, "sym_a_lazy_spec")
val _r2 = moduleloader_resolve_symbol(loader, "sym_a_lazy_spec")
expect(moduleloader_jit_service_created(loader)).to_equal(true)
expect(moduleloader_lifecycle_created(loader)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b91b3f9e12cee9ba5294f3df408bbc530a45966d6f166d7f2bb23951312da481`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b91b3f9e12cee9ba5294f3df408bbc530a45966d6f166d7f2bb23951312da481`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b91b3f9e12cee9ba5294f3df408bbc530a45966d6f166d7f2bb23951312da481`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/loader/module_loader_lazy_services_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/module_loader_lazy_services_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/module_loader_lazy_services_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/module_loader_lazy_services_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/module_loader_lazy_services_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates no heavy services at construction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/module_loader_lazy_services_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates no heavy services via with_defaults either' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/module_loader_lazy_services_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'symbol lookup creates exactly lifecycle and jit, not provider or obj_taker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
