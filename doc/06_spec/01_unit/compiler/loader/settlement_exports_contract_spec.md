# settlement_exports_contract_spec

> Purpose: Prove that settlement export updates are transactional.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# settlement_exports_contract_spec

Purpose: Prove that settlement export updates are transactional.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/settlement_exports_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that settlement export updates are transactional.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### settlement export updates are transactional

#### rejects duplicate strong exports without partial mutation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects duplicate strong exports without partial mutation
- Verify: rejects duplicate strong exports without partial mutation
   - Expected: container.add_module("A", "/a.smf").is_ok() is true
   - Expected: container.add_module("B", "/b.smf").is_ok() is true
   - Expected: container.set_exports("A", [export_symbol("stable", 10, "A", SymbolBinding.Strong)]).is_ok() is true
   - Expected: result.is_err() is true
   - Expected: container.linker.get_export("new_b") == nil is true
   - Expected: container.modules["B"].exports.len() equals `0`
   - Expected: symbol.module_id equals `A`
   - Expected: symbol.address equals `10`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects duplicate strong exports without partial mutation")
step("Verify: rejects duplicate strong exports without partial mutation")
# @req: REQ-COMPILER-LOADER-001
val container = SettlementContainer.create()
expect(container.add_module("A", "/a.smf").is_ok()).to_equal(true)
expect(container.add_module("B", "/b.smf").is_ok()).to_equal(true)
expect(container.set_exports("A", [export_symbol("stable", 10, "A", SymbolBinding.Strong)]).is_ok()).to_equal(true)

val result = container.set_exports("B", [
    export_symbol("new_b", 20, "B", SymbolBinding.Strong),
    export_symbol("stable", 30, "B", SymbolBinding.Strong)
])
expect(result.is_err()).to_equal(true)
expect(container.linker.get_export("new_b") == nil).to_equal(true)
expect(container.modules["B"].exports.len()).to_equal(0)
match container.linker.get_export("stable"):
    case Some(symbol):
        expect(symbol.module_id).to_equal("A")
        expect(symbol.address).to_equal(10)  # oracle: 10 — named expected value from the requirement
    case nil:
        expect(false).to_equal(true)
```

</details>

#### replaces a module export set and removes stale names

- replaces a module export set and removes stale names
- Verify: replaces a module export set and removes stale names
   - Expected: container.add_module("A", "/a.smf").is_ok() is true
   - Expected: container.linker.get_export("old") == nil is true
   - Expected: container.linker.get_export("new") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("replaces a module export set and removes stale names")
step("Verify: replaces a module export set and removes stale names")
val container = SettlementContainer.create()
expect(container.add_module("A", "/a.smf").is_ok()).to_equal(true)
expect(container.set_exports("A", [
    export_symbol("old", 10, "A", SymbolBinding.Strong),
    export_symbol("keep", 20, "A", SymbolBinding.Strong)
]).is_ok()).to_equal(true)
expect(container.set_exports("A", [
    export_symbol("keep", 30, "A", SymbolBinding.Strong),
    export_symbol("new", 40, "A", SymbolBinding.Strong)
]).is_ok()).to_equal(true)

expect(container.linker.get_export("old") == nil).to_equal(true)
expect(container.linker.get_export("new") != nil).to_equal(true)
match container.linker.get_export("keep"):
    case Some(symbol): expect(symbol.address).to_equal(30)  # oracle: 30 — named expected value from the requirement
    case nil: expect(false).to_equal(true)
```

</details>

#### restores a weak export after its strong replacement is removed

- restores a weak export after its strong replacement is removed
- Verify: restores a weak export after its strong replacement is removed
   - Expected: container.add_module("A", "/a.smf").is_ok() is true
   - Expected: container.add_module("B", "/b.smf").is_ok() is true
   - Expected: container.set_exports("A", [export_symbol("shared", 10, "A", SymbolBinding.Weak)]).is_ok() is true
   - Expected: container.set_exports("B", [export_symbol("shared", 20, "B", SymbolBinding.Strong)]).is_ok() is true
   - Expected: symbol.module_id equals `B`
   - Expected: symbol.address equals `20`
   - Expected: false is true
   - Expected: container.set_exports("B", []).is_ok() is true
   - Expected: symbol.module_id equals `A`
   - Expected: symbol.address equals `10`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("restores a weak export after its strong replacement is removed")
step("Verify: restores a weak export after its strong replacement is removed")
val container = SettlementContainer.create()
expect(container.add_module("A", "/a.smf").is_ok()).to_equal(true)
expect(container.add_module("B", "/b.smf").is_ok()).to_equal(true)
expect(container.set_exports("A", [export_symbol("shared", 10, "A", SymbolBinding.Weak)]).is_ok()).to_equal(true)
expect(container.set_exports("B", [export_symbol("shared", 20, "B", SymbolBinding.Strong)]).is_ok()).to_equal(true)
match container.linker.get_export("shared"):
    case Some(symbol):
        expect(symbol.module_id).to_equal("B")
        expect(symbol.address).to_equal(20)  # oracle: 20 — named expected value from the requirement
    case nil:
        expect(false).to_equal(true)
expect(container.set_exports("B", []).is_ok()).to_equal(true)
match container.linker.get_export("shared"):
    case Some(symbol):
        expect(symbol.module_id).to_equal("A")
        expect(symbol.address).to_equal(10)  # oracle: 10 — named expected value from the requirement
    case nil:
        expect(false).to_equal(true)
```

</details>

#### handles remove and re-add without replaying a module twice

- handles remove and re-add without replaying a module twice
- Verify: handles remove and re-add without replaying a module twice
   - Expected: container.add_module("A", "/old.smf").is_ok() is true
   - Expected: container.set_exports("A", [export_symbol("old", 10, "A", SymbolBinding.Strong)]).is_ok() is true
   - Expected: container.remove_module("A").is_ok() is true
   - Expected: container.add_module("A", "/new.smf").is_ok() is true
   - Expected: container.set_exports("A", [export_symbol("fresh", 20, "A", SymbolBinding.Strong)]).is_ok() is true
   - Expected: container.linker.get_export("old") == nil is true
   - Expected: container.linker.get_export("fresh") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles remove and re-add without replaying a module twice")
step("Verify: handles remove and re-add without replaying a module twice")
val container = SettlementContainer.create()
expect(container.add_module("A", "/old.smf").is_ok()).to_equal(true)
expect(container.set_exports("A", [export_symbol("old", 10, "A", SymbolBinding.Strong)]).is_ok()).to_equal(true)
expect(container.remove_module("A").is_ok()).to_equal(true)
expect(container.add_module("A", "/new.smf").is_ok()).to_equal(true)
expect(container.set_exports("A", [export_symbol("fresh", 20, "A", SymbolBinding.Strong)]).is_ok()).to_equal(true)
expect(container.linker.get_export("old") == nil).to_equal(true)
expect(container.linker.get_export("fresh") != nil).to_equal(true)
```

</details>

#### preserves fallback exports across an unrelated module update

- preserves fallback exports across an unrelated module update
- Verify: preserves fallback exports across an unrelated module update
   - Expected: container.add_module("A", "/a.smf").is_ok() is true
   - Expected: container.linker.resolve_with_fallback(fallback_symbol).is_ok() is true
   - Expected: container.set_exports("A", [export_symbol("owned", 10, "A", SymbolBinding.Strong)]).is_ok() is true
   - Expected: symbol.module_id equals `__jit__`
   - Expected: symbol.address equals `99`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves fallback exports across an unrelated module update")
step("Verify: preserves fallback exports across an unrelated module update")
val container = SettlementContainer.create()
expect(container.add_module("A", "/a.smf").is_ok()).to_equal(true)
container.linker.add_import(ImportRef(
    symbol_name: "fallback",
    from_module: "A",
    relocation_offset: 0,
    relocation_kind: RelocationKind.Abs64
))
expect(container.linker.resolve_with_fallback(fallback_symbol).is_ok()).to_equal(true)
expect(container.set_exports("A", [export_symbol("owned", 10, "A", SymbolBinding.Strong)]).is_ok()).to_equal(true)
match container.linker.get_export("fallback"):
    case Some(symbol):
        expect(symbol.module_id).to_equal("__jit__")
        expect(symbol.address).to_equal(99)  # oracle: 99 — named expected value from the requirement
    case nil:
        expect(false).to_equal(true)
```

</details>

#### restores a fallback export after a same-name provider is removed

- restores a fallback export after a same-name provider is removed
- Verify: restores a fallback export after a same-name provider is removed
   - Expected: container.add_module("consumer", "/consumer.smf").is_ok() is true
   - Expected: container.add_module("provider", "/provider.smf").is_ok() is true
   - Expected: container.linker.resolve_with_fallback(fallback_symbol).is_ok() is true
   - Expected: container.set_exports("provider", [export_symbol("service", 20, "provider", SymbolBinding.Strong)]).is_ok() is true
   - Expected: container.remove_module("provider").is_ok() is true
   - Expected: symbol.module_id equals `__jit__`
   - Expected: symbol.address equals `99`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("restores a fallback export after a same-name provider is removed")
step("Verify: restores a fallback export after a same-name provider is removed")
val container = SettlementContainer.create()
expect(container.add_module("consumer", "/consumer.smf").is_ok()).to_equal(true)
expect(container.add_module("provider", "/provider.smf").is_ok()).to_equal(true)
container.linker.add_import(import_symbol("service", "consumer"))
expect(container.linker.resolve_with_fallback(fallback_symbol).is_ok()).to_equal(true)
expect(container.set_exports("provider", [export_symbol("service", 20, "provider", SymbolBinding.Strong)]).is_ok()).to_equal(true)
match container.linker.get_export("service"):
    case Some(symbol): expect(symbol.module_id).to_equal("provider")
    case nil: expect(false).to_equal(true)
expect(container.remove_module("provider").is_ok()).to_equal(true)
match container.linker.get_export("service"):
    case Some(symbol):
        expect(symbol.module_id).to_equal("__jit__")
        expect(symbol.address).to_equal(99)  # oracle: 99 — named expected value from the requirement
    case nil:
        expect(false).to_equal(true)
```

</details>

#### replaces imports instead of accumulating stale or duplicate refs

- replaces imports instead of accumulating stale or duplicate refs
- Verify: replaces imports instead of accumulating stale or duplicate refs
   - Expected: container.add_module("A", "/a.smf").is_ok() is true
   - Expected: container.set_imports("A", [import_symbol("old_missing", "A")]).is_ok() is true
   - Expected: container.set_imports("A", [import_symbol("new_missing", "A")]).is_ok() is true
   - Expected: container.set_imports("A", [import_symbol("new_missing", "A")]).is_ok() is true
   - Expected: container.linker.imports does not contain `old_missing`
   - Expected: container.linker.imports["new_missing"].len() equals `1`
   - Expected: container.linker.resolve().is_err() is true
   - Expected: container.linker.stats().unresolved equals `1`
   - Expected: container.linker.get_unresolved_imports() does not contain `old_missing`
   - Expected: container.linker.get_unresolved_imports() contains `new_missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("replaces imports instead of accumulating stale or duplicate refs")
step("Verify: replaces imports instead of accumulating stale or duplicate refs")
val container = SettlementContainer.create()
expect(container.add_module("A", "/a.smf").is_ok()).to_equal(true)
expect(container.set_imports("A", [import_symbol("old_missing", "A")]).is_ok()).to_equal(true)
expect(container.set_imports("A", [import_symbol("new_missing", "A")]).is_ok()).to_equal(true)
expect(container.set_imports("A", [import_symbol("new_missing", "A")]).is_ok()).to_equal(true)
expect(container.linker.imports.contains("old_missing")).to_equal(false)
expect(container.linker.imports["new_missing"].len()).to_equal(1)
expect(container.linker.resolve().is_err()).to_equal(true)
expect(container.linker.stats().unresolved).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(container.linker.get_unresolved_imports().contains("old_missing")).to_equal(false)
expect(container.linker.get_unresolved_imports().contains("new_missing")).to_equal(true)
```

</details>

#### removes graph and linker state before a clean module re-add

- removes graph and linker state before a clean module re-add
- Verify: removes graph and linker state before a clean module re-add
   - Expected: container.add_module("consumer", "/consumer.smf").is_ok() is true
   - Expected: container.add_module("provider", "/provider-old.smf").is_ok() is true
   - Expected: container.add_dependency("consumer", "provider").is_ok() is true
   - Expected: container.set_imports("consumer", [import_symbol("service", "consumer")]).is_ok() is true
   - Expected: container.set_exports("provider", [export_symbol("service", 10, "provider", SymbolBinding.Strong)]).is_ok() is true
   - Expected: container.link().is_ok() is true
   - Expected: container.remove_module("provider").is_ok() is true
   - Expected: container.modules does not contain `provider`
   - Expected: container.linker.modules does not contain `provider`
   - Expected: container.linker.get_export("service") == nil is true
   - Expected: container.modules["consumer"].dependencies does not contain `provider`
   - Expected: container.load_order.len() equals `0`
   - Expected: container.link().is_err() is true
   - Expected: container.linker.stats().unresolved equals `1`
   - Expected: container.add_module("provider", "/provider-new.smf").is_ok() is true
   - Expected: container.add_dependency("consumer", "provider").is_ok() is true
   - Expected: container.set_exports("provider", [export_symbol("service", 20, "provider", SymbolBinding.Strong)]).is_ok() is true
   - Expected: container.link().is_ok() is true
   - Expected: container.linker.modules.filter(\id: id == "provider").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("removes graph and linker state before a clean module re-add")
step("Verify: removes graph and linker state before a clean module re-add")
val container = SettlementContainer.create()
expect(container.add_module("consumer", "/consumer.smf").is_ok()).to_equal(true)
expect(container.add_module("provider", "/provider-old.smf").is_ok()).to_equal(true)
expect(container.add_dependency("consumer", "provider").is_ok()).to_equal(true)
expect(container.set_imports("consumer", [import_symbol("service", "consumer")]).is_ok()).to_equal(true)
expect(container.set_exports("provider", [export_symbol("service", 10, "provider", SymbolBinding.Strong)]).is_ok()).to_equal(true)
expect(container.link().is_ok()).to_equal(true)

expect(container.remove_module("provider").is_ok()).to_equal(true)
expect(container.modules.contains("provider")).to_equal(false)
expect(container.linker.modules.contains("provider")).to_equal(false)
expect(container.linker.get_export("service") == nil).to_equal(true)
expect(container.modules["consumer"].dependencies.contains("provider")).to_equal(false)
expect(container.load_order.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(container.link().is_err()).to_equal(true)
expect(container.linker.stats().unresolved).to_equal(1)  # oracle: 1 — named expected value from the requirement

expect(container.add_module("provider", "/provider-new.smf").is_ok()).to_equal(true)
expect(container.add_dependency("consumer", "provider").is_ok()).to_equal(true)
expect(container.set_exports("provider", [export_symbol("service", 20, "provider", SymbolBinding.Strong)]).is_ok()).to_equal(true)
expect(container.link().is_ok()).to_equal(true)
expect(container.linker.modules.filter(\id: id == "provider").len()).to_equal(1)
match container.linker.get_export("service"):
    case Some(symbol): expect(symbol.address).to_equal(20)  # oracle: 20 — named expected value from the requirement
    case nil: expect(false).to_equal(true)
```

</details>

#### orders a dependency chain before its consumers deterministically

- orders a dependency chain before its consumers deterministically
- Verify: orders a dependency chain before its consumers deterministically
   - Expected: container.add_module("app", "/app.smf").is_ok() is true
   - Expected: container.add_module("mid", "/mid.smf").is_ok() is true
   - Expected: container.add_module("base", "/base.smf").is_ok() is true
   - Expected: container.add_dependency("app", "mid").is_ok() is true
   - Expected: container.add_dependency("mid", "base").is_ok() is true
   - Expected: order equals `["base", "mid", "app"]`
   - Expected: container.get_load_order() equals `order`
   - Expected: container.modules[order[i]].load_order equals `i`
   - Expected: false is true
   - Expected: container.add_module("solo", "/solo.smf").is_ok() is true
   - Expected: container.get_load_order().len() equals `0`
   - Expected: container.modules[id].load_order equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders a dependency chain before its consumers deterministically")
step("Verify: orders a dependency chain before its consumers deterministically")
val container = SettlementContainer.create()
expect(container.add_module("app", "/app.smf").is_ok()).to_equal(true)
expect(container.add_module("mid", "/mid.smf").is_ok()).to_equal(true)
expect(container.add_module("base", "/base.smf").is_ok()).to_equal(true)
expect(container.add_dependency("app", "mid").is_ok()).to_equal(true)
expect(container.add_dependency("mid", "base").is_ok()).to_equal(true)
match container.topological_sort():
    case Ok(order):
        expect(order).to_equal(["base", "mid", "app"])
        expect(container.get_load_order()).to_equal(order)
        var i = 0
        while i < order.len():
            expect(container.modules[order[i]].load_order).to_equal(i)
            i = i + 1
    case Err(_):
        expect(false).to_equal(true)
expect(container.add_module("solo", "/solo.smf").is_ok()).to_equal(true)
expect(container.get_load_order().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
for id in ["app", "mid", "base", "solo"]:
    expect(container.modules[id].load_order).to_equal(-1)  # oracle: -1 — named expected value from the requirement
match container.topological_sort():
    case Ok(order): expect(order).to_equal(["base", "mid", "app", "solo"])
    case Err(_): expect(false).to_equal(true)
```

</details>

#### orders a diamond dependency once and keeps repeat sorts stable

- orders a diamond dependency once and keeps repeat sorts stable
- Verify: orders a diamond dependency once and keeps repeat sorts stable
   - Expected: container.add_module(id, "/{id}.smf").is_ok() is true
   - Expected: container.add_dependency("app", "right").is_ok() is true
   - Expected: container.add_dependency("app", "left").is_ok() is true
   - Expected: container.add_dependency("right", "base").is_ok() is true
   - Expected: container.add_dependency("left", "base").is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders a diamond dependency once and keeps repeat sorts stable")
step("Verify: orders a diamond dependency once and keeps repeat sorts stable")
val container = SettlementContainer.create()
for id in ["right", "app", "base", "left"]:
    expect(container.add_module(id, "/{id}.smf").is_ok()).to_equal(true)
expect(container.add_dependency("app", "right").is_ok()).to_equal(true)
expect(container.add_dependency("app", "left").is_ok()).to_equal(true)
expect(container.add_dependency("right", "base").is_ok()).to_equal(true)
expect(container.add_dependency("left", "base").is_ok()).to_equal(true)
val first = container.topological_sort()
val second = container.topological_sort()
match first:
    case Ok(order): expect(order).to_equal(["base", "left", "right", "app"])
    case Err(_): expect(false).to_equal(true)
match second:
    case Ok(order): expect(order).to_equal(["base", "left", "right", "app"])
    case Err(_): expect(false).to_equal(true)
```

</details>

#### rejects cycles without publishing a partial load order

- rejects cycles without publishing a partial load order
- Verify: rejects cycles without publishing a partial load order
   - Expected: container.add_module(id, "/{id}.smf").is_ok() is true
   - Expected: container.add_dependency("A", "B").is_ok() is true
   - Expected: container.add_dependency("B", "C").is_ok() is true
   - Expected: container.add_dependency("C", "A").is_ok() is true
   - Expected: container.get_load_order().len() equals `0`
   - Expected: container.modules["A"].load_order equals `-1`
   - Expected: cycle equals `["A", "B", "C"]`
   - Expected: false is true
   - Expected: container.get_load_order().len() equals `0`
   - Expected: container.modules[id].load_order equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects cycles without publishing a partial load order")
step("Verify: rejects cycles without publishing a partial load order")
val container = SettlementContainer.create()
for id in ["A", "B", "C", "D"]:
    expect(container.add_module(id, "/{id}.smf").is_ok()).to_equal(true)
expect(container.add_dependency("A", "B").is_ok()).to_equal(true)
expect(container.add_dependency("B", "C").is_ok()).to_equal(true)
match container.topological_sort():
    case Ok(order): expect(order).to_equal(["C", "B", "A", "D"])
    case Err(_): expect(false).to_equal(true)
expect(container.add_dependency("C", "A").is_ok()).to_equal(true)
expect(container.get_load_order().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(container.modules["A"].load_order).to_equal(-1)
match container.topological_sort():
    case Err(ContainerError.CircularDependency(cycle)):
        expect(cycle).to_equal(["A", "B", "C"])
    case _:
        expect(false).to_equal(true)
expect(container.get_load_order().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
for id in ["A", "B", "C", "D"]:
    expect(container.modules[id].load_order).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LOADER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4648bc47173c83fb81d9ddef9227435a0f9f6c7d7068d7cbc116d4e408b9655a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4648bc47173c83fb81d9ddef9227435a0f9f6c7d7068d7cbc116d4e408b9655a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4648bc47173c83fb81d9ddef9227435a0f9f6c7d7068d7cbc116d4e408b9655a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/loader/settlement_exports_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/settlement_exports_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/settlement_exports_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/settlement_exports_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/settlement_exports_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/loader/settlement_exports_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate strong exports without partial mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/settlement_exports_contract_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces a module export set and removes stale names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/settlement_exports_contract_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restores a weak export after its strong replacement is removed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
