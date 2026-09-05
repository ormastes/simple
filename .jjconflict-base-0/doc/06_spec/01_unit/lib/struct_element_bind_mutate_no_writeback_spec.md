# Defect class: bind a STRUCT element out of a collection, mutate it, never write it back

> Structs are value types by design, so `val x = coll[k]` yields a COPY on every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 7 | 0 | 2 |

<details>
<summary>Full Scenario Manual</summary>

# Defect class: bind a STRUCT element out of a collection, mutate it, never write it back

Structs are value types by design, so `val x = coll[k]` yields a COPY on every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Structs are value types by design, so `val x = coll[k]` yields a COPY on every
engine — interpreter, JIT and native alike. A following `x.field = ...` then
mutates the copy and the write is silently lost. This is an ordinary code bug,
not the interpreter class-aliasing defect recorded in
`doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`
— and it must NOT be confused with it: adding write-backs to CLASS-typed sites
is explicitly rejected there.

The defect is the PATTERN, not one call site. This spec scans the owned source
that carried it so a reintroduction anywhere in these files fails, not merely a
regression at the six sites that were fixed. A positive control proves the
detector still fires on the defective shape, so a clean sweep cannot silently
mean a broken scanner.

## Scenarios

### defect class: struct element bind-then-mutate with no write-back

####  _(pending)_
####  _(pending)_
#### control: the detector fires on the defective shape

- control: the detector fires on the defective shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("control: the detector fires on the defective shape")
# Without this, a clean sweep below could mean the detector is broken.
val bad = "val bp = line_map[line]\nbp.hit_count = bp.hit_count + 1\n"
assert_true(detects(bad))
```

</details>

#### control: the detector accepts a written-back binding and ignores prose

- control: the detector accepts a written-back binding and ignores prose


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("control: the detector accepts a written-back binding and ignores prose")
val good = "val bp = line_map[line]\nbp.hit_count = bp.hit_count + 1\nline_map[line] = bp\n"
assert_false(detects(good))
assert_false(detects("# val bp = line_map[line]\n# bp.hit_count = 1\n"))
# a mutable `var` binding read back into the collection is the fixed form
assert_false(detects("var ctx = self.actors[actor_id]\nctx.error_count = 1\nself.actors[actor_id] = ctx\n"))
```

</details>

#### control: the scan can see the files it claims to scan

- control: the scan can see the files it claims to scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("control: the scan can see the files it claims to scan")
# Guards against an absence check that silently scanned nothing.
expect(source_of("src/app/dap/hooks.spl")).to_contain("struct Breakpoint")
expect(source_of("src/lib/nogc_async_mut/actors/actor.spl")).to_contain("struct ActorContext")
expect(source_of("src/compiler/30.types/type_system/checker.spl")).to_contain("struct TraitImplRegistry")
```

</details>

#### the DAP hook copies write the Breakpoint hit count back

- the DAP hook copies write the Breakpoint hit count back


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the DAP hook copies write the Breakpoint hit count back")
assert_false(has_unprotected_site("src/app/dap/hooks.spl"))
assert_false(has_unprotected_site("src/lib/nogc_sync_mut/dap/hooks.spl"))
assert_false(has_unprotected_site("src/lib/nogc_async_mut/dap/hooks.spl"))
assert_false(has_unprotected_site("src/runtime/hooks.spl"))
```

</details>

#### all four DAP hook copies carry the two-level write-back

- all four DAP hook copies carry the two-level write-back


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all four DAP hook copies carry the two-level write-back")
# Nested Dict<text, Dict<i64, Breakpoint>>: both levels must be stored.
for path in ["src/app/dap/hooks.spl", "src/lib/nogc_sync_mut/dap/hooks.spl",
             "src/lib/nogc_async_mut/dap/hooks.spl", "src/runtime/hooks.spl"]:
    val s = source_of(path)
    expect(s).to_contain("line_map[line] = bp")
    expect(s).to_contain("self.breakpoints[file] = line_map")
```

</details>

#### the actor runtime writes the mutated ActorContext back

- the actor runtime writes the mutated ActorContext back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the actor runtime writes the mutated ActorContext back")
assert_false(has_unprotected_site("src/lib/nogc_async_mut/actors/actor.spl"))
expect(source_of("src/lib/nogc_async_mut/actors/actor.spl")).to_contain("self.actors[actor_id] = ctx")
```

</details>

#### trait impl registration writes the TraitImplRegistry back

- trait impl registration writes the TraitImplRegistry back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trait impl registration writes the TraitImplRegistry back")
assert_false(has_unprotected_site("src/compiler/30.types/type_system/checker.spl"))
expect(source_of("src/compiler/30.types/type_system/checker.spl")).to_contain("self.trait_impls[trait_name] = registry")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 2 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb16bb58e7b0223583be4b84e2fb3d0fd6df9fa42e51ca9cc369fda43ff3353e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb16bb58e7b0223583be4b84e2fb3d0fd6df9fa42e51ca9cc369fda43ff3353e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb16bb58e7b0223583be4b84e2fb3d0fd6df9fa42e51ca9cc369fda43ff3353e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.spl
mirror: doc/06_spec/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: the detector fires on the defective shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: the detector accepts a written-back binding and ignores prose' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/struct_element_bind_mutate_no_writeback_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: the scan can see the files it claims to scan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
