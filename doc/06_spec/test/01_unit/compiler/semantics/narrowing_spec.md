# Narrowing Specification

> 1. var ctx = NarrowingContext new

<!-- sdn-diagram:id=narrowing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=narrowing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

narrowing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=narrowing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Narrowing Specification

## Scenarios

### NarrowingContext basic operations

#### pushes scope, adds fact, and looks it up

1. var ctx = NarrowingContext new
2. ctx push scope
3. ctx add fact
   - Expected: result.? is true
   - Expected: result.unwrap() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = NarrowingContext.new()
ctx.push_scope()
val fact = NarrowingFact(
    symbol_id: 1,
    original_type: "i64?",
    narrowed_type: "i64",
    condition: NarrowingConditionKind.NilCheckPos
)
ctx.add_fact(fact)
val result = ctx.lookup(1)
expect(result.?).to_equal(true)
expect(result.unwrap()).to_equal("i64")
```

</details>

#### facts do not leak across scope boundaries

1. var ctx = NarrowingContext new
2. ctx push scope
3. ctx add fact
   - Expected: ctx.lookup(2).? is true
4. ctx pop scope
   - Expected: after_pop.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = NarrowingContext.new()
ctx.push_scope()
val fact = NarrowingFact(
    symbol_id: 2,
    original_type: "text?",
    narrowed_type: "text",
    condition: NarrowingConditionKind.ExistsCheck
)
ctx.add_fact(fact)
expect(ctx.lookup(2).?).to_equal(true)
ctx.pop_scope()
val after_pop = ctx.lookup(2)
expect(after_pop.?).to_equal(false)
```

</details>

#### innermost scope takes priority

1. var ctx = NarrowingContext new
2. ctx add fact
3. ctx push scope
4. ctx add fact
   - Expected: result.? is true
   - Expected: result.unwrap() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = NarrowingContext.new()
val outer_fact = NarrowingFact(
    symbol_id: 3,
    original_type: "i64?",
    narrowed_type: "i64",
    condition: NarrowingConditionKind.Truthiness
)
ctx.add_fact(outer_fact)
ctx.push_scope()
val inner_fact = NarrowingFact(
    symbol_id: 3,
    original_type: "i64?",
    narrowed_type: "text",
    condition: NarrowingConditionKind.NilCheckPos
)
ctx.add_fact(inner_fact)
val result = ctx.lookup(3)
expect(result.?).to_equal(true)
expect(result.unwrap()).to_equal("text")
```

</details>

#### add_facts adds multiple facts at once

1. var ctx = NarrowingContext new
2. NarrowingFact
3. NarrowingFact
4. ctx add facts
   - Expected: ctx.lookup(10).? is true
   - Expected: ctx.lookup(11).? is true
   - Expected: ctx.lookup(99).? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = NarrowingContext.new()
val facts = [
    NarrowingFact(symbol_id: 10, original_type: "i64?", narrowed_type: "i64", condition: NarrowingConditionKind.NilCheckPos),
    NarrowingFact(symbol_id: 11, original_type: "text?", narrowed_type: "text", condition: NarrowingConditionKind.ExistsCheck)
]
ctx.add_facts(facts)
expect(ctx.lookup(10).?).to_equal(true)
expect(ctx.lookup(11).?).to_equal(true)
expect(ctx.lookup(99).?).to_equal(false)
```

</details>

### Condition analysis - nil checks

#### x != nil narrows Optional(i64) to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_nil_check(10, "i64?", false)
expect(facts.len()).to_equal(1)
expect(facts[0].symbol_id).to_equal(10)
expect(facts[0].narrowed_type).to_equal("i64")
```

</details>

#### x == nil produces NilCheckNeg fact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_nil_check(12, "i64?", true)
expect(facts.len()).to_equal(1)
expect(facts[0].symbol_id).to_equal(12)
expect(facts[0].narrowed_type).to_equal("i64?")
```

</details>

#### non-optional type produces no facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_nil_check(13, "i64", false)
expect(facts.is_empty()).to_equal(true)
```

</details>

### Condition analysis - exists checks

#### x.? where x has Optional(text) narrows to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_exists_check(20, "text?")
expect(facts.len()).to_equal(1)
expect(facts[0].symbol_id).to_equal(20)
expect(facts[0].narrowed_type).to_equal("text")
```

</details>

#### x.? where x has non-optional type returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_exists_check(21, "i64")
expect(facts.is_empty()).to_equal(true)
```

</details>

### Condition analysis - truthiness

#### bare Var with Optional type narrows to inner

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_truthiness(30, "text?")
expect(facts.len()).to_equal(1)
expect(facts[0].symbol_id).to_equal(30)
expect(facts[0].narrowed_type).to_equal("text")
```

</details>

#### bare Var with non-optional produces no narrowing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = analyze_truthiness(31, "bool")
expect(facts.is_empty()).to_equal(true)
```

</details>

### Fact negation

#### NilCheckPos negated returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fact = NarrowingFact(
    symbol_id: 40,
    original_type: "i64?",
    narrowed_type: "i64",
    condition: NarrowingConditionKind.NilCheckPos
)
val negated = negate_facts([fact])
expect(negated.is_empty()).to_equal(true)
```

</details>

#### NilCheckNeg negated returns fact with inner type

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fact = NarrowingFact(
    symbol_id: 41,
    original_type: "i64?",
    narrowed_type: "i64?",
    condition: NarrowingConditionKind.NilCheckNeg
)
val negated = negate_facts([fact])
expect(negated.len()).to_equal(1)
expect(negated[0].symbol_id).to_equal(41)
expect(negated[0].narrowed_type).to_equal("i64")
```

</details>

#### IsNotCheck negated returns IsCheck fact

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fact = NarrowingFact(
    symbol_id: 42,
    original_type: "i64|text",
    narrowed_type: "text",
    condition: NarrowingConditionKind.IsNotCheck
)
val negated = negate_facts([fact])
expect(negated.len()).to_equal(1)
expect(negated[0].symbol_id).to_equal(42)
```

</details>

#### ExistsCheck negated returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fact = NarrowingFact(
    symbol_id: 43,
    original_type: "i64?",
    narrowed_type: "i64",
    condition: NarrowingConditionKind.ExistsCheck
)
val negated = negate_facts([fact])
expect(negated.is_empty()).to_equal(true)
```

</details>

#### Truthiness negated returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fact = NarrowingFact(
    symbol_id: 44,
    original_type: "text?",
    narrowed_type: "text",
    condition: NarrowingConditionKind.Truthiness
)
val negated = negate_facts([fact])
expect(negated.is_empty()).to_equal(true)
```

</details>

### Definite termination

#### block ending in Return definitely terminates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = SimpleBlock(stmts: [StmtKind.ExprStmt, StmtKind.ReturnStmt])
expect(definitely_terminates(block)).to_equal(true)
```

</details>

#### empty block does not definitely terminate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = SimpleBlock(stmts: [])
expect(definitely_terminates(block)).to_equal(false)
```

</details>

#### block ending in regular expression does not terminate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = SimpleBlock(stmts: [StmtKind.ExprStmt])
expect(definitely_terminates(block)).to_equal(false)
```

</details>

#### block ending in Break definitely terminates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = SimpleBlock(stmts: [StmtKind.BreakStmt])
expect(definitely_terminates(block)).to_equal(true)
```

</details>

#### block ending in Continue definitely terminates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = SimpleBlock(stmts: [StmtKind.ContinueStmt])
expect(definitely_terminates(block)).to_equal(true)
```

</details>

### Narrowing integration

#### simulates if-else narrowing flow

1. var ctx = NarrowingContext new
2. ctx push scope
3. ctx add facts
   - Expected: ctx.lookup(50).unwrap() equals `i64`
4. ctx pop scope
5. ctx push scope
6. ctx add facts
   - Expected: ctx.lookup(50).? is false
7. ctx pop scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate: if x != nil: <then> else: <else>
var ctx = NarrowingContext.new()
val then_facts = analyze_nil_check(50, "i64?", false)

# Then branch
ctx.push_scope()
ctx.add_facts(then_facts)
expect(ctx.lookup(50).unwrap()).to_equal("i64")
ctx.pop_scope()

# Else branch uses negated facts
val else_facts = negate_facts(then_facts)
ctx.push_scope()
ctx.add_facts(else_facts)
# NilCheckPos negated -> no fact in else
expect(ctx.lookup(50).?).to_equal(false)
ctx.pop_scope()
```

</details>

#### simulates early-return narrowing promotion

1. var ctx = NarrowingContext new
2. ctx push scope
3. ctx add facts
4. ctx pop scope
5. ctx add facts
   - Expected: ctx.lookup(60).? is true
   - Expected: ctx.lookup(60).unwrap() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate: if x == nil: return
# After early return, x is narrowed in remaining code
var ctx = NarrowingContext.new()
val guard_facts = analyze_nil_check(60, "text?", true)

# Then branch (return) -> terminates
ctx.push_scope()
ctx.add_facts(guard_facts)
ctx.pop_scope()

# Promote negated facts to parent scope (early return promotion)
val promoted = negate_facts(guard_facts)
ctx.add_facts(promoted)

# Now x is narrowed in the remaining code
expect(ctx.lookup(60).?).to_equal(true)
expect(ctx.lookup(60).unwrap()).to_equal("text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/narrowing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NarrowingContext basic operations
- Condition analysis - nil checks
- Condition analysis - exists checks
- Condition analysis - truthiness
- Fact negation
- Definite termination
- Narrowing integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
