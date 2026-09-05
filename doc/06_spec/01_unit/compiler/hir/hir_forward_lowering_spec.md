# hir_forward_lowering_spec

> Purpose: Prove that hir_forward_lowering populates HirForwardDecl from real source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_forward_lowering_spec

Purpose: Prove that hir_forward_lowering populates HirForwardDecl from real source.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_forward_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that hir_forward_lowering populates HirForwardDecl from real source.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### hir_forward_lowering populates HirForwardDecl from real source

#### lowers a no-arg alias fn into a populated node

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers a no-arg alias fn into a populated node
- Verify: lowers a no-arg alias fn into a populated node
   - Expected: decls.len() equals `1`
   - Expected: decls[0].logical_symbol equals `C.len`
   - Expected: decls[0].receiver_projection equals `inner`
   - Expected: decls[0].target_symbol equals `len`
   - Expected: decls[0].is_me is false
   - Expected: decls[0].params.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a no-arg alias fn into a populated node")
step("Verify: lowers a no-arg alias fn into a populated node")
# @req: REQ-COMPILER-HIR-001
val decls = lower_forward_decls(class_source("    alias fn len = inner.len"))
expect(decls.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(decls[0].logical_symbol).to_equal("C.len")
expect(decls[0].receiver_projection).to_equal("inner")
expect(decls[0].target_symbol).to_equal("len")
expect(decls[0].is_me).to_equal(false)
expect(decls[0].params.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### carries the receiver mode and parameter list of an alias me

- carries the receiver mode and parameter list of an alias me
- Verify: carries the receiver mode and parameter list of an alias me
   - Expected: decls.len() equals `1`
   - Expected: decls[0].is_me is true
   - Expected: decls[0].params.len() equals `1`
   - Expected: decls[0].params[0] equals `item`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the receiver mode and parameter list of an alias me")
step("Verify: carries the receiver mode and parameter list of an alias me")
val decls = lower_forward_decls(class_source("    alias me push(item) = inner.push"))
expect(decls.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(decls[0].is_me).to_equal(true)
expect(decls[0].params.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(decls[0].params[0]).to_equal("item")
```

</details>

#### assigns a distinct join point id per declaration

- assigns a distinct join point id per declaration
- Verify: assigns a distinct join point id per declaration
   - Expected: decls.len() equals `2`
   - Expected: decls[0].logical_join_point_id equals `1`
   - Expected: decls[1].logical_join_point_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns a distinct join point id per declaration")
step("Verify: assigns a distinct join point id per declaration")
val src = "class C:\n    alias fn a = inner.a\n    alias me b(x) = inner.b\n"
val decls = lower_forward_decls(src)
expect(decls.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(decls[0].logical_join_point_id).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(decls[1].logical_join_point_id).to_equal(2)  # oracle: 2 — named expected value from the requirement
assert_true(decls[0].logical_join_point_id != decls[1].logical_join_point_id)
```

</details>

#### lowers every line of the real-tree corpus (no form is skipped)

- lowers every line of the real-tree corpus (no form is skipped)
- Verify: lowers every line of the real-tree corpus (no form is skipped)
   - Expected: decls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers every line of the real-tree corpus (no form is skipped)")
step("Verify: lowers every line of the real-tree corpus (no form is skipped)")
val lines = corpus_lines()
var i = 0
while i < lines.len():
    val decls = lower_forward_decls(class_source(lines[i]))
    expect(decls.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
    i = i + 1
```

</details>

#### ignores alias lines outside a class body and malformed targets

- ignores alias lines outside a class body and malformed targets
- Verify: ignores alias lines outside a class body and malformed targets
   - Expected: lower_forward_decls("alias fn len = inner.len\n").len() equals `0`
   - Expected: lower_forward_decls(class_source("    alias fn len = inner")).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores alias lines outside a class body and malformed targets")
step("Verify: ignores alias lines outside a class body and malformed targets")
# Discriminates an over-eager lowering: a bare module-level alias and a
# target with no dot must produce NO node.
expect(lower_forward_decls("alias fn len = inner.len\n").len()).to_equal(0)
expect(lower_forward_decls(class_source("    alias fn len = inner")).len()).to_equal(0)
```

</details>

### typed node agrees with the authoritative text generator

#### reconstructs the generator's forwarder byte-for-byte, whole corpus

- reconstructs the generator's forwarder byte-for-byte, whole corpus
- Verify: reconstructs the generator's forwarder byte-for-byte, whole corpus
   - Expected: decls.len() equals `1`
   - Expected: typed equals `generated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reconstructs the generator's forwarder byte-for-byte, whole corpus")
step("Verify: reconstructs the generator's forwarder byte-for-byte, whole corpus")
val lines = corpus_lines()
var i = 0
while i < lines.len():
    val decls = lower_forward_decls(class_source(lines[i]))
    expect(decls.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
    val typed = forwarder_text(decls[0], "    ")
    val generated = generated_forwarder(lines[i])
    # Raw text on both sides: no normalization, so a disagreement in
    # keyword, name, args, projection or target all show up here.
    expect(typed).to_equal(generated)
    i = i + 1
```

</details>

#### the agreement is not vacuous — the oracle can disagree

- the agreement is not vacuous — the oracle can disagree
- Verify: the agreement is not vacuous — the oracle can disagree


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the agreement is not vacuous — the oracle can disagree")
step("Verify: the agreement is not vacuous — the oracle can disagree")
# If `forwarder_text` were a constant or the comparison were loose,
# this would also pass; it must not.
val decls = lower_forward_decls(class_source("    alias me push(item) = inner.push"))
val typed = forwarder_text(decls[0], "    ")
val other = generated_forwarder("    alias fn len = inner.len")
assert_true(typed != other)
```

</details>

#### preserves the mutating receiver in the generated keyword

- preserves the mutating receiver in the generated keyword
- Verify: preserves the mutating receiver in the generated keyword
   - Expected: forwarder_text(decls[0], "    ") contains `me push(item):`
   - Expected: forwarder_text(decls2[0], "    ") contains `fn len():`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves the mutating receiver in the generated keyword")
step("Verify: preserves the mutating receiver in the generated keyword")
val decls = lower_forward_decls(class_source("    alias me push(item) = inner.push"))
expect(forwarder_text(decls[0], "    ").contains("me push(item):")).to_equal(true)
val decls2 = lower_forward_decls(class_source("    alias fn len = inner.len"))
expect(forwarder_text(decls2[0], "    ").contains("fn len():")).to_equal(true)
```

</details>

### receiver projection uses the LAST dot (C5 scanner divergence tripwire)

#### projects through inner.items and targets push

- projects through inner.items and targets push
- Verify: projects through inner.items and targets push
   - Expected: decls.len() equals `1`
   - Expected: decls[0].receiver_projection equals `inner.items`
   - Expected: decls[0].target_symbol equals `push`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("projects through inner.items and targets push")
step("Verify: projects through inner.items and targets push")
val decls = lower_forward_decls(class_source("    alias fn push = inner.items.push"))
expect(decls.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(decls[0].receiver_projection).to_equal("inner.items")
expect(decls[0].target_symbol).to_equal("push")
```

</details>

#### matches the generator's self.inner.items.push() body

- matches the generator's self.inner.items.push() body
- Verify: matches the generator's self.inner.items.push() body
   - Expected: forwarder_text(decls[0], "    ") contains `self.inner.items.push()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches the generator's self.inner.items.push() body")
step("Verify: matches the generator's self.inner.items.push() body")
val decls = lower_forward_decls(class_source("    alias fn push = inner.items.push"))
expect(forwarder_text(decls[0], "    ").contains("self.inner.items.push()")).to_equal(true)
```

</details>

### forms this slice cannot represent are reported, not dropped

#### reports a module-level Phase 1 fn alias

- reports a module-level Phase 1 fn alias
- Verify: reports a module-level Phase 1 fn alias
   - Expected: forms.len() equals `1`
   - Expected: forms[0] equals `fn alias_name = target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a module-level Phase 1 fn alias")
step("Verify: reports a module-level Phase 1 fn alias")
val forms = unrepresented_forward_forms("fn target(x):\n    x\n\nfn alias_name = target\n")
expect(forms.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(forms[0]).to_equal("fn alias_name = target")
```

</details>

#### reports Phase 3 trait alias and Phase 4 blanket alias

- reports Phase 3 trait alias and Phase 4 blanket alias
- Verify: reports Phase 3 trait alias and Phase 4 blanket alias
   - Expected: forms.len() equals `2`
   - Expected: forms[0] equals `alias Drawable = inner`
   - Expected: forms[1] equals `alias inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports Phase 3 trait alias and Phase 4 blanket alias")
step("Verify: reports Phase 3 trait alias and Phase 4 blanket alias")
val src = "class C:\n    alias Drawable = inner\n    alias inner\n"
val forms = unrepresented_forward_forms(src)
expect(forms.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(forms[0]).to_equal("alias Drawable = inner")
expect(forms[1]).to_equal("alias inner")
```

</details>

#### does not report the Phase 2 forms it does represent

- does not report the Phase 2 forms it does represent
- Verify: does not report the Phase 2 forms it does represent
   - Expected: forms.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not report the Phase 2 forms it does represent")
step("Verify: does not report the Phase 2 forms it does represent")
val forms = unrepresented_forward_forms(class_source("    alias me push(item) = inner.push"))
expect(forms.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### a normal fn declaration is not mistaken for a Phase 1 alias

- a normal fn declaration is not mistaken for a Phase 1 alias
- Verify: a normal fn declaration is not mistaken for a Phase 1 alias
   - Expected: unrepresented_forward_forms("fn f(x: i64) -> i64:\n    x + 1\n").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a normal fn declaration is not mistaken for a Phase 1 alias")
step("Verify: a normal fn declaration is not mistaken for a Phase 1 alias")
expect(unrepresented_forward_forms("fn f(x: i64) -> i64:\n    x + 1\n").len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-HIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `29d92bc5e5d2301a37d0d27610494ce16c918fc7c9375f8b5e084bcac858c39e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29d92bc5e5d2301a37d0d27610494ce16c918fc7c9375f8b5e084bcac858c39e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29d92bc5e5d2301a37d0d27610494ce16c918fc7c9375f8b5e084bcac858c39e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/hir_forward_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_forward_lowering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_forward_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_forward_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_forward_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_forward_lowering_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a no-arg alias fn into a populated node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_forward_lowering_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the receiver mode and parameter list of an alias me' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_forward_lowering_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns a distinct join point id per declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
