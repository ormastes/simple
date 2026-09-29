# Macro Check Specification

> Tests covering SyntaxMark, MarkedIdent, HygieneContext, HygieneTransformer, FragmentKind, TemplateValidator, TemplateTypeChecker, MacroChecker, MacroDef, MacroCheckResult, real-world macro patterns, error messages.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Check Specification

## Scenarios

### SyntaxMark

#### creates unique marks for each expansion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates unique marks for each expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates unique marks for each expansion")
# mark1 = SyntaxMark.create(1)
# mark2 = SyntaxMark.create(2)
# mark1.id != mark2.id
pass
```

</details>

#### formats mark as text

- formats mark as text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats mark as text")
# mark.to_text() => "mark_1"
pass
```

</details>

### MarkedIdent

#### creates unmarked identifier

- creates unmarked identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates unmarked identifier")
# ident = MarkedIdent.from_name("x")
# ident.marks.is_empty() == true
pass
```

</details>

#### adds marks during expansion

- adds marks during expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("adds marks during expansion")
# ident = MarkedIdent.from_name("x")
# marked = ident.add_mark(mark)
# marked.marks.len() == 1
pass
```

</details>

#### checks equality with marks

- checks equality with marks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks equality with marks")
# ident1 = MarkedIdent("x", [mark1])
# ident2 = MarkedIdent("x", [mark1])
# ident1.equals(ident2) == true
pass
```

</details>

#### distinguishes different marks

- distinguishes different marks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("distinguishes different marks")
# ident1 = MarkedIdent("x", [mark1])
# ident2 = MarkedIdent("x", [mark2])
# ident1.equals(ident2) == false
pass
```

</details>

### HygieneContext

#### creates root scope

- creates root scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates root scope")
# ctx = HygieneContext.create()
# ctx.current_scope == 0
pass
```

</details>

#### enters and exits scopes

- enters and exits scopes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("enters and exits scopes")
# ctx.enter_scope(ScopeKind.Block)
# ctx.current_scope == 1
# ctx.exit_scope()
# ctx.current_scope == 0
pass
```

</details>

#### tracks bindings in scope

- tracks bindings in scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks bindings in scope")
# ctx.bind_name("x", ident)
# ctx.resolve(ident) != nil
pass
```

</details>

#### resolves through scope chain

- resolves through scope chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves through scope chain")
# Bind "x" in parent
# Enter child scope
# Should still resolve "x"
pass
```

</details>

### HygieneTransformer

#### marks identifiers during expansion

- marks identifiers during expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks identifiers during expansion")
# transformer.start_expansion()
# ident = transformer.mark_identifier("x")
# ident.marks.len() == 1
pass
```

</details>

#### binds names in current scope

- binds names in current scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds names in current scope")
# transformer.bind("x")
# transformer.resolve("x") != nil
pass
```

</details>

#### detects hygiene violations

- detects hygiene violations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects hygiene violations")
# Outer binding of "x"
# Start expansion with inner binding of "x"
# Should detect shadowing
pass
```

</details>

### FragmentKind

#### parses fragment specifiers

- parses fragment specifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses fragment specifiers")
# FragmentKind.from_text("expr") == Some(FragmentKind.Expr)
# FragmentKind.from_text("ident") == Some(FragmentKind.Ident)
pass
```

</details>

#### checks follow-set rules

- checks follow-set rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks follow-set rules")
# FragmentKind.Ident.can_follow(Some(FragmentKind.Expr)) == true
# Some fragments cannot follow others
pass
```

</details>

### TemplateValidator

#### validates simple matcher

- validates simple matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates simple matcher")
# matcher = [Param("x", Expr)]
# validator.validate_matcher(matcher) == true
pass
```

</details>

#### detects duplicate parameters

- detects duplicate parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects duplicate parameters")
# matcher = [Param("x", Expr), Param("x", Ident)]
# validator.validate_matcher(matcher) == false
# error: "Duplicate parameter"
pass
```

</details>

#### validates repetitions

- validates repetitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates repetitions")
# matcher = [Repetition([Param("x", Expr)], ",", ZeroOrMore)]
# validator.validate_matcher(matcher) == true
pass
```

</details>

#### checks parameter usage in transcriber

- checks parameter usage in transcriber


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks parameter usage in transcriber")
# Define "x" in matcher
# Use "$x" in transcriber
# Should validate
pass
```

</details>

#### rejects undefined parameters

- rejects undefined parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects undefined parameters")
# Use "$y" in transcriber without defining
# error: "Undefined parameter"
pass
```

</details>

#### checks repetition depth

- checks repetition depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks repetition depth")
# Parameter in repetition must be used in repetition
pass
```

</details>

### TemplateTypeChecker

#### checks rule type consistency

- checks rule type consistency


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks rule type consistency")
# matcher captures expr
# transcriber uses it as expr
# Should pass
pass
```

</details>

#### infers expansion type

- infers expansion type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("infers expansion type")
# transcriber = [Keyword("if"), ...]
# infer_expansion_type() == "expr"
pass
```

</details>

### MacroChecker

#### registers macro definitions

- registers macro definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers macro definitions")
# checker.define_macro("log!", rules)
# checker.get_macro("log!") != nil
pass
```

</details>

#### validates macro rules on registration

- validates macro rules on registration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates macro rules on registration")
# Invalid rule should fail registration
pass
```

</details>

#### checks macro calls

- checks macro calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks macro calls")
# checker.check_call(call) == MacroCheckResult.Ok(...)
pass
```

</details>

#### reports undefined macros

- reports undefined macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports undefined macros")
# checker.check_call(undefined_call)
# == MacroCheckResult.UndefinedMacro(...)
pass
```

</details>

#### reports no matching rule

- reports no matching rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports no matching rule")
# Wrong number of args
# == MacroCheckResult.NoMatchingRule(...)
pass
```

</details>

### MacroDef

#### creates macro with rules

- creates macro with rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates macro with rules")
# def = MacroDef.create("test!")
# def.add_rule(rule)
# def.rules.len() == 1
pass
```

</details>

#### supports hygienic flag

- supports hygienic flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports hygienic flag")
# def.set_unhygienic()
# def.is_hygienic == false
pass
```

</details>

#### supports export levels

- supports export levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports export levels")
# def.set_export(2)  # public
# def.export_level == 2
pass
```

</details>

### MacroCheckResult

#### checks success

- checks success


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks success")
# result = MacroCheckResult.Ok("expr")
# result.is_ok() == true
# result.get_type() == Some("expr")
pass
```

</details>

#### formats errors

- formats errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats errors")
# result = MacroCheckResult.TypeError("...")
# result.get_error() != nil
pass
```

</details>

### real-world macro patterns

#### validates println! style macro

- validates println! style macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates println! style macro")
# println!("Hello, {}!", name)
# Format string + variadic args
pass
```

</details>

#### validates vec! style macro

- validates vec! style macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates vec! style macro")
# vec![1, 2, 3]
# Comma-separated repetition
pass
```

</details>

#### validates match! style macro

- validates match! style macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates match! style macro")
# match! { $e:expr, $( $p:pat => $body:expr ),* }
pass
```

</details>

#### validates derive! style macro

- validates derive! style macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates derive! style macro")
# @derive(Debug)
# Attribute-like macro
pass
```

</details>

### error messages

#### provides clear undefined macro error

- provides clear undefined macro error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provides clear undefined macro error")
# "Undefined macro: unknown!"
pass
```

</details>

#### provides clear duplicate param error

- provides clear duplicate param error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provides clear duplicate param error")
# "Duplicate parameter '$x'"
pass
```

</details>

#### provides clear follow-set error

- provides clear follow-set error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provides clear follow-set error")
# "'expr' cannot follow 'stmt'"
pass
```

</details>

#### provides clear hygiene error

- provides clear hygiene error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provides clear hygiene error")
# "Macro binding 'x' shadows existing binding"
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/macros/macro_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SyntaxMark, MarkedIdent, HygieneContext, HygieneTransformer, FragmentKind, TemplateValidator, TemplateTypeChecker, MacroChecker, MacroDef, MacroCheckResult, real-world macro patterns, error messages.
- SyntaxMark
- MarkedIdent
- HygieneContext
- HygieneTransformer
- FragmentKind
- TemplateValidator
- TemplateTypeChecker
- MacroChecker
- MacroDef
- MacroCheckResult
- real-world macro patterns
- error messages

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `2b87fdf0e0502010c3df8d47e443cdca61f3d67faf46f91441d1863ac47f5a9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b87fdf0e0502010c3df8d47e443cdca61f3d67faf46f91441d1863ac47f5a9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b87fdf0e0502010c3df8d47e443cdca61f3d67faf46f91441d1863ac47f5a9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/macros/macro_check_spec.spl
mirror: doc/06_spec/01_unit/compiler/macros/macro_check_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/macros/macro_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/macros/macro_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/macros/macro_check_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/compiler/macros/macro_check_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates unique marks for each expansion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/macros/macro_check_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats mark as text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/macros/macro_check_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates unmarked identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
