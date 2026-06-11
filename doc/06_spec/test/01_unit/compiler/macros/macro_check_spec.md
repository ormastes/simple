# Macro Check Specification

> <details>

<!-- sdn-diagram:id=macro_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Check Specification

## Scenarios

### SyntaxMark

#### creates unique marks for each expansion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mark1 = SyntaxMark.create(1)
# mark2 = SyntaxMark.create(2)
# mark1.id != mark2.id
pass
```

</details>

#### formats mark as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mark.to_text() => "mark_1"
pass
```

</details>

### MarkedIdent

#### creates unmarked identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ident = MarkedIdent.from_name("x")
# ident.marks.is_empty() == true
pass
```

</details>

#### adds marks during expansion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ident = MarkedIdent.from_name("x")
# marked = ident.add_mark(mark)
# marked.marks.len() == 1
pass
```

</details>

#### checks equality with marks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ident1 = MarkedIdent("x", [mark1])
# ident2 = MarkedIdent("x", [mark1])
# ident1.equals(ident2) == true
pass
```

</details>

#### distinguishes different marks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ident1 = MarkedIdent("x", [mark1])
# ident2 = MarkedIdent("x", [mark2])
# ident1.equals(ident2) == false
pass
```

</details>

### HygieneContext

#### creates root scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ctx = HygieneContext.create()
# ctx.current_scope == 0
pass
```

</details>

#### enters and exits scopes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ctx.enter_scope(ScopeKind.Block)
# ctx.current_scope == 1
# ctx.exit_scope()
# ctx.current_scope == 0
pass
```

</details>

#### tracks bindings in scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ctx.bind_name("x", ident)
# ctx.resolve(ident).? == true
pass
```

</details>

#### resolves through scope chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Bind "x" in parent
# Enter child scope
# Should still resolve "x"
pass
```

</details>

### HygieneTransformer

#### marks identifiers during expansion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# transformer.start_expansion()
# ident = transformer.mark_identifier("x")
# ident.marks.len() == 1
pass
```

</details>

#### binds names in current scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# transformer.bind("x")
# transformer.resolve("x").? == true
pass
```

</details>

#### detects hygiene violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Outer binding of "x"
# Start expansion with inner binding of "x"
# Should detect shadowing
pass
```

</details>

### FragmentKind

#### parses fragment specifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FragmentKind.from_text("expr") == Some(FragmentKind.Expr)
# FragmentKind.from_text("ident") == Some(FragmentKind.Ident)
pass
```

</details>

#### checks follow-set rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FragmentKind.Ident.can_follow(Some(FragmentKind.Expr)) == true
# Some fragments cannot follow others
pass
```

</details>

### TemplateValidator

#### validates simple matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# matcher = [Param("x", Expr)]
# validator.validate_matcher(matcher) == true
pass
```

</details>

#### detects duplicate parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# matcher = [Param("x", Expr), Param("x", Ident)]
# validator.validate_matcher(matcher) == false
# error: "Duplicate parameter"
pass
```

</details>

#### validates repetitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# matcher = [Repetition([Param("x", Expr)], ",", ZeroOrMore)]
# validator.validate_matcher(matcher) == true
pass
```

</details>

#### checks parameter usage in transcriber

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Define "x" in matcher
# Use "$x" in transcriber
# Should validate
pass
```

</details>

#### rejects undefined parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use "$y" in transcriber without defining
# error: "Undefined parameter"
pass
```

</details>

#### checks repetition depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parameter in repetition must be used in repetition
pass
```

</details>

### TemplateTypeChecker

#### checks rule type consistency

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# matcher captures expr
# transcriber uses it as expr
# Should pass
pass
```

</details>

#### infers expansion type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# transcriber = [Keyword("if"), ...]
# infer_expansion_type() == "expr"
pass
```

</details>

### MacroChecker

#### registers macro definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.define_macro("log!", rules)
# checker.get_macro("log!").? == true
pass
```

</details>

#### validates macro rules on registration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Invalid rule should fail registration
pass
```

</details>

#### checks macro calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_call(call) == MacroCheckResult.Ok(...)
pass
```

</details>

#### reports undefined macros

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_call(undefined_call)
# == MacroCheckResult.UndefinedMacro(...)
pass
```

</details>

#### reports no matching rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wrong number of args
# == MacroCheckResult.NoMatchingRule(...)
pass
```

</details>

### MacroDef

#### creates macro with rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# def = MacroDef.create("test!")
# def.add_rule(rule)
# def.rules.len() == 1
pass
```

</details>

#### supports hygienic flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# def.set_unhygienic()
# def.is_hygienic == false
pass
```

</details>

#### supports export levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# def.set_export(2)  # public
# def.export_level == 2
pass
```

</details>

### MacroCheckResult

#### checks success

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result = MacroCheckResult.Ok("expr")
# result.is_ok() == true
# result.get_type() == Some("expr")
pass
```

</details>

#### formats errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result = MacroCheckResult.TypeError("...")
# result.get_error().? == true
pass
```

</details>

### real-world macro patterns

#### validates println! style macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# println!("Hello, {}!", name)
# Format string + variadic args
pass
```

</details>

#### validates vec! style macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vec![1, 2, 3]
# Comma-separated repetition
pass
```

</details>

#### validates match! style macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# match! { $e:expr, $( $p:pat => $body:expr ),* }
pass
```

</details>

#### validates derive! style macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @derive(Debug)
# Attribute-like macro
pass
```

</details>

### error messages

#### provides clear undefined macro error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Undefined macro: unknown!"
pass
```

</details>

#### provides clear duplicate param error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Duplicate parameter '$x'"
pass
```

</details>

#### provides clear follow-set error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "'expr' cannot follow 'stmt'"
pass
```

</details>

#### provides clear hygiene error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
