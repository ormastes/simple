# Trait Keyword - All Phases

**Feature ID:** #TRAIT-002 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/trait_keyword_all_phases_spec.spl`_

---

## Overview

Comprehensive phase tests for the trait keyword desugaring feature covering all
five phases: trait detection via scan_traits, method signature extraction
(fn/me, parameters, return types), default method detection (has_default),
forwarding generation (alias fn/me and alias TraitName = field), and end-to-end
workflows from trait definition through implementation to usage with correct
forwarding of abstract-only methods.

## Syntax

```simple
trait Formatter:
    fn format(value: text) -> text
class TextFormatter:
    inner: BaseFormatter
    alias Formatter = inner
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 35 |

## Test Structure

### Trait Keyword: Phase 1 - Trait detection

#### basic detection

- ✅ trait declaration is recognized
- ✅ trait name is extracted correctly
- ✅ trait without methods has empty method list
- ✅ source with no traits returns empty list
#### multiple traits

- ✅ finds two traits in source
- ✅ traits mixed with non-trait declarations are detected
- ✅ trait with lowercase start is ignored
#### find_trait

- ✅ find_trait returns matching trait
- ✅ find_trait returns empty trait for unknown name
### Trait Keyword: Phase 2 - Method signature extraction

#### fn methods

- ✅ fn method is detected with is_me=false
- ✅ fn method with return type extracts name correctly
#### me methods

- ✅ me method is detected with is_me=true
- ✅ mixed fn and me methods in same trait
#### parameter extraction

- ✅ no-arg method has empty param_names
- ✅ single-param method extracts name
- ✅ multi-param method extracts all param names
#### comments and type lines skipped

- ✅ comment lines in trait body are skipped
- ✅ type declaration lines in trait body are skipped
### Trait Keyword: Phase 3 - Default method detection

#### abstract vs default methods

- ✅ method without body has has_default=false
- ✅ method with multi-line body has has_default=true
- ✅ method with inline body has has_default=true
#### trait alias forwarding skips default methods

- ✅ alias TraitName=field only generates for abstract methods
- ✅ all-abstract trait generates forwarding for every method
### Trait Keyword: Phase 4 - Forwarding

#### Phase 2: alias fn and alias me

- ✅ alias fn generates immutable forwarding method
- ✅ alias fn with args generates forwarding with parameters
- ✅ alias me generates mutable forwarding method
#### Phase 3: alias TraitName = field

- ✅ alias Trait generates fn forwarding for fn methods
- ✅ alias Trait generates me forwarding for me methods
- ✅ unknown trait generates no forwarding code
#### Phase 4: blanket alias field

- ✅ alias field_name forwards all methods from field type
### Trait Keyword: Phase 5 - End-to-end usage

#### complete trait workflow

- ✅ define a trait, scan it, use find_trait to retrieve
- ✅ complete define-implement-forward workflow
- ✅ multiple traits in source: each generates correct forwarding
- ✅ trait with default methods: only abstract methods are forwarded
- ✅ trait scanner and forwarding agree on method count

