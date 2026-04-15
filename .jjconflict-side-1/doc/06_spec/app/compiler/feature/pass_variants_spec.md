# Pass Keyword Variants

**Feature ID:** #SYNTAX-002 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/pass_variants_spec.spl`_

---

## Overview

Tests the enhanced pass keyword with semantic distinctions: `pass_todo` for
unimplemented code markers, `pass_do_nothing`/`pass_dn` for intentional no-ops,
and `pass` for generic backward-compatible no-ops. All variants evaluate to nil,
work as both expressions and statements, function in control flow contexts,
and accept optional descriptive message arguments.

## Syntax

```simple
pass_todo("implement error handling")
pass_do_nothing("intentional stub for interface")
pass_dn
val result = pass  # evaluates to nil
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 26 |

## Test Structure

### Pass Variants

- ✅ pass evaluates to nil
- ✅ pass with message evaluates to nil
- ✅ pass_todo evaluates to nil
- ✅ pass_todo with message evaluates to nil
- ✅ pass_do_nothing evaluates to nil
- ✅ pass_do_nothing with message evaluates to nil
- ✅ pass_dn evaluates to nil
- ✅ pass_dn with message evaluates to nil
### Pass Variants in Statements

- ✅ pass as statement
- ✅ pass_todo as statement
- ✅ pass_do_nothing as statement
- ✅ pass_dn as statement
### Pass Variants in Functions

- ✅ function returning pass
- ✅ function returning pass_todo
- ✅ function returning pass_do_nothing
- ✅ function returning pass_dn
### Pass Variants in Control Flow

- ✅ pass in if branch
- ✅ pass_todo in else branch
- ✅ pass_do_nothing in loop
- ✅ pass_dn in match case
### Pass Variants with Messages

- ✅ pass with descriptive message
- ✅ pass_todo with reason
- ✅ pass_do_nothing with explanation
- ✅ pass_dn with context
### Pass Variants Equivalence

- ✅ all pass variants return same value
- ✅ all pass variants are nil

