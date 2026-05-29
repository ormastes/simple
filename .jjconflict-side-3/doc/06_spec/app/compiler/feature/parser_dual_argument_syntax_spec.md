# Dual Syntax for Argument Assignment Specification

**Feature ID:** #1200-1210 | **Category:** Syntax | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/parser_dual_argument_syntax_spec.spl`_

---

## Overview

Support BOTH ':' and '=' for argument assignment in ALL contexts.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 24 |

## Test Structure

### Dual Syntax - Function Calls

#### colon syntax in function calls
_Traditional colon syntax._

- ✅ accepts single named argument with colon
- ✅ accepts multiple named arguments with colons
#### equals syntax in function calls
_Equals syntax for arguments._

- ✅ accepts single named argument with equals
- ✅ accepts multiple named arguments with equals
#### mixed syntax in function calls
_Mixing ':' and '=' in same call._

- ✅ accepts mixed colon and equals syntax
- ✅ produces identical results regardless of syntax
### Dual Syntax - Struct Initialization

#### colon syntax in struct init
_Traditional colon syntax for struct fields._

- ✅ accepts single field with colon
- ✅ accepts multiple fields with colons
- ✅ accepts many fields with colons
#### equals syntax in struct init
_Equals syntax for struct fields._

- ✅ accepts single field with equals
- ✅ accepts multiple fields with equals
- ✅ accepts many fields with equals
#### mixed syntax in struct init
_Mixing ':' and '=' in struct initialization._

- ✅ accepts mixed colon and equals syntax
- ✅ produces identical structs regardless of syntax
#### shorthand syntax still works
_Field shorthand when variable name matches field name._

- ✅ accepts shorthand syntax
- ✅ mixes shorthand with explicit syntax
### Dual Syntax - No-Paren Calls

#### colon syntax in no-paren calls

#### equals syntax in no-paren calls

#### mixed syntax in no-paren calls

### Dual Syntax - Edge Cases

#### nested calls and struct init
_Combining different contexts._

- ✅ handles nested function calls with mixed syntax
- ✅ handles struct init inside function call
- ✅ handles function call result in struct init
#### multiline arguments
_Arguments spanning multiple lines._

- ✅ handles multiline with colon syntax
- ✅ handles multiline with equals syntax
- ✅ handles multiline with mixed syntax
#### whitespace handling
_Various whitespace patterns - some cause parse issues._

### Dual Syntax - Consistency

- ✅ produces same results in all contexts combined
- ✅ works identically in real-world scenarios

