# Named Argument with Equals Syntax Specification

**Feature ID:** #NAMED-ARG-EQUALS | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/named_arg_equals_spec.spl`_

---

## Syntax

```simple
# Colon syntax (preferred for readability)
connect(host: "localhost", port: 8080)

# Equals syntax (concise, especially for single args)
Point(x=3, y=4)

# Mixed with positional
greet("Hello", name="World")
```

## Key Behaviors

- Named arguments can appear in any order
- Named arguments can be mixed with positional arguments
- Positional arguments must come before named arguments
- Both `name: value` and `name=value` syntax are supported

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Named Arguments with Equals Syntax

#### basic named arguments with equals

- ✅ passes single named argument
- ✅ passes multiple named arguments
- ✅ allows reordered named arguments
#### basic named arguments with colon

- ✅ passes single named argument with colon
- ✅ passes multiple named arguments with colon
- ✅ allows reordered named arguments with colon
#### mixed positional and named arguments

- ✅ combines positional with named equals
- ✅ combines positional with named colon
- ✅ uses multiple positional then named
#### named arguments with default values

- ✅ uses default when named arg omitted
- ✅ overrides default with named arg
- ✅ overrides multiple defaults
- ✅ overrides defaults in any order
#### struct construction with named arguments

- ✅ constructs struct with equals syntax
- ✅ constructs struct with colon syntax
- ✅ allows reordered struct fields
- ✅ constructs complex struct
#### edge cases

- ✅ handles single character parameter names
- ✅ handles longer parameter names
- ✅ handles underscored parameter names

