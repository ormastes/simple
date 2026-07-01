# Comma Decorator (Labeled Arguments) Design

**Date:** 2026-02-01
**Status:** Proposal

## Summary

Allow functions to declare call-site labels on parameters using directional keywords (`to`, `from`, etc.) as postfix decorators.

```simple
# Declaration: label keyword after type
fn copy_from(from: text to, to: text)

# Call site: value followed by label, comma-separated
copy_from(src_path to, dest_path)
```

## Motivation

Directional operations like `copy(from, to)` are clearer when labels appear at call sites. Compare:

```simple
# Without labels - which is source, which is dest?
copy_from("/tmp/a.txt", "/tmp/b.txt")

# With labels - self-documenting
copy_from("/tmp/a.txt" to, "/tmp/b.txt")

# Traditional named args also work
copy_from(from: "/tmp/a.txt", to: "/tmp/b.txt")
```

## Syntax

### Declaration

Label keyword appears after the parameter type:

```simple
fn copy_from(from: text to, to: text)
fn transfer(amount: i64, from: Account from, to: Account to)
fn convert(data: bytes, from: Format from, to: Format to)
fn scale(value: f64, by: f64 by)
```

### Call Site

Value followed by label keyword, arguments comma-separated:

```simple
copy_from(src to, dst)
transfer(100, checking from, savings to)
convert(raw_data, Format.JSON from, Format.XML to)
scale(10.0, 2.5 by)
```

### Mixing Styles

Label decorators and traditional named arguments can be mixed:

```simple
copy_from(src_path to, to: dest_path)
```

## Comma-Required vs Comma-Optional

### Decision: Comma-required is mandatory. Comma-optional is rejected.

`copy_from(a to, b)` — accepted.
`copy_from(a to b)` — **rejected, problematic.**

### Why Comma-Optional Fails

**1. Ambiguity with keywords as identifiers**

Simple allows `to`/`from` as identifiers in expression position. Without commas, the parser cannot distinguish labels from variables:

```simple
val to = "dest.txt"
copy_from(to to to)  # Completely ambiguous — which 'to' is label, variable, argument?
```

**2. Breaks LL(1) parsing**

```simple
copy_from(a to b to c)
```

Ambiguous interpretations:
1. Two args: `(a to, b to c)` — labels on first and... what?
2. Two args: `(a to b, to c)` — where do args split?
3. Three args: `(a, to, b to c)` — `to` as variable?

The parser cannot decide without unbounded lookahead and backtracking.

**3. Performance**

- Comma-required: O(n) linear, LL(1), no backtracking
- Comma-optional: O(n^2) to exponential worst case with backtracking

**4. No precedent without delimiters**

Even Objective-C (which skips commas) uses colons as delimiters: `[obj copyFrom:a to:b]`. Without *some* delimiter between arguments, parsing is fundamentally ambiguous.

**5. All mainstream languages require commas**

Swift, Kotlin, Python — all require commas between arguments. The one-character cost buys unambiguous, fast, maintainable parsing.

### Conclusion

Comma-required (`copy_from(a to, b)`) is the only viable option. The comma costs one character but keeps parsing simple, fast, and unambiguous. Comma-optional is not "just OK" — it is genuinely problematic and is rejected.

## Comparison with Other Languages

| Language | Syntax | Commas | Notes |
|----------|--------|--------|-------|
| **Swift** | `greet(person: "Bill", from: "Cupertino")` | Required | External labels before internal name |
| **Kotlin** | `copy(from = "a", to = "b")` | Required | Named args with `=` |
| **Objective-C** | `[fm copyFrom:@"a" to:@"b"]` | No commas | Colons as delimiters, method selector |
| **Simple (proposed)** | `copy_from(src to, dst)` | Required | Postfix label after value |

Simple's approach is unique: labels are postfix on values rather than prefix (Swift) or assignment (Kotlin). This reads naturally for directional operations.

## Label Keywords

Initial set of supported labels:

| Keyword | Already a token | Use case |
|---------|----------------|----------|
| `to` | Yes (`TokenKind::To`) | Destination, target |
| `from` | Yes (`TokenKind::From`) | Source, origin |

Future candidates (if needed): `into`, `by`, `with`, `onto`

## Parsing Strategy

After parsing an argument expression, check if the next token is a label keyword:

```
argument := expression [label_keyword]
arguments := '(' argument (',' argument)* ')'
label_keyword := 'to' | 'from'
```

This is LL(1) - one token of lookahead after the expression suffices.

## AST Representation

Extend argument kind to distinguish labeled from named:

```rust
enum ArgumentKind {
    Positional,         // func(value)
    Named(String),      // func(name: value)
    Labeled(String),    // func(value label)
}

struct Argument {
    kind: ArgumentKind,
    value: Expr,
    span: Span,
}
```

Parameter declaration gains an optional call-site label:

```rust
struct Parameter {
    // ... existing fields ...
    call_site_label: Option<String>,
}
```

## Type Checker Validation

- Call-site labels must match declaration labels
- Missing label when declared: error
- Wrong label: error with suggestion
- Unlabeled argument to labeled parameter: allowed (positional matching)

Example error:

```
error: argument label mismatch
  --> file.spl:10:15
   |
10 |     copy_from(src from, dst)
   |                   ^^^^ expected label 'to', found 'from'
```

## Edge Cases

### Label keyword as variable name

```simple
val to = "dest.txt"
copy_from(to to, from)  # Variable 'to' labeled with 'to', variable 'from' unlabeled
```

Unambiguous with commas: expression `to` parsed first, then label `to` consumed.

### No label on unlabeled parameter

```simple
fn process(data: bytes, verbose: bool)
process(raw_data, true)  # No labels - works fine
```

### Multiple labels per argument

Not allowed. Each argument has at most one label.

## Backward Compatibility

Fully backward compatible:
- Functions without labels work as before
- Named arguments (`name: value`) unchanged
- Optional feature - labels are opt-in per parameter

## Implementation Files

- `rust/parser/src/expressions/helpers.rs` - argument parsing (add postfix label check)
- `rust/parser/src/ast/nodes/core.rs` - `Argument` and `Parameter` structs
- `rust/parser/src/token.rs` - `TokenKind::To`, `TokenKind::From` (already exist)
- Type checker - validate label matching at call sites
