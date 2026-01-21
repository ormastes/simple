# Lean Block Design

## Overview

The `lean{}` block allows embedding Lean 4 code directly in Simple source files or importing external Lean 4 files. This enables formal verification to live alongside implementation code.

## Grammar

### Inline Lean Block

```simple
lean {
    -- Lean 4 code here
    theorem my_theorem : ∀ n : Nat, n + 0 = n := by
        simp
}
```

### Lean Import Block

```simple
lean import "proofs/memory_safety.lean"
```

### Combined (Import + Inline Extensions)

```simple
lean import "proofs/base.lean" {
    -- Additional Lean code extending the import
    theorem extended_theorem : ... := by
        apply base_lemma
        simp
}
```

## Formal Grammar (EBNF)

```ebnf
lean_block      ::= 'lean' lean_content
lean_content    ::= lean_import? lean_body?
lean_import     ::= 'import' STRING_LITERAL
lean_body       ::= '{' lean_code '}'
lean_code       ::= <any text until matching '}'>
```

**Lexer Note**:
- `lean{...}` (no space) is tokenized as a `CustomBlock { kind: "lean", payload }` token
- The lexer switches to "raw mode" collecting text until the matching closing brace
- `lean` followed by `import` is parsed contextually (not as a keyword) to preserve backward compatibility with module paths like `verification.lean.codegen`

## Placement Contexts

### 1. Module Level (Top-Level)

```simple
# my_math.spl

lean {
    namespace MyMath
    theorem add_comm : ∀ a b : Nat, a + b = b + a := by
        omega
    end MyMath
}

fn add(a: i64, b: i64) -> i64:
    a + b
```

### 2. Function Level (Verification Block)

```simple
fn binary_search(arr: [i32], target: i32) -> Option<i32>:
    in:
        arr.is_sorted()
    out(result):
        result.is_some() ==> arr[result.unwrap()] == target

    lean {
        theorem binary_search_correct :
            ∀ arr target, sorted arr →
            match binary_search arr target with
            | some i => arr[i] = target
            | none => target ∉ arr := by
                sorry -- proof here
    }

    # Implementation
    var low = 0
    var high = arr.len() - 1
    while low <= high:
        val mid = (low + high) / 2
        if arr[mid] == target:
            return Some(mid)
        elif arr[mid] < target:
            low = mid + 1
        else:
            high = mid - 1
    None
```

### 3. Type/Struct Level

```simple
struct RedBlackTree<T>:
    lean {
        -- Invariant: Red nodes have black children
        def rb_invariant (t : RBTree) : Prop :=
            match t with
            | .leaf => True
            | .node c l _ r =>
                (c = .red → l.color = .black ∧ r.color = .black) ∧
                rb_invariant l ∧ rb_invariant r
    }

    root: Option<Node<T>>
    size: i64
```

## File Organization

Lean files are placed beside Simple source files:

```
src/
├── my_module.spl           # Simple source
├── my_module.lean          # Generated/imported Lean (auto-created)
└── proofs/
    ├── my_module_base.lean # External Lean proofs (manually written)
    └── my_module_ext.lean  # Extension proofs
```

### Naming Conventions

| Simple File | Generated Lean | Import Path |
|-------------|----------------|-------------|
| `foo.spl` | `foo.lean` | `"foo.lean"` or `"./foo.lean"` |
| `bar/baz.spl` | `bar/baz.lean` | `"bar/baz.lean"` |

### Import Resolution

```simple
# In src/algo/sort.spl
lean import "proofs/sort_correctness.lean"  # Relative to sort.spl
lean import "/verification/sort.lean"       # Absolute from project root
```

## Compilation Flow

```
┌─────────────────┐
│  my_module.spl  │
│  ┌───────────┐  │
│  │ lean { }  │  │
│  └───────────┘  │
└────────┬────────┘
         │
    ┌────▼────┐
    │  Parse  │
    └────┬────┘
         │
    ┌────▼────────────────┐
    │ Extract Lean Blocks │
    └────┬────────────────┘
         │
    ┌────▼──────────────────────────┐
    │ Generate my_module.lean       │
    │ - Imports from lean import    │
    │ - Inline lean { } content     │
    │ - Auto-generated contracts    │
    └────┬──────────────────────────┘
         │
    ┌────▼────────────────┐
    │ Verify with Lean 4  │
    │ (if --verify flag)  │
    └─────────────────────┘
```

## AST Representation

### New AST Node

```rust
// src/parser/src/ast/nodes/statements.rs

/// A lean block containing Lean 4 code
#[derive(Debug, Clone, PartialEq)]
pub struct LeanBlock {
    pub span: Span,
    /// Optional import path (relative or absolute)
    pub import_path: Option<String>,
    /// Inline Lean code (may be empty if import-only)
    pub code: String,
    /// Context: where this lean block appears
    pub context: LeanBlockContext,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LeanBlockContext {
    /// Top-level module
    Module,
    /// Inside a function definition
    Function(String),  // function name
    /// Inside a struct/type definition
    Type(String),      // type name
}
```

### Token Addition

```rust
// src/parser/src/token.rs

pub enum TokenKind {
    // ... existing tokens ...

    /// 'lean' keyword
    Lean,
    /// Raw Lean code content (between { })
    LeanCode(String),
}
```

## Parser Implementation

### Lexer Changes

The lexer needs a special mode for lean blocks:

```rust
// Pseudocode for lexer
fn lex_lean_block(&mut self) -> Token {
    self.expect('{');
    let mut depth = 1;
    let mut code = String::new();

    while depth > 0 {
        match self.peek() {
            '{' => { depth += 1; code.push('{'); }
            '}' => {
                depth -= 1;
                if depth > 0 { code.push('}'); }
            }
            c => code.push(c),
        }
        self.advance();
    }

    Token::LeanCode(code.trim().to_string())
}
```

### Parser Changes

```rust
// src/parser/src/stmt_parsing/lean.rs (new file)

impl Parser {
    pub fn parse_lean_block(&mut self) -> Result<LeanBlock, ParseError> {
        let start = self.current_span();
        self.expect(TokenKind::Lean)?;

        // Optional import
        let import_path = if self.check(TokenKind::Import) {
            self.advance();
            Some(self.expect_string_literal()?)
        } else {
            None
        };

        // Optional inline code
        let code = if self.check(TokenKind::LBrace) {
            self.advance();
            let code_token = self.expect(TokenKind::LeanCode)?;
            self.expect(TokenKind::RBrace)?;
            code_token.as_string()
        } else {
            String::new()
        };

        // Must have at least one of import or code
        if import_path.is_none() && code.is_empty() {
            return Err(ParseError::new(
                "lean block must have import path or inline code",
                start,
            ));
        }

        Ok(LeanBlock {
            span: start.merge(self.previous_span()),
            import_path,
            code,
            context: LeanBlockContext::Module, // Set by caller
        })
    }
}
```

## Generated Lean File Structure

For a Simple file with lean blocks:

```simple
# math.spl

lean import "proofs/axioms.lean"

lean {
    def helper_lemma : ... := sorry
}

fn factorial(n: i64) -> i64:
    in:
        n >= 0
    lean {
        theorem factorial_positive : ∀ n, n ≥ 0 → factorial n > 0 := by
            sorry
    }
    if n <= 1:
        1
    else:
        n * factorial(n - 1)
```

Generates `math.lean`:

```lean
-- Auto-generated from math.spl
-- DO NOT EDIT - changes will be overwritten

import Mathlib.Tactic
import «proofs/axioms»  -- from: lean import "proofs/axioms.lean"

namespace Math

/-! ## Module-Level Definitions -/

def helper_lemma : ... := sorry

/-! ## Function: factorial -/

-- Contract: requires n >= 0
def factorial_precondition (n : Int) : Prop := n ≥ 0

-- User-provided theorem
theorem factorial_positive : ∀ n, n ≥ 0 → factorial n > 0 := by
    sorry

end Math
```

## CLI Integration

```bash
# Generate Lean file from Simple source
simple --gen-lean src/math.spl

# Generate and verify
simple --gen-lean src/math.spl --verify

# Verify specific aspects
simple --gen-lean src/math.spl --verify memory
simple --gen-lean src/math.spl --verify contracts
simple --gen-lean src/math.spl --verify all
```

## Error Handling

### Parse Errors

```
error: unbalanced braces in lean block
  --> src/math.spl:15:1
   |
15 | lean {
   | ^^^^ lean block started here
   |
   = help: ensure all '{' have matching '}'
```

### Import Errors

```
error: lean import file not found
  --> src/math.spl:3:13
   |
3  | lean import "proofs/missing.lean"
   |             ^^^^^^^^^^^^^^^^^^^^^ file not found
   |
   = help: create file at src/proofs/missing.lean
```

### Verification Errors

```
error: lean verification failed
  --> src/math.spl:20:5
   |
20 |     lean {
   |     ^^^^ in this lean block
   |
   = lean error: type mismatch at theorem statement
   = see math.lean:45 for full error
```

## Examples

### Example 1: Pure Verification Module

```simple
# verification/list_proofs.spl

lean {
    namespace ListProofs

    theorem append_assoc :
        ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
        intros xs ys zs
        induction xs with
        | nil => simp
        | cons x xs ih => simp [ih]

    theorem reverse_reverse :
        ∀ (xs : List α), xs.reverse.reverse = xs := by
        intros xs
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [ih]

    end ListProofs
}
```

### Example 2: Mixed Implementation and Verification

```simple
# collections/sorted_set.spl

struct SortedSet<T>:
    lean {
        -- Invariant: elements are strictly sorted
        def sorted_invariant (s : SortedSet) : Prop :=
            ∀ i j, i < j → i < s.data.length → j < s.data.length →
                s.data[i] < s.data[j]
    }

    data: [T]

impl SortedSet<T>:
    fn insert(item: T) -> bool:
        in:
            true
        out(result):
            result ==> self.contains(item)
        lean {
            theorem insert_preserves_sorted :
                sorted_invariant s → sorted_invariant (s.insert x) := by
                sorry
        }

        # Binary search for insertion point
        val pos = self.find_position(item)
        if pos < self.data.len() && self.data[pos] == item:
            false  # Already exists
        else:
            self.data.insert(pos, item)
            true
```

### Example 3: Importing External Proofs

```simple
# crypto/hash.spl

# Import pre-written cryptographic proofs
lean import "crypto_proofs/collision_resistance.lean"

fn hash(data: [u8]) -> [u8; 32]:
    lean {
        -- Reference imported theorem
        #check collision_resistance_theorem
    }
    # ... implementation ...
```

## Future Extensions

For detailed plans on verification improvements, see [Verification Improvements Plan](verification_improvements_plan.md).

### Planned Features

| Feature | Description | Priority |
|---------|-------------|----------|
| Ghost code | `@ghost` functions for spec-only code | High |
| Loop invariants | `invariant:` clauses in loops | High |
| Refinement types | `type NonZero = i64 where self != 0` | High |
| Proof hints | `lean hint: "tactic"` guidance | Medium |
| Assert/Assume/Admit | Different trust levels | Medium |
| Incremental verification | Cache proof results | Medium |

### 1. Ghost Code (VER-001)

```simple
@ghost
fn sorted(arr: [i32]) -> bool:
    forall i in 0..arr.len()-1: arr[i] <= arr[i+1]

@verify
fn sort(arr: [i32]) -> [i32]:
    out(result): sorted(result)  # Ghost call in contract OK
    # ...
```

### 2. Loop Invariants (VER-002)

```simple
@verify
fn sum(arr: [i32]) -> i64:
    var total: i64 = 0
    for i in 0..arr.len():
        invariant: total == sum_spec(arr, i)
        total = total + arr[i]
    total
```

### 3. Refinement Types (VER-010)

```simple
type NonZero = i64 where self != 0

fn divide(a: i64, b: NonZero) -> i64:
    a / b  # No precondition needed - in type
```

### 4. Proof Hints (VER-020)

```simple
@verify
fn factorial(n: i64) -> i64:
    lean hint: "induction n <;> simp [*]"
    if n <= 1: 1
    else: n * factorial(n - 1)
```

## Summary

The `lean{}` block provides:

1. **Inline Lean code** embedded directly in Simple source
2. **External imports** for larger proof developments
3. **Context-aware placement** at module, function, or type level
4. **Automatic file generation** placing `.lean` files beside `.spl` files
5. **Integrated verification** via CLI flags

This design follows existing patterns in the codebase (contract blocks, custom blocks) while enabling powerful formal verification capabilities.
