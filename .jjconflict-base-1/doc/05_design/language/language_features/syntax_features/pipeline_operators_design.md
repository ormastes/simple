# Pipeline Operators and Dimension Checking Design

## Overview

Simple provides pipeline operators for functional composition and neural network layer chaining, with compile-time and runtime dimension checking to catch shape mismatches early.

## Pipeline Operators

### Operator Summary

| Operator | Name | Associativity | Description |
|----------|------|---------------|-------------|
| `\|>` | Pipe Forward | Left | Pass value to function: `x \|> f` = `f(x)` |
| `>>` | Compose | Right | Forward composition: `f >> g` = `λx. g(f(x))` |
| `<<` | Compose Back | Right | Backward composition: `f << g` = `λx. f(g(x))` |
| `//` | Parallel | Left | Parallel branches: `f // g` runs both |
| `~>` | Layer Connect | Left | NN layer pipeline with dimension checking |

### Precedence (Low to High)

```
15. Pipeline (|>, ~>)     ← Lowest
14. Parallel (//)
13. Compose (>>, <<)
12. Logical OR (or, ||)
11. Logical AND (and, &&)
... (standard operators)
1.  Primary               ← Highest
```

---

## Pipe Forward (`|>`)

Passes the left operand as the first argument to the right operand.

### Syntax
```simple
value |> function
value |> function |> another_function
```

### Type Rule
```
Γ ⊢ x : A    Γ ⊢ f : A → B
───────────────────────────
    Γ ⊢ x |> f : B
```

### Examples

```simple
# Basic usage
val result = 5 |> double |> square |> to_string
# Equivalent to: to_string(square(double(5)))

# With lambdas
val processed = data
    |> \x: x.filter(\item: item > 0)
    |> \x: x.map(\item: item * 2)
    |> \x: x.sum()

# Data processing pipeline
val output = raw_input
    |> parse_json
    |> validate
    |> transform
    |> serialize
```

### Method Chaining Comparison

```simple
# Pipe forward style
data |> normalize |> augment |> batch

# Method chaining style (equivalent)
data.normalize().augment().batch()
```

---

## Function Composition (`>>`, `<<`)

Creates a new function by composing two functions.

### Syntax
```simple
f >> g      # Forward: apply f first, then g
f << g      # Backward: apply g first, then f (like Haskell's .)
```

### Type Rules
```
Γ ⊢ f : A → B    Γ ⊢ g : B → C
──────────────────────────────
    Γ ⊢ f >> g : A → C

Γ ⊢ f : B → C    Γ ⊢ g : A → B
──────────────────────────────
    Γ ⊢ f << g : A → C
```

### Examples

```simple
# Create reusable pipeline
val preprocess = normalize >> augment >> to_tensor
val result = preprocess(raw_data)

# Backward composition (Haskell-style)
val pipeline = serialize << transform << validate
# Same as: validate >> transform >> serialize

# Point-free style
val double = \x: x * 2
val square = \x: x * x
val double_then_square = double >> square

assert double_then_square(3) == 36  # (3 * 2)^2
```

### Right Associativity

```simple
# f >> g >> h is parsed as f >> (g >> h)
val pipeline = a >> b >> c >> d
# Creates: λx. d(c(b(a(x))))
```

---

## Parallel (`//`)

Runs two operations in parallel, combining their results.

### Syntax
```simple
f // g
```

### Type Rule
```
Γ ⊢ f : A → B    Γ ⊢ g : C → D
──────────────────────────────
  Γ ⊢ f // g : (A, C) → (B, D)
```

### Examples

```simple
# Parallel function application
val both = inc // dec
val (a, b) = both(5, 5)  # (6, 4)

# Parallel data processing
val process_both = encode_audio // encode_video
val (audio, video) = process_both(raw_audio, raw_video)

# Neural network parallel branches
val features = conv_branch // pool_branch
```

---

## Layer Connect (`~>`)

Composes neural network layers with compile-time dimension checking.

### Syntax
```simple
layer1 ~> layer2 ~> layer3
```

### Type Rule
```
Γ ⊢ l1 : Layer<A, B>    Γ ⊢ l2 : Layer<B', C>    unify(B, B') = σ
─────────────────────────────────────────────────────────────────
                Γ ⊢ l1 ~> l2 : Layer<σA, σC>
```

### Examples

```simple
# MLP with dimension checking
val mlp = Linear(784, 256) ~> ReLU() ~> Linear(256, 128) ~> ReLU() ~> Linear(128, 10)
# Type: Layer<[batch, 784], [batch, 10]>

# CNN encoder
val encoder = Conv2d(1, 32, 3) ~> ReLU() ~> MaxPool2d(2)
              ~> Conv2d(32, 64, 3) ~> ReLU() ~> MaxPool2d(2)
              ~> Flatten() ~> Linear(1600, 256)

# Autoencoder
val encoder = Linear(784, 256) ~> ReLU() ~> Linear(256, 64)
val decoder = Linear(64, 256) ~> ReLU() ~> Linear(256, 784)
val autoencoder = encoder ~> decoder
# Type: Layer<[batch, 784], [batch, 784]>
```

### Compile-Time Error Example

```simple
# ERROR: dimension mismatch
val bad = Linear(784, 256) ~> Linear(128, 64)
```

```
error[E0502]: layer dimension mismatch in ~> pipeline
  --> model.spl:1:35
   |
   = found: previous layer outputs shape: [batch, 256]
   = expected: next layer expects input shape: [batch, 128]
   = note: dimension 1 differs: 256 vs 128
   = help: insert Linear(256, 128) between these layers
```

---

## Dimension Checking

### Two-Phase Checking

| Phase | When | What's Checked |
|-------|------|----------------|
| **Compile-time** | Type inference | Static dimensions (literals, const params) |
| **Runtime** | Before forward pass | Dynamic dimensions (batch size, sequence length) |

### Dimension Expressions

```simple
# Literal dimension
784

# Named dimension with range
batch: 1..128

# Dynamic (runtime only)
?

# Const parameter
N  # from generic: fn process<N>(...)

# Arithmetic
M * K
H / num_heads
```

### Dimension Check Modes

```simple
# Configure in code or build flags
enum DimCheckMode:
    None_   # No checks (production)
    Assert  # Debug assertions (default)
    Log     # Warn but continue
    Strict  # Return error
```

### Where Clauses (Future)

```simple
fn matmul<M, K, N>(
    a: Tensor<f32, [M, K]>,
    b: Tensor<f32, [K, N]>
) -> Tensor<f32, [M, N]>
where K: 1..4096:
    a @ b
```

---

## Error Codes Reference

| Code | Name | Description |
|------|------|-------------|
| E0501 | Mismatch | Basic dimension mismatch |
| E0502 | LayerIncompatible | Layer output/input mismatch |
| E0503 | RankMismatch | Tensor rank (ndim) mismatch |
| E0504 | MatMulIncompat | Matrix multiplication K mismatch |
| E0505 | BroadcastIncompat | Cannot broadcast shapes |
| E0506 | BatchMismatch | Batch dimension mismatch |
| E0507 | ChannelMismatch | CNN channel mismatch |
| E0508 | SequenceMismatch | Sequence length mismatch |
| E0509 | OutOfRange | Dimension outside range |
| E0510 | UnresolvedVariable | Cannot infer dimension |
| E0511 | ProductEquals | Product constraint failed |
| E0512 | RankMismatch | Layer rank mismatch |

---

## Implementation Details

### Files

| File | Purpose |
|------|---------|
| `simple/compiler/lexer.spl` | Token definitions for operators |
| `simple/compiler/parser.spl` | Parsing and precedence |
| `simple/compiler/hir.spl` | DimExpr, LayerType, HirBinOp variants |
| `simple/compiler/dim_constraints.spl` | Constraint solver, error messages |
| `simple/compiler/type_infer.spl` | Integration with HM inference |

### Lexer Tokens

```simple
enum TokenKind:
    # ... existing ...
    PipeForward     # |>
    Compose         # >>
    ComposeBack     # <<
    Parallel        # //
    LayerConnect    # ~>
```

### Generic Depth Tracking

The lexer tracks `<>` nesting to disambiguate `>>`:

```simple
Dict<List<Int>>   # >> here is two > tokens (closing generics)
f >> g            # >> here is Compose operator
```

---

## Best Practices

### 1. Use `~>` for Neural Networks

```simple
# Good: Dimension-checked pipeline
val model = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)

# Avoid: Manual forward calls
fn forward(x):
    var h = self.linear1(x)
    h = self.relu(h)
    self.linear2(h)
```

### 2. Use `|>` for Data Transformations

```simple
# Good: Clear data flow
val result = raw_data
    |> preprocess
    |> validate
    |> transform

# Avoid: Nested calls
val result = transform(validate(preprocess(raw_data)))
```

### 3. Use `>>` for Reusable Pipelines

```simple
# Good: Composable, reusable
val preprocess = normalize >> augment >> to_tensor
val train_data = load_data() |> preprocess
val test_data = load_test() |> preprocess

# Avoid: Repeated code
val train_data = to_tensor(augment(normalize(load_data())))
val test_data = to_tensor(augment(normalize(load_test())))
```

### 4. Add Type Annotations for Clarity

```simple
# Explicit layer types help catch errors early
val encoder: Layer<[batch, 784], [batch, 64]> =
    Linear(784, 256) ~> ReLU() ~> Linear(256, 64)
```

---

## Future Work

1. **Where Clauses**: Dimension constraints in function signatures
2. **Symbolic Dimensions**: `N`, `M` in type signatures
3. **Lean Verification**: Formal proofs of dimension correctness
4. **IDE Integration**: Real-time dimension error highlighting
5. **Auto-fix Suggestions**: Automatic layer insertion
