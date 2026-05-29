## Part 3: Kernel Bounds Policy

This section defines the default and programmable behavior when indexing may underflow or overflow in GPU kernels using the `@simd` annotation.

### 3.1 Terms

- **Indexable variable**: any expression used as `base[index...]` (array, buffer, user indexer)
- **Underflow**: `index < lower bound` (typically < 0)
- **Overflow**: `index >= upper bound` (typically >= length)
- **Bounds event**: a dynamic situation where an index operation would underflow/overflow

### 3.2 Default Rule

**`@simd` implies `@bounds(default=return, strict=true)`**

Every `@simd` kernel has an implicit bounds policy unless explicitly overridden:

- `default=return`: any bounds event causes the current GPU thread to return from the kernel
- `strict=true`: the compiler performs static coverage analysis; uncovered possible bounds events must be diagnosed

Override per kernel:

```simple
@simd @bounds(default=trap, strict=true)
fn my_kernel(...):
    ...
```

### 3.3 `@bounds(...)` Attribute

Parameters:

| Parameter | Values | Description |
|-----------|--------|-------------|
| `default` | `return`, `trap`, `panic`, `ignore` | What to do on uncovered bounds events |
| `strict` | `true`, `false` | Whether to require coverage analysis |

- `return`: early-exit the current GPU thread
- `trap`: device trap/abort for the kernel (backend-defined)
- `panic`: host-visible failure (requires runtime support)
- `ignore`: proceed without intervention (unsafe; intended only with explicit `bounds:` cases)

### 3.4 `bounds:` Clause (Pattern-Based Handlers)

A `@simd` kernel may include a trailing `bounds:` block that defines handlers:

```simple
@simd
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]

bounds:
    _.out.over:
        return
    _.out.under:
        return
```

#### Pattern Keys

A bounds case label is a boolean condition composed of bounds atoms:

- **Bounds atom**: `_.<var>.<kind>` where `<var>` is the base variable and `<kind>` is `over` or `under`
- **Boolean composition**: `&&`, `||`, parentheses `(...)` are permitted

Examples:
- `_.out.over:`
- `(_.a.over || _.b.over) && _.out.over:`
- `_.out.under || _.out.over:`

#### Default Handler

```simple
bounds:
    _.x.over:
        return
    _:                    # Catch-all
        return
```

#### Rules

1. **Fallthrough is an error**: Each case body must end in a terminator (`return`, `trap`, `panic`)
2. **Dead code diagnostics**: Unreachable/shadowed cases are errors under `strict=true`
3. **Uncovered case diagnostics**: Under `strict=true`, all reachable bounds events must be covered

### 3.5 Interaction with `@skip_index_range_check`

`@skip_index_range_check` disables bounds checks at indexing operation sites. It is invalid to combine:
- `@skip_index_range_check` with `@bounds(strict=true)` unless the compiler can prove no out-of-bounds

---

