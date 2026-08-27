# Deep Learning Equation Tests for m{} Math Blocks

> Tests that composite DL equations parse, evaluate correctly, render to LaTeX, and render to nvim-friendly Unicode. Covers all 27 DL equations found in `examples/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 72 | 72 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deep Learning Equation Tests for m{} Math Blocks

Tests that composite DL equations parse, evaluate correctly, render to LaTeX, and render to nvim-friendly Unicode. Covers all 27 DL equations found in `examples/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (DL equation coverage) |
| Category | Syntax / Math DSL |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/math_dl_equations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that composite DL equations parse, evaluate correctly, render to LaTeX,
and render to nvim-friendly Unicode. Covers all 27 DL equations found in
`examples/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

## Scenarios

### DL Activations

#### Sigmoid: frac(1, 1 + exp(-x))

#### evaluates sigmoid(2) correctly

- evaluates sigmoid(2) correctly
   - Expected: close(result, 0.8808, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates sigmoid(2) correctly")
val x = 2.0
val result = m{ frac(1, 1 + exp(-x)) }
expect(close(result, 0.8808, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates sigmoid(2) correctly")<br>
> val x = 2.0<br>
> val result = $\frac{1}{1 + \exp(-x)}$<br>
> expect(close(result, 0.8808, 0.01)).to_equal(true)

</details>

</details>

#### renders sigmoid LaTeX

- renders sigmoid LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders sigmoid LaTeX")
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders sigmoid Unicode

- renders sigmoid Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders sigmoid Unicode")
val pretty = to_pretty("frac(1, 1 + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

#### Tanh: frac(exp(x) - exp(-x), exp(x) + exp(-x))

#### evaluates tanh(1) correctly

- evaluates tanh(1) correctly
   - Expected: close(result, 0.7616, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates tanh(1) correctly")
val x = 1.0
val result = m{ frac(exp(x) - exp(-x), exp(x) + exp(-x)) }
expect(close(result, 0.7616, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates tanh(1) correctly")<br>
> val x = 1.0<br>
> val result = $\frac{\exp(x) - \exp(-x)}{\exp(x) + \exp(-x)}$<br>
> expect(close(result, 0.7616, 0.01)).to_equal(true)

</details>

</details>

#### renders tanh LaTeX

- renders tanh LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders tanh LaTeX")
val latex = render_latex_raw("frac(exp(x) - exp(-x), exp(x) + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders tanh Unicode

- renders tanh Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders tanh Unicode")
val pretty = to_pretty("frac(exp(x) - exp(-x), exp(x) + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

#### ReLU: max(0, x)

#### evaluates relu(3) correctly

- evaluates relu(3) correctly
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates relu(3) correctly")
val x = 3.0
val result = m{ max(0, x) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates relu(3) correctly")<br>
> val x = 3.0<br>
> val result = $\max(0, x)$<br>
> expect(result).to_equal(3.0)

</details>

</details>

#### evaluates relu(-2) correctly

- evaluates relu(-2) correctly
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates relu(-2) correctly")
val x = -2.0
val result = m{ max(0, x) }
expect(result).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates relu(-2) correctly")<br>
> val x = -2.0<br>
> val result = $\max(0, x)$<br>
> expect(result).to_equal(0.0)

</details>

</details>

#### renders relu LaTeX

- renders relu LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders relu LaTeX")
val latex = render_latex_raw("max(0, x)")
expect(latex).to_contain("\\max")
```

</details>

#### renders relu Unicode

- renders relu Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders relu Unicode")
val pretty = to_pretty("max(0, x)")
expect(pretty).to_contain("max")
```

</details>

#### GELU: x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))

#### evaluates gelu(1) correctly

- evaluates gelu(1) correctly
   - Expected: close(result, 0.8412, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates gelu(1) correctly")
val x = 1.0
val result = m{ x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3))) }
expect(close(result, 0.8412, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates gelu(1) correctly")<br>
> val x = 1.0<br>
> val result = $x \cdot 0.5 \cdot (1 + \tanh(\sqrt{\frac{2}{\pi}} \cdot (x + 0.044715 \cdot x^{3})))$<br>
> expect(close(result, 0.8412, 0.01)).to_equal(true)

</details>

</details>

#### renders gelu LaTeX

- renders gelu LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders gelu LaTeX")
val latex = render_latex_raw("x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))")
expect(latex).to_contain("\\tanh")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders gelu Unicode

- renders gelu Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders gelu Unicode")
val pretty = to_pretty("x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))")
expect(pretty).to_contain("π")
```

</details>

#### Softmax denominator: exp(x) / sum(exp(x))

#### evaluates softmax component

- evaluates softmax component
   - Expected: close(result, 7.389, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates softmax component")
val x = 2.0
val result = m{ exp(x) }
expect(close(result, 7.389, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates softmax component")<br>
> val x = 2.0<br>
> val result = $\exp(x)$<br>
> expect(close(result, 7.389, 0.01)).to_equal(true)

</details>

</details>

#### renders softmax LaTeX

- renders softmax LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders softmax LaTeX")
val latex = render_latex_raw("exp(x - max(x)) / sum(exp(x - max(x)))")
expect(latex).to_contain("\\exp")
expect(latex).to_contain("\\max")
```

</details>

#### renders softmax Unicode

- renders softmax Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders softmax Unicode")
val pretty = to_pretty("exp(x - max(x)) / sum(exp(x - max(x)))")
expect(pretty).to_contain("exp")
expect(pretty).to_contain("max")
```

</details>

### DL Normalization

#### Layer Norm: frac(x - mu, sqrt(sigma^2 + epsilon)) * gamma + beta

#### evaluates layer norm with concrete values

- evaluates layer norm with concrete values
   - Expected: close(result, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates layer norm with concrete values")
val x = 5.0
val mu = 3.0
val sigma = 2.0
val epsilon = 0.00001
val gamma = 1.0
val beta = 0.0
val result = m{ frac(x - mu, sqrt(sigma^2 + epsilon)) * gamma + beta }
expect(close(result, 1.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates layer norm with concrete values")<br>
> val x = 5.0<br>
> val mu = 3.0<br>
> val sigma = 2.0<br>
> val epsilon = 0.00001<br>
> val gamma = 1.0<br>
> val beta = 0.0<br>
> val result = $\frac{x - \mu}{\sqrt{\sigma^{2} + \epsilon}} \cdot \gamma + \beta$<br>
> expect(close(result, 1.0, 0.01)).to_equal(true)

</details>

</details>

#### renders layer norm LaTeX

- renders layer norm LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders layer norm LaTeX")
val latex = render_latex_raw("frac(x - mu, sqrt(sigma^2 + epsilon)) * gamma + beta")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\mu")
expect(latex).to_contain("\\sigma")
expect(latex).to_contain("\\epsilon")
expect(latex).to_contain("\\gamma")
expect(latex).to_contain("\\beta")
```

</details>

#### renders layer norm Unicode

- renders layer norm Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders layer norm Unicode")
val pretty = to_pretty("frac(x - mu, sqrt(sigma^2 + epsilon)) * gamma + beta")
expect(pretty).to_contain("μ")
expect(pretty).to_contain("σ")
expect(pretty).to_contain("ε")
expect(pretty).to_contain("γ")
expect(pretty).to_contain("β")
```

</details>

#### RMS Norm: x * w / sqrt(mean(x^2) + epsilon)

#### renders rms norm LaTeX

- renders rms norm LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders rms norm LaTeX")
val latex = render_latex_raw("x * w / sqrt(mean(x^2) + epsilon)")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\epsilon")
```

</details>

#### renders rms norm Unicode

- renders rms norm Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders rms norm Unicode")
val pretty = to_pretty("x * w / sqrt(mean(x^2) + epsilon)")
expect(pretty).to_contain("ε")
```

</details>

#### Dropout scaling: frac(x, 1 - p)

#### evaluates dropout scaling

- evaluates dropout scaling
   - Expected: close(result, 20.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates dropout scaling")
val x = 10.0
val p = 0.5
val result = m{ frac(x, 1 - p) }
expect(close(result, 20.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates dropout scaling")<br>
> val x = 10.0<br>
> val p = 0.5<br>
> val result = $\frac{x}{1 - p}$<br>
> expect(close(result, 20.0, 0.01)).to_equal(true)

</details>

</details>

#### renders dropout LaTeX

- renders dropout LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders dropout LaTeX")
val latex = render_latex_raw("frac(x, 1 - p)")
expect(latex).to_contain("\\frac")
```

</details>

#### renders dropout Unicode

- renders dropout Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders dropout Unicode")
val pretty = to_pretty("frac(x, 1 - p)")
expect(pretty).to_contain("x")
```

</details>

### DL Layers

#### Linear: matmul(x, transpose(W)) + b

#### renders linear LaTeX

- renders linear LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders linear LaTeX")
val latex = render_latex_raw("matmul(x, transpose(W)) + b")
expect(latex).to_contain(r"\operatorname{matmul}")
expect(latex).to_contain(r"\operatorname{transpose}")
```

</details>

#### renders linear Unicode

- renders linear Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders linear Unicode")
val pretty = to_pretty("matmul(x, transpose(W)) + b")
expect(pretty).to_contain("matmul")
expect(pretty).to_contain("transpose")
```

</details>

#### Embedding: W[token_id]

#### renders embedding LaTeX with subscript

- renders embedding LaTeX with subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders embedding LaTeX with subscript")
val latex = render_latex_raw("W[token_id]")
expect(latex).to_contain("W")
expect(latex).to_contain("token")
```

</details>

#### renders embedding Unicode

- renders embedding Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders embedding Unicode")
val pretty = to_pretty("W[token_id]")
expect(pretty).to_contain("W")
```

</details>

#### FFN: matmul(relu(matmul(x, W1) + b1), W2) + b2

#### renders FFN LaTeX

- renders FFN LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders FFN LaTeX")
val latex = render_latex_raw("matmul(relu(matmul(x, W1) + b1), W2) + b2")
expect(latex).to_contain(r"\operatorname{matmul}")
expect(latex).to_contain(r"\operatorname{relu}")
```

</details>

#### renders FFN Unicode

- renders FFN Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders FFN Unicode")
val pretty = to_pretty("matmul(relu(matmul(x, W1) + b1), W2) + b2")
expect(pretty).to_contain("matmul")
expect(pretty).to_contain("relu")
```

</details>

### DL Attention & Architecture

#### Scaled Dot-Product Attention: softmax(frac(matmul(Q, K'), sqrt(d_k))) * V

#### renders attention LaTeX

- renders attention LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders attention LaTeX")
val latex = render_latex_raw("softmax(frac(matmul(Q, K'), sqrt(d_k))) * V")
expect(latex).to_contain(r"\operatorname{softmax}")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders attention Unicode

- renders attention Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders attention Unicode")
val pretty = to_pretty("softmax(frac(matmul(Q, K'), sqrt(d_k))) * V")
expect(pretty).to_contain("softmax")
```

</details>

#### Multi-Head Attention: matmul(concat_heads, W_o)

#### renders MHA LaTeX

- renders MHA LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders MHA LaTeX")
val latex = render_latex_raw("matmul(concat_heads, W_o)")
expect(latex).to_contain(r"\operatorname{matmul}")
```

</details>

#### renders MHA Unicode

- renders MHA Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders MHA Unicode")
val pretty = to_pretty("matmul(concat_heads, W_o)")
expect(pretty).to_contain("matmul")
```

</details>

#### Transformer Block: x + sublayer(layernorm(x))

#### renders transformer block LaTeX

- renders transformer block LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders transformer block LaTeX")
val latex = render_latex_raw("x + sublayer(layernorm(x))")
expect(latex).to_contain(r"\operatorname{sublayer}")
expect(latex).to_contain(r"\operatorname{layernorm}")
```

</details>

#### renders transformer block Unicode

- renders transformer block Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders transformer block Unicode")
val pretty = to_pretty("x + sublayer(layernorm(x))")
expect(pretty).to_contain("sublayer")
expect(pretty).to_contain("layernorm")
```

</details>

#### Positional Encoding: sin(frac(pos, 10000^(frac(2 * i, d))))

#### renders positional encoding LaTeX

- renders positional encoding LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders positional encoding LaTeX")
val latex = render_latex_raw("sin(frac(pos, 10000^(frac(2 * i, d))))")
expect(latex).to_contain("\\sin")
expect(latex).to_contain("\\frac")
```

</details>

#### renders positional encoding Unicode

- renders positional encoding Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders positional encoding Unicode")
val pretty = to_pretty("sin(frac(pos, 10000^(frac(2 * i, d))))")
expect(pretty).to_contain("sin")
```

</details>

### DL Loss Functions

#### Cross-Entropy: frac(-1, N) * sum(i, 1..N) log(p[i])

#### renders cross-entropy LaTeX

- renders cross-entropy LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders cross-entropy LaTeX")
val latex = render_latex_raw("frac(-1, N) * sum(i, 1..N) log(p[i])")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sum_{")
expect(latex).to_contain("\\log")
```

</details>

#### renders cross-entropy Unicode

- renders cross-entropy Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders cross-entropy Unicode")
val pretty = to_pretty("frac(-1, N) * sum(i, 1..N) log(p[i])")
expect(pretty).to_contain("log")
```

</details>

#### MSE: frac(1, N) * sum(i, 1..N) (y[i] - yhat[i])^2

#### renders MSE LaTeX

- renders MSE LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders MSE LaTeX")
val latex = render_latex_raw("frac(1, N) * sum(i, 1..N) (y[i] - yhat[i])^2")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sum_{")
```

</details>

#### renders MSE Unicode

- renders MSE Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders MSE Unicode")
val pretty = to_pretty("frac(1, N) * sum(i, 1..N) (y[i] - yhat[i])^2")
expect(pretty).to_contain("N")
```

</details>

#### Temperature scaling: frac(logits, T)

#### evaluates temperature scaling

- evaluates temperature scaling
   - Expected: close(result, 3.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates temperature scaling")
val logits = 6.0
val T = 2.0
val result = m{ frac(logits, T) }
expect(close(result, 3.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates temperature scaling")<br>
> val logits = 6.0<br>
> val T = 2.0<br>
> val result = $\frac{logits}{T}$<br>
> expect(close(result, 3.0, 0.01)).to_equal(true)

</details>

</details>

#### renders temperature LaTeX

- renders temperature LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders temperature LaTeX")
val latex = render_latex_raw("frac(logits, T)")
expect(latex).to_contain("\\frac")
```

</details>

#### renders temperature Unicode

- renders temperature Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders temperature Unicode")
val pretty = to_pretty("frac(logits, T)")
expect(pretty).to_contain("logits")
```

</details>

### DL Optimizers

#### SGD: theta - alpha * grad

#### evaluates SGD update

- evaluates SGD update
   - Expected: close(result, 4.8, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates SGD update")
val theta = 5.0
val alpha = 0.1
val grad = 2.0
val result = m{ theta - alpha * grad }
expect(close(result, 4.8, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates SGD update")<br>
> val theta = 5.0<br>
> val alpha = 0.1<br>
> val grad = 2.0<br>
> val result = $\theta - \alpha \cdot grad$<br>
> expect(close(result, 4.8, 0.01)).to_equal(true)

</details>

</details>

#### renders SGD LaTeX

- renders SGD LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders SGD LaTeX")
val latex = render_latex_raw("theta - alpha * grad")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
```

</details>

#### renders SGD Unicode

- renders SGD Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders SGD Unicode")
val pretty = to_pretty("theta - alpha * grad")
expect(pretty).to_contain("θ")
expect(pretty).to_contain("α")
```

</details>

#### SGD+Momentum: theta - alpha * (mu * v + grad)

#### evaluates SGD+momentum update

- evaluates SGD+momentum update
   - Expected: close(result, 4.71, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates SGD+momentum update")
val theta = 5.0
val alpha = 0.1
val mu = 0.9
val v = 1.0
val grad = 2.0
val result = m{ theta - alpha * (mu * v + grad) }
expect(close(result, 4.71, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates SGD+momentum update")<br>
> val theta = 5.0<br>
> val alpha = 0.1<br>
> val mu = 0.9<br>
> val v = 1.0<br>
> val grad = 2.0<br>
> val result = $\theta - \alpha \cdot (\mu \cdot v + grad)$<br>
> expect(close(result, 4.71, 0.01)).to_equal(true)

</details>

</details>

#### renders SGD+momentum LaTeX

- renders SGD+momentum LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders SGD+momentum LaTeX")
val latex = render_latex_raw("theta - alpha * (mu * v + grad)")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\mu")
```

</details>

#### renders SGD+momentum Unicode

- renders SGD+momentum Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders SGD+momentum Unicode")
val pretty = to_pretty("theta - alpha * (mu * v + grad)")
expect(pretty).to_contain("θ")
expect(pretty).to_contain("α")
expect(pretty).to_contain("μ")
```

</details>

#### Adam bias correction: frac(m, 1 - beta^t)

#### evaluates adam bias correction

- evaluates adam bias correction
   - Expected: close(result, 3.69, 0.1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates adam bias correction")
val t = 3.0
val beta = 0.9
val result = m{ frac(1, 1 - beta^t) }
expect(close(result, 3.69, 0.1)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates adam bias correction")<br>
> val t = 3.0<br>
> val beta = 0.9<br>
> val result = $\frac{1}{1 - \beta^{t}}$<br>
> expect(close(result, 3.69, 0.1)).to_equal(true)

</details>

</details>

#### renders adam LaTeX

- renders adam LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders adam LaTeX")
val latex = render_latex_raw("frac(m, 1 - beta^t)")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\beta")
```

</details>

#### renders adam Unicode

- renders adam Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders adam Unicode")
val pretty = to_pretty("frac(m, 1 - beta^t)")
expect(pretty).to_contain("β")
```

</details>

#### Gradient clip: frac(c, sqrt(dot(g, g)))

#### renders gradient clip LaTeX

- renders gradient clip LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders gradient clip LaTeX")
val latex = render_latex_raw("frac(c, sqrt(dot(g, g)))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain(r"\operatorname{dot}")
```

</details>

#### renders gradient clip Unicode

- renders gradient clip Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders gradient clip Unicode")
val pretty = to_pretty("frac(c, sqrt(dot(g, g)))")
expect(pretty).to_contain("dot")
```

</details>

### DL Learning Rate

#### Linear Warmup: alpha * frac(step, warmup)

#### evaluates linear warmup

- evaluates linear warmup
   - Expected: close(result, 0.0005, 0.0001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates linear warmup")
val alpha = 0.001
val step = 500.0
val warmup = 1000.0
val result = m{ alpha * frac(step, warmup) }
expect(close(result, 0.0005, 0.0001)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates linear warmup")<br>
> val alpha = 0.001<br>
> val step = 500.0<br>
> val warmup = 1000.0<br>
> val result = $\alpha \cdot \frac{step}{warmup}$<br>
> expect(close(result, 0.0005, 0.0001)).to_equal(true)

</details>

</details>

#### renders warmup LaTeX

- renders warmup LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders warmup LaTeX")
val latex = render_latex_raw("alpha * frac(step, warmup)")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\frac")
```

</details>

#### renders warmup Unicode

- renders warmup Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders warmup Unicode")
val pretty = to_pretty("alpha * frac(step, warmup)")
expect(pretty).to_contain("α")
```

</details>

#### Cosine Decay: min_lr + (alpha - min_lr) * (1 - progress)

#### evaluates cosine decay at midpoint

- evaluates cosine decay at midpoint
   - Expected: close(result, 0.00055, 0.0001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates cosine decay at midpoint")
val min_lr = 0.0001
val alpha = 0.001
val progress = 0.5
val result = m{ min_lr + (alpha - min_lr) * (1 - progress) }
expect(close(result, 0.00055, 0.0001)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates cosine decay at midpoint")<br>
> val min_lr = 0.0001<br>
> val alpha = 0.001<br>
> val progress = 0.5<br>
> val result = $min_lr + (\alpha - min_lr) \cdot (1 - progress)$<br>
> expect(close(result, 0.00055, 0.0001)).to_equal(true)

</details>

</details>

#### renders cosine decay LaTeX

- renders cosine decay LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders cosine decay LaTeX")
val latex = render_latex_raw("min_lr + (alpha - min_lr) * (1 - progress)")
expect(latex).to_contain("\\alpha")
```

</details>

#### renders cosine decay Unicode

- renders cosine decay Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders cosine decay Unicode")
val pretty = to_pretty("min_lr + (alpha - min_lr) * (1 - progress)")
expect(pretty).to_contain("α")
```

</details>

### DL Metrics & Init

#### Cosine Similarity: frac(dot(a, b), sqrt(dot(a, a)) * sqrt(dot(b, b)))

#### evaluates cosine similarity of parallel vectors

- evaluates cosine similarity of parallel vectors
   - Expected: close(result, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates cosine similarity of parallel vectors")
val result = m{ frac(dot([1, 2, 3], [2, 4, 6]), sqrt(dot([1, 2, 3], [1, 2, 3])) * sqrt(dot([2, 4, 6], [2, 4, 6]))) }
expect(close(result, 1.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates cosine similarity of parallel vectors")<br>
> val result = $\frac{\operatorname{dot}(?, 2, 3, ?, 4, 6)}{\sqrt{\operatorname{dot}(?, 2, 3, ?, 2, 3)} \cdot \sqrt{\operatorname{dot}(?, 4, 6, ?, 4, 6)}}$<br>
> expect(close(result, 1.0, 0.01)).to_equal(true)

</details>

</details>

#### renders cosine similarity LaTeX

- renders cosine similarity LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders cosine similarity LaTeX")
val latex = render_latex_raw("frac(dot(a, b), sqrt(dot(a, a)) * sqrt(dot(b, b)))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain(r"\operatorname{dot}")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders cosine similarity Unicode

- renders cosine similarity Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders cosine similarity Unicode")
val pretty = to_pretty("frac(dot(a, b), sqrt(dot(a, a)) * sqrt(dot(b, b)))")
expect(pretty).to_contain("dot")
```

</details>

#### Accuracy approx: frac(1, 1 + (pred - target)^2)

#### evaluates accuracy at exact match

- evaluates accuracy at exact match
   - Expected: close(result, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates accuracy at exact match")
val pred = 5.0
val target = 5.0
val result = m{ frac(1, 1 + (pred - target)^2) }
expect(close(result, 1.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates accuracy at exact match")<br>
> val pred = 5.0<br>
> val target = 5.0<br>
> val result = $\frac{1}{1 + (pred - target)^{2}}$<br>
> expect(close(result, 1.0, 0.01)).to_equal(true)

</details>

</details>

#### evaluates accuracy with distance

- evaluates accuracy with distance
   - Expected: close(result, 0.5, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates accuracy with distance")
val pred = 5.0
val target = 6.0
val result = m{ frac(1, 1 + (pred - target)^2) }
expect(close(result, 0.5, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates accuracy with distance")<br>
> val pred = 5.0<br>
> val target = 6.0<br>
> val result = $\frac{1}{1 + (pred - target)^{2}}$<br>
> expect(close(result, 0.5, 0.01)).to_equal(true)

</details>

</details>

#### renders accuracy LaTeX

- renders accuracy LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders accuracy LaTeX")
val latex = render_latex_raw("frac(1, 1 + (pred - target)^2)")
expect(latex).to_contain("\\frac")
```

</details>

#### renders accuracy Unicode

- renders accuracy Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders accuracy Unicode")
val pretty = to_pretty("frac(1, 1 + (pred - target)^2)")
expect(pretty).to_contain("pred")
```

</details>

#### Xavier Init: sqrt(frac(6, fan_in + fan_out))

#### evaluates xavier init

- evaluates xavier init
   - Expected: close(result, 0.1250, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates xavier init")
val fan_in = 256.0
val fan_out = 128.0
val result = m{ sqrt(frac(6, fan_in + fan_out)) }
expect(close(result, 0.1250, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates xavier init")<br>
> val fan_in = 256.0<br>
> val fan_out = 128.0<br>
> val result = $\sqrt{\frac{6}{fan_in + fan_out}}$<br>
> expect(close(result, 0.1250, 0.01)).to_equal(true)

</details>

</details>

#### renders xavier LaTeX

- renders xavier LaTeX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders xavier LaTeX")
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders xavier Unicode

- renders xavier Unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders xavier Unicode")
val pretty = to_pretty("sqrt(frac(6, fan_in + fan_out))")
expect(pretty).to_contain("√")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 72 |
| Active scenarios | 72 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd0bd749bcfa96786304c3c253efee4cbc2bfe41f670aaf04dd6753838610c41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd0bd749bcfa96786304c3c253efee4cbc2bfe41f670aaf04dd6753838610c41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd0bd749bcfa96786304c3c253efee4cbc2bfe41f670aaf04dd6753838610c41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/feature/usage/math_dl_equations_spec.spl
mirror: doc/06_spec/feature/usage/math_dl_equations_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/math_dl_equations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/math_dl_equations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/math_dl_equations_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/math_dl_equations_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates sigmoid(2) correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/math_dl_equations_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders sigmoid LaTeX' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/math_dl_equations_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders sigmoid Unicode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
