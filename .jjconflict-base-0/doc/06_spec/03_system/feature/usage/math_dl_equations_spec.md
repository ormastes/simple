# Deep Learning Equation Tests for m{} Math Blocks

> Tests that composite DL equations parse, evaluate correctly, render to LaTeX, and render to nvim-friendly Unicode. Covers all 27 DL equations found in `examples/07_ml/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

<!-- sdn-diagram:id=math_dl_equations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_dl_equations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_dl_equations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_dl_equations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 72 | 72 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deep Learning Equation Tests for m{} Math Blocks

Tests that composite DL equations parse, evaluate correctly, render to LaTeX, and render to nvim-friendly Unicode. Covers all 27 DL equations found in `examples/07_ml/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (DL equation coverage) |
| Category | Syntax / Math DSL |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/math_dl_equations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that composite DL equations parse, evaluate correctly, render to LaTeX,
and render to nvim-friendly Unicode. Covers all 27 DL equations found in
`examples/07_ml/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

## Scenarios

### DL Activations

#### Sigmoid: frac(1, 1 + exp(-x))

#### evaluates sigmoid(2) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2.0
val result = m{ frac(1, 1 + exp(-x)) }
expect(close(result, 0.8808, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 2.0<br>
> val result = $\frac{1}{1 + \exp(-x)}$<br>
> expect(close(result, 0.8808, 0.01)).to_equal(true)

</details>

</details>

#### renders sigmoid LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders sigmoid Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(1, 1 + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

#### Tanh: frac(exp(x) - exp(-x), exp(x) + exp(-x))

#### evaluates tanh(1) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
val result = m{ frac(exp(x) - exp(-x), exp(x) + exp(-x)) }
expect(close(result, 0.7616, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 1.0<br>
> val result = $\frac{\exp(x) - \exp(-x)}{\exp(x) + \exp(-x)}$<br>
> expect(close(result, 0.7616, 0.01)).to_equal(true)

</details>

</details>

#### renders tanh LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(exp(x) - exp(-x), exp(x) + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders tanh Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(exp(x) - exp(-x), exp(x) + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

#### ReLU: max(0, x)

#### evaluates relu(3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.0
val result = m{ max(0, x) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 3.0<br>
> val result = $\max(0)$<br>
> expect(result).to_equal(3.0)

</details>

</details>

#### evaluates relu(-2) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -2.0
val result = m{ max(0, x) }
expect(result).to_equal(0.0)
```

<details>
<summary>Rendered scenario source</summary>

> val x = -2.0<br>
> val result = $\max(0)$<br>
> expect(result).to_equal(0.0)

</details>

</details>

#### renders relu LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("max(0, x)")
expect(latex).to_contain("\\max")
```

</details>

#### renders relu Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("max(0, x)")
expect(pretty).to_contain("max")
```

</details>

#### GELU: x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))

#### evaluates gelu(1) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
val result = m{ x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3))) }
expect(close(result, 0.8412, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 1.0<br>
> val result = $x \cdot 0.5 \cdot (1 + \tanh(\sqrt{\frac{2}{\pi}} \cdot (x + 0.044715 \cdot x^{3})))$<br>
> expect(close(result, 0.8412, 0.01)).to_equal(true)

</details>

</details>

#### renders gelu LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))")
expect(latex).to_contain("\\tanh")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders gelu Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("x * 0.5 * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))")
expect(pretty).to_contain("π")
```

</details>

#### Softmax denominator: exp(x) / sum(exp(x))

#### evaluates softmax component

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2.0
val result = m{ exp(x) }
expect(close(result, 7.389, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 2.0<br>
> val result = $\exp(x)$<br>
> expect(close(result, 7.389, 0.01)).to_equal(true)

</details>

</details>

#### renders softmax LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("exp(x - max(x)) / sum(exp(x - max(x)))")
expect(latex).to_contain("\\exp")
expect(latex).to_contain("\\max")
```

</details>

#### renders softmax Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("exp(x - max(x)) / sum(exp(x - max(x)))")
expect(pretty).to_contain("exp")
expect(pretty).to_contain("max")
```

</details>

### DL Normalization

#### Layer Norm: frac(x - mu, sqrt(sigma^2 + epsilon)) * gamma + beta

#### evaluates layer norm with concrete values

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("x * w / sqrt(mean(x^2) + epsilon)")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\epsilon")
```

</details>

#### renders rms norm Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("x * w / sqrt(mean(x^2) + epsilon)")
expect(pretty).to_contain("ε")
```

</details>

#### Dropout scaling: frac(x, 1 - p)

#### evaluates dropout scaling

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10.0
val p = 0.5
val result = m{ frac(x, 1 - p) }
expect(close(result, 20.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 10.0<br>
> val p = 0.5<br>
> val result = $\frac{x}{1 - p}$<br>
> expect(close(result, 20.0, 0.01)).to_equal(true)

</details>

</details>

#### renders dropout LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(x, 1 - p)")
expect(latex).to_contain("\\frac")
```

</details>

#### renders dropout Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(x, 1 - p)")
expect(pretty).to_contain("x")
```

</details>

### DL Layers

#### Linear: matmul(x, transpose(W)) + b

#### renders linear LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("matmul(x, transpose(W)) + b")
expect(latex).to_contain(r"\operatorname{matmul}")
expect(latex).to_contain(r"\operatorname{transpose}")
```

</details>

#### renders linear Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("matmul(x, transpose(W)) + b")
expect(pretty).to_contain("matmul")
expect(pretty).to_contain("transpose")
```

</details>

#### Embedding: W[token_id]

#### renders embedding LaTeX with subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("W[token_id]")
expect(latex).to_contain("W")
expect(latex).to_contain("token")
```

</details>

#### renders embedding Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("W[token_id]")
expect(pretty).to_contain("W")
```

</details>

#### FFN: matmul(relu(matmul(x, W1) + b1), W2) + b2

#### renders FFN LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("matmul(relu(matmul(x, W1) + b1), W2) + b2")
expect(latex).to_contain(r"\operatorname{matmul}")
expect(latex).to_contain(r"\operatorname{relu}")
```

</details>

#### renders FFN Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("matmul(relu(matmul(x, W1) + b1), W2) + b2")
expect(pretty).to_contain("matmul")
expect(pretty).to_contain("relu")
```

</details>

### DL Attention & Architecture

#### Scaled Dot-Product Attention: softmax(frac(matmul(Q, K'), sqrt(d_k))) * V

#### renders attention LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("softmax(frac(matmul(Q, K'), sqrt(d_k))) * V")
expect(latex).to_contain(r"\operatorname{softmax}")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders attention Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("softmax(frac(matmul(Q, K'), sqrt(d_k))) * V")
expect(pretty).to_contain("softmax")
```

</details>

#### Multi-Head Attention: matmul(concat_heads, W_o)

#### renders MHA LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("matmul(concat_heads, W_o)")
expect(latex).to_contain(r"\operatorname{matmul}")
```

</details>

#### renders MHA Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("matmul(concat_heads, W_o)")
expect(pretty).to_contain("matmul")
```

</details>

#### Transformer Block: x + sublayer(layernorm(x))

#### renders transformer block LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("x + sublayer(layernorm(x))")
expect(latex).to_contain(r"\operatorname{sublayer}")
expect(latex).to_contain(r"\operatorname{layernorm}")
```

</details>

#### renders transformer block Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("x + sublayer(layernorm(x))")
expect(pretty).to_contain("sublayer")
expect(pretty).to_contain("layernorm")
```

</details>

#### Positional Encoding: sin(frac(pos, 10000^(frac(2 * i, d))))

#### renders positional encoding LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sin(frac(pos, 10000^(frac(2 * i, d))))")
expect(latex).to_contain("\\sin")
expect(latex).to_contain("\\frac")
```

</details>

#### renders positional encoding Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("sin(frac(pos, 10000^(frac(2 * i, d))))")
expect(pretty).to_contain("sin")
```

</details>

### DL Loss Functions

#### Cross-Entropy: frac(-1, N) * sum(i, 1..N) log(p[i])

#### renders cross-entropy LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(-1, N) * sum(i, 1..N) log(p[i])")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sum_{")
expect(latex).to_contain("\\log")
```

</details>

#### renders cross-entropy Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(-1, N) * sum(i, 1..N) log(p[i])")
expect(pretty).to_contain("log")
```

</details>

#### MSE: frac(1, N) * sum(i, 1..N) (y[i] - yhat[i])^2

#### renders MSE LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, N) * sum(i, 1..N) (y[i] - yhat[i])^2")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sum_{")
```

</details>

#### renders MSE Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(1, N) * sum(i, 1..N) (y[i] - yhat[i])^2")
expect(pretty).to_contain("N")
```

</details>

#### Temperature scaling: frac(logits, T)

#### evaluates temperature scaling

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logits = 6.0
val T = 2.0
val result = m{ frac(logits, T) }
expect(close(result, 3.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val logits = 6.0<br>
> val T = 2.0<br>
> val result = $\frac{logits}{T}$<br>
> expect(close(result, 3.0, 0.01)).to_equal(true)

</details>

</details>

#### renders temperature LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(logits, T)")
expect(latex).to_contain("\\frac")
```

</details>

#### renders temperature Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(logits, T)")
expect(pretty).to_contain("logits")
```

</details>

### DL Optimizers

#### SGD: theta - alpha * grad

#### evaluates SGD update

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val theta = 5.0
val alpha = 0.1
val grad = 2.0
val result = m{ theta - alpha * grad }
expect(close(result, 4.8, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val theta = 5.0<br>
> val alpha = 0.1<br>
> val grad = 2.0<br>
> val result = $\theta - \alpha \cdot grad$<br>
> expect(close(result, 4.8, 0.01)).to_equal(true)

</details>

</details>

#### renders SGD LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("theta - alpha * grad")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
```

</details>

#### renders SGD Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("theta - alpha * grad")
expect(pretty).to_contain("θ")
expect(pretty).to_contain("α")
```

</details>

#### SGD+Momentum: theta - alpha * (mu * v + grad)

#### evaluates SGD+momentum update

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("theta - alpha * (mu * v + grad)")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\mu")
```

</details>

#### renders SGD+momentum Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("theta - alpha * (mu * v + grad)")
expect(pretty).to_contain("θ")
expect(pretty).to_contain("α")
expect(pretty).to_contain("μ")
```

</details>

#### Adam bias correction: frac(m, 1 - beta^t)

#### evaluates adam bias correction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = 3.0
val beta = 0.9
val result = m{ frac(1, 1 - beta^t) }
expect(close(result, 3.69, 0.1)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val t = 3.0<br>
> val beta = 0.9<br>
> val result = $\frac{1}{1 - \beta^{t}}$<br>
> expect(close(result, 3.69, 0.1)).to_equal(true)

</details>

</details>

#### renders adam LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(m, 1 - beta^t)")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\beta")
```

</details>

#### renders adam Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(m, 1 - beta^t)")
expect(pretty).to_contain("β")
```

</details>

#### Gradient clip: frac(c, sqrt(dot(g, g)))

#### renders gradient clip LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(c, sqrt(dot(g, g)))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain(r"\operatorname{dot}")
```

</details>

#### renders gradient clip Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(c, sqrt(dot(g, g)))")
expect(pretty).to_contain("dot")
```

</details>

### DL Learning Rate

#### Linear Warmup: alpha * frac(step, warmup)

#### evaluates linear warmup

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alpha = 0.001
val step = 500.0
val warmup = 1000.0
val result = m{ alpha * frac(step, warmup) }
expect(close(result, 0.0005, 0.0001)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val alpha = 0.001<br>
> val step = 500.0<br>
> val warmup = 1000.0<br>
> val result = $\alpha \cdot \frac{step}{warmup}$<br>
> expect(close(result, 0.0005, 0.0001)).to_equal(true)

</details>

</details>

#### renders warmup LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("alpha * frac(step, warmup)")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\frac")
```

</details>

#### renders warmup Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("alpha * frac(step, warmup)")
expect(pretty).to_contain("α")
```

</details>

#### Cosine Decay: min_lr + (alpha - min_lr) * (1 - progress)

#### evaluates cosine decay at midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val min_lr = 0.0001
val alpha = 0.001
val progress = 0.5
val result = m{ min_lr + (alpha - min_lr) * (1 - progress) }
expect(close(result, 0.00055, 0.0001)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val min_lr = 0.0001<br>
> val alpha = 0.001<br>
> val progress = 0.5<br>
> val result = $min_lr + (\alpha - min_lr) \cdot (1 - progress)$<br>
> expect(close(result, 0.00055, 0.0001)).to_equal(true)

</details>

</details>

#### renders cosine decay LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("min_lr + (alpha - min_lr) * (1 - progress)")
expect(latex).to_contain("\\alpha")
```

</details>

#### renders cosine decay Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("min_lr + (alpha - min_lr) * (1 - progress)")
expect(pretty).to_contain("α")
```

</details>

### DL Metrics & Init

#### Cosine Similarity: frac(dot(a, b), sqrt(dot(a, a)) * sqrt(dot(b, b)))

#### evaluates cosine similarity of parallel vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ frac(dot([1, 2, 3], [2, 4, 6]), sqrt(dot([1, 2, 3], [1, 2, 3])) * sqrt(dot([2, 4, 6], [2, 4, 6]))) }
expect(close(result, 1.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\frac{\operatorname{dot}([, 2, 3, [, 4, 6)}{\sqrt{\operatorname{dot}([, 2, 3, [, 2, 3)} \cdot \sqrt{\operatorname{dot}([, 4, 6, [, 4, 6)}}$<br>
> expect(close(result, 1.0, 0.01)).to_equal(true)

</details>

</details>

#### renders cosine similarity LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(dot(a, b), sqrt(dot(a, a)) * sqrt(dot(b, b)))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain(r"\operatorname{dot}")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders cosine similarity Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(dot(a, b), sqrt(dot(a, a)) * sqrt(dot(b, b)))")
expect(pretty).to_contain("dot")
```

</details>

#### Accuracy approx: frac(1, 1 + (pred - target)^2)

#### evaluates accuracy at exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = 5.0
val target = 5.0
val result = m{ frac(1, 1 + (pred - target)^2) }
expect(close(result, 1.0, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val pred = 5.0<br>
> val target = 5.0<br>
> val result = $\frac{1}{1 + (pred - target)^{2}}$<br>
> expect(close(result, 1.0, 0.01)).to_equal(true)

</details>

</details>

#### evaluates accuracy with distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = 5.0
val target = 6.0
val result = m{ frac(1, 1 + (pred - target)^2) }
expect(close(result, 0.5, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val pred = 5.0<br>
> val target = 6.0<br>
> val result = $\frac{1}{1 + (pred - target)^{2}}$<br>
> expect(close(result, 0.5, 0.01)).to_equal(true)

</details>

</details>

#### renders accuracy LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, 1 + (pred - target)^2)")
expect(latex).to_contain("\\frac")
```

</details>

#### renders accuracy Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(1, 1 + (pred - target)^2)")
expect(pretty).to_contain("pred")
```

</details>

#### Xavier Init: sqrt(frac(6, fan_in + fan_out))

#### evaluates xavier init

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fan_in = 256.0
val fan_out = 128.0
val result = m{ sqrt(frac(6, fan_in + fan_out)) }
expect(close(result, 0.1250, 0.01)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val fan_in = 256.0<br>
> val fan_out = 128.0<br>
> val result = $\sqrt{\frac{6}{fan_in + fan_out}}$<br>
> expect(close(result, 0.1250, 0.01)).to_equal(true)

</details>

</details>

#### renders xavier LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders xavier Unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
