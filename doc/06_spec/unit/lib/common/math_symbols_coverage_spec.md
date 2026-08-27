# Unicode Math Symbols & Operators Coverage Specification

> Branch coverage tests for `std.unicode_math` symbol/operator lookup functions and box-drawing/bracket pieces. Split from math_coverage_spec.spl for memory.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 112 | 112 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unicode Math Symbols & Operators Coverage Specification

Branch coverage tests for `std.unicode_math` symbol/operator lookup functions and box-drawing/bracket pieces. Split from math_coverage_spec.spl for memory.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-MATH-COV |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/lib/common/math_symbols_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch coverage tests for `std.unicode_math` symbol/operator lookup functions
and box-drawing/bracket pieces. Split from math_coverage_spec.spl for memory.

## Key Concepts

| Concept | Description |
|---------|-------------|
| math_sym | Symbol lookup: calculus, roots, constants, quantifiers, logic, sets, misc |
| math_op | Operator lookup: comparison, arithmetic, arrows |
| brackets | Box-drawing pieces for matrices |

## Scenarios

### unicode_math math_sym

#### calculus symbols

#### returns sum

- returns sum
   - Expected: math_sym("sum") equals `\u2211`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sum")
expect(math_sym("sum")).to_equal("\u2211")
```

</details>

#### returns product

- returns product
   - Expected: math_sym("product") equals `\u220F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns product")
expect(math_sym("product")).to_equal("\u220F")
```

</details>

#### returns coproduct

- returns coproduct
   - Expected: math_sym("coproduct") equals `\u2210`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns coproduct")
expect(math_sym("coproduct")).to_equal("\u2210")
```

</details>

#### returns integral

- returns integral
   - Expected: math_sym("integral") equals `\u222B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns integral")
expect(math_sym("integral")).to_equal("\u222B")
```

</details>

#### returns double_integral

- returns double_integral
   - Expected: math_sym("double_integral") equals `\u222C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns double_integral")
expect(math_sym("double_integral")).to_equal("\u222C")
```

</details>

#### returns triple_integral

- returns triple_integral
   - Expected: math_sym("triple_integral") equals `\u222D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns triple_integral")
expect(math_sym("triple_integral")).to_equal("\u222D")
```

</details>

#### returns contour_integral

- returns contour_integral
   - Expected: math_sym("contour_integral") equals `\u222E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns contour_integral")
expect(math_sym("contour_integral")).to_equal("\u222E")
```

</details>

#### returns surface_integral

- returns surface_integral
   - Expected: math_sym("surface_integral") equals `\u222F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns surface_integral")
expect(math_sym("surface_integral")).to_equal("\u222F")
```

</details>

#### returns volume_integral

- returns volume_integral
   - Expected: math_sym("volume_integral") equals `\u2230`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns volume_integral")
expect(math_sym("volume_integral")).to_equal("\u2230")
```

</details>

#### root symbols

#### returns sqrt

- returns sqrt
   - Expected: math_sym("sqrt") equals `\u221A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sqrt")
expect(math_sym("sqrt")).to_equal("\u221A")
```

</details>

#### returns cbrt

- returns cbrt
   - Expected: math_sym("cbrt") equals `\u221B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cbrt")
expect(math_sym("cbrt")).to_equal("\u221B")
```

</details>

#### returns fourthrt

- returns fourthrt
   - Expected: math_sym("fourthrt") equals `\u221C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns fourthrt")
expect(math_sym("fourthrt")).to_equal("\u221C")
```

</details>

#### constants

#### returns infinity

- returns infinity
   - Expected: math_sym("infinity") equals `\u221E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns infinity")
expect(math_sym("infinity")).to_equal("\u221E")
```

</details>

#### returns pi_sym

- returns pi_sym
   - Expected: math_sym("pi_sym") equals `\u03C0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pi_sym")
expect(math_sym("pi_sym")).to_equal("\u03C0")
```

</details>

#### returns euler

- returns euler
   - Expected: math_sym("euler") equals `\u212F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns euler")
expect(math_sym("euler")).to_equal("\u212F")
```

</details>

#### returns imaginary

- returns imaginary
   - Expected: math_sym("imaginary") equals `\u2111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns imaginary")
expect(math_sym("imaginary")).to_equal("\u2111")
```

</details>

#### returns real_part

- returns real_part
   - Expected: math_sym("real_part") equals `\u211C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns real_part")
expect(math_sym("real_part")).to_equal("\u211C")
```

</details>

#### returns planck

- returns planck
   - Expected: math_sym("planck") equals `\u210F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns planck")
expect(math_sym("planck")).to_equal("\u210F")
```

</details>

#### returns aleph

- returns aleph
   - Expected: math_sym("aleph") equals `\u2135`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns aleph")
expect(math_sym("aleph")).to_equal("\u2135")
```

</details>

#### quantifiers

#### returns forall

- returns forall
   - Expected: math_sym("forall") equals `\u2200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns forall")
expect(math_sym("forall")).to_equal("\u2200")
```

</details>

#### returns exists

- returns exists
   - Expected: math_sym("exists") equals `\u2203`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exists")
expect(math_sym("exists")).to_equal("\u2203")
```

</details>

#### returns nexists

- returns nexists
   - Expected: math_sym("nexists") equals `\u2204`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nexists")
expect(math_sym("nexists")).to_equal("\u2204")
```

</details>

#### logic symbols

#### returns and

- returns and
   - Expected: math_sym("and") equals `\u2227`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns and")
expect(math_sym("and")).to_equal("\u2227")
```

</details>

#### returns or

- returns or
   - Expected: math_sym("or") equals `\u2228`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns or")
expect(math_sym("or")).to_equal("\u2228")
```

</details>

#### returns not

- returns not
   - Expected: math_sym("not") equals `\u00AC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns not")
expect(math_sym("not")).to_equal("\u00AC")
```

</details>

#### returns top

- returns top
   - Expected: math_sym("top") equals `\u22A4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns top")
expect(math_sym("top")).to_equal("\u22A4")
```

</details>

#### returns bot

- returns bot
   - Expected: math_sym("bot") equals `\u22A5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bot")
expect(math_sym("bot")).to_equal("\u22A5")
```

</details>

#### returns proves

- returns proves
   - Expected: math_sym("proves") equals `\u22A2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns proves")
expect(math_sym("proves")).to_equal("\u22A2")
```

</details>

#### returns models

- returns models
   - Expected: math_sym("models") equals `\u22A8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns models")
expect(math_sym("models")).to_equal("\u22A8")
```

</details>

#### returns therefore

- returns therefore
   - Expected: math_sym("therefore") equals `\u2234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns therefore")
expect(math_sym("therefore")).to_equal("\u2234")
```

</details>

#### returns because

- returns because
   - Expected: math_sym("because") equals `\u2235`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns because")
expect(math_sym("because")).to_equal("\u2235")
```

</details>

#### set symbols

#### returns in

- returns in
   - Expected: math_sym("in") equals `\u2208`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns in")
expect(math_sym("in")).to_equal("\u2208")
```

</details>

#### returns notin

- returns notin
   - Expected: math_sym("notin") equals `\u2209`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns notin")
expect(math_sym("notin")).to_equal("\u2209")
```

</details>

#### returns subset

- returns subset
   - Expected: math_sym("subset") equals `\u2282`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns subset")
expect(math_sym("subset")).to_equal("\u2282")
```

</details>

#### returns superset

- returns superset
   - Expected: math_sym("superset") equals `\u2283`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns superset")
expect(math_sym("superset")).to_equal("\u2283")
```

</details>

#### returns subseteq

- returns subseteq
   - Expected: math_sym("subseteq") equals `\u2286`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns subseteq")
expect(math_sym("subseteq")).to_equal("\u2286")
```

</details>

#### returns supseteq

- returns supseteq
   - Expected: math_sym("supseteq") equals `\u2287`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns supseteq")
expect(math_sym("supseteq")).to_equal("\u2287")
```

</details>

#### returns union

- returns union
   - Expected: math_sym("union") equals `\u222A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns union")
expect(math_sym("union")).to_equal("\u222A")
```

</details>

#### returns intersection

- returns intersection
   - Expected: math_sym("intersection") equals `\u2229`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns intersection")
expect(math_sym("intersection")).to_equal("\u2229")
```

</details>

#### returns emptyset

- returns emptyset
   - Expected: math_sym("emptyset") equals `\u2205`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns emptyset")
expect(math_sym("emptyset")).to_equal("\u2205")
```

</details>

#### returns setminus

- returns setminus
   - Expected: math_sym("setminus") equals `\u2216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns setminus")
expect(math_sym("setminus")).to_equal("\u2216")
```

</details>

#### number set symbols

#### returns naturals

- returns naturals
   - Expected: math_sym("naturals") equals `\u2115`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns naturals")
expect(math_sym("naturals")).to_equal("\u2115")
```

</details>

#### returns integers

- returns integers
   - Expected: math_sym("integers") equals `\u2124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns integers")
expect(math_sym("integers")).to_equal("\u2124")
```

</details>

#### returns rationals

- returns rationals
   - Expected: math_sym("rationals") equals `\u211A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns rationals")
expect(math_sym("rationals")).to_equal("\u211A")
```

</details>

#### returns reals

- returns reals
   - Expected: math_sym("reals") equals `\u211D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns reals")
expect(math_sym("reals")).to_equal("\u211D")
```

</details>

#### returns complex

- returns complex
   - Expected: math_sym("complex") equals `\u2102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns complex")
expect(math_sym("complex")).to_equal("\u2102")
```

</details>

#### returns primes

- returns primes
   - Expected: math_sym("primes") equals `\u2119`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns primes")
expect(math_sym("primes")).to_equal("\u2119")
```

</details>

#### miscellaneous symbols

#### returns degree

- returns degree
   - Expected: math_sym("degree") equals `\u00B0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns degree")
expect(math_sym("degree")).to_equal("\u00B0")
```

</details>

#### returns prime

- returns prime
   - Expected: math_sym("prime") equals `\u2032`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns prime")
expect(math_sym("prime")).to_equal("\u2032")
```

</details>

#### returns double_prime

- returns double_prime
   - Expected: math_sym("double_prime") equals `\u2033`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns double_prime")
expect(math_sym("double_prime")).to_equal("\u2033")
```

</details>

#### returns triple_prime

- returns triple_prime
   - Expected: math_sym("triple_prime") equals `\u2034`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns triple_prime")
expect(math_sym("triple_prime")).to_equal("\u2034")
```

</details>

#### returns ellipsis

- returns ellipsis
   - Expected: math_sym("ellipsis") equals `\u2026`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ellipsis")
expect(math_sym("ellipsis")).to_equal("\u2026")
```

</details>

#### returns vellipsis

- returns vellipsis
   - Expected: math_sym("vellipsis") equals `\u22EE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns vellipsis")
expect(math_sym("vellipsis")).to_equal("\u22EE")
```

</details>

#### returns hellipsis

- returns hellipsis
   - Expected: math_sym("hellipsis") equals `\u22EF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns hellipsis")
expect(math_sym("hellipsis")).to_equal("\u22EF")
```

</details>

#### returns dellipsis

- returns dellipsis
   - Expected: math_sym("dellipsis") equals `\u22F1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns dellipsis")
expect(math_sym("dellipsis")).to_equal("\u22F1")
```

</details>

#### returns compose

- returns compose
   - Expected: math_sym("compose") equals `\u2218`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns compose")
expect(math_sym("compose")).to_equal("\u2218")
```

</details>

#### returns tensor

- returns tensor
   - Expected: math_sym("tensor") equals `\u2297`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns tensor")
expect(math_sym("tensor")).to_equal("\u2297")
```

</details>

#### returns direct_sum

- returns direct_sum
   - Expected: math_sym("direct_sum") equals `\u2295`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns direct_sum")
expect(math_sym("direct_sum")).to_equal("\u2295")
```

</details>

#### returns dot_product

- returns dot_product
   - Expected: math_sym("dot_product") equals `\u2299`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns dot_product")
expect(math_sym("dot_product")).to_equal("\u2299")
```

</details>

#### fallback for unknown symbols

#### returns unknown name unchanged

- returns unknown name unchanged
   - Expected: math_sym("unknown_sym") equals `unknown_sym`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown name unchanged")
expect(math_sym("unknown_sym")).to_equal("unknown_sym")
```

</details>

### unicode_math math_op

#### comparison operators

#### returns leq

- returns leq
   - Expected: math_op("leq") equals `\u2264`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns leq")
expect(math_op("leq")).to_equal("\u2264")
```

</details>

#### returns geq

- returns geq
   - Expected: math_op("geq") equals `\u2265`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns geq")
expect(math_op("geq")).to_equal("\u2265")
```

</details>

#### returns neq

- returns neq
   - Expected: math_op("neq") equals `\u2260`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns neq")
expect(math_op("neq")).to_equal("\u2260")
```

</details>

#### returns approx

- returns approx
   - Expected: math_op("approx") equals `\u2248`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns approx")
expect(math_op("approx")).to_equal("\u2248")
```

</details>

#### returns equiv

- returns equiv
   - Expected: math_op("equiv") equals `\u2261`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns equiv")
expect(math_op("equiv")).to_equal("\u2261")
```

</details>

#### returns nequiv

- returns nequiv
   - Expected: math_op("nequiv") equals `\u2262`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nequiv")
expect(math_op("nequiv")).to_equal("\u2262")
```

</details>

#### returns cong

- returns cong
   - Expected: math_op("cong") equals `\u2245`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cong")
expect(math_op("cong")).to_equal("\u2245")
```

</details>

#### returns sim

- returns sim
   - Expected: math_op("sim") equals `\u223C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sim")
expect(math_op("sim")).to_equal("\u223C")
```

</details>

#### returns ll

- returns ll
   - Expected: math_op("ll") equals `\u226A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ll")
expect(math_op("ll")).to_equal("\u226A")
```

</details>

#### returns gg

- returns gg
   - Expected: math_op("gg") equals `\u226B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns gg")
expect(math_op("gg")).to_equal("\u226B")
```

</details>

#### returns propto

- returns propto
   - Expected: math_op("propto") equals `\u221D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns propto")
expect(math_op("propto")).to_equal("\u221D")
```

</details>

#### returns defeq

- returns defeq
   - Expected: math_op("defeq") equals `\u2254`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns defeq")
expect(math_op("defeq")).to_equal("\u2254")
```

</details>

#### arithmetic operators

#### returns pm

- returns pm
   - Expected: math_op("pm") equals `\u00B1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pm")
expect(math_op("pm")).to_equal("\u00B1")
```

</details>

#### returns mp

- returns mp
   - Expected: math_op("mp") equals `\u2213`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns mp")
expect(math_op("mp")).to_equal("\u2213")
```

</details>

#### returns times

- returns times
   - Expected: math_op("times") equals `\u00D7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns times")
expect(math_op("times")).to_equal("\u00D7")
```

</details>

#### returns div

- returns div
   - Expected: math_op("div") equals `\u00F7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns div")
expect(math_op("div")).to_equal("\u00F7")
```

</details>

#### returns cdot

- returns cdot
   - Expected: math_op("cdot") equals `\u00B7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cdot")
expect(math_op("cdot")).to_equal("\u00B7")
```

</details>

#### returns star

- returns star
   - Expected: math_op("star") equals `\u2217`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns star")
expect(math_op("star")).to_equal("\u2217")
```

</details>

#### arrow operators

#### returns to

- returns to
   - Expected: math_op("to") equals `\u2192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns to")
expect(math_op("to")).to_equal("\u2192")
```

</details>

#### returns from

- returns from
   - Expected: math_op("from") equals `\u2190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns from")
expect(math_op("from")).to_equal("\u2190")
```

</details>

#### returns lr

- returns lr
   - Expected: math_op("lr") equals `\u2194`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns lr")
expect(math_op("lr")).to_equal("\u2194")
```

</details>

#### returns implies

- returns implies
   - Expected: math_op("implies") equals `\u21D2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns implies")
expect(math_op("implies")).to_equal("\u21D2")
```

</details>

#### returns implied_by

- returns implied_by
   - Expected: math_op("implied_by") equals `\u21D0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns implied_by")
expect(math_op("implied_by")).to_equal("\u21D0")
```

</details>

#### returns iff

- returns iff
   - Expected: math_op("iff") equals `\u21D4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns iff")
expect(math_op("iff")).to_equal("\u21D4")
```

</details>

#### returns mapsto

- returns mapsto
   - Expected: math_op("mapsto") equals `\u21A6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns mapsto")
expect(math_op("mapsto")).to_equal("\u21A6")
```

</details>

#### returns long_to

- returns long_to
   - Expected: math_op("long_to") equals `\u27F6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns long_to")
expect(math_op("long_to")).to_equal("\u27F6")
```

</details>

#### returns long_implies

- returns long_implies
   - Expected: math_op("long_implies") equals `\u27F9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns long_implies")
expect(math_op("long_implies")).to_equal("\u27F9")
```

</details>

#### returns long_iff

- returns long_iff
   - Expected: math_op("long_iff") equals `\u27FA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns long_iff")
expect(math_op("long_iff")).to_equal("\u27FA")
```

</details>

#### returns surjection

- returns surjection
   - Expected: math_op("surjection") equals `\u21A0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns surjection")
expect(math_op("surjection")).to_equal("\u21A0")
```

</details>

#### returns injection

- returns injection
   - Expected: math_op("injection") equals `\u21A3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns injection")
expect(math_op("injection")).to_equal("\u21A3")
```

</details>

#### fallback for unknown operators

#### returns unknown name unchanged

- returns unknown name unchanged
   - Expected: math_op("unknown_op") equals `unknown_op`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown name unchanged")
expect(math_op("unknown_op")).to_equal("unknown_op")
```

</details>

### unicode_math brackets and lines

#### hline

#### creates line of width 3

- creates line of width 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates line of width 3")
val line = hline(3)
expect(line.len()).to_be_greater_than(0)
```

</details>

#### creates line of width 0

- creates line of width 0
   - Expected: hline(0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates line of width 0")
expect(hline(0)).to_equal("")
```

</details>

#### square bracket pieces

#### returns left top bracket

- returns left top bracket
   - Expected: bracket_left_top() equals `\u23A1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left top bracket")
expect(bracket_left_top()).to_equal("\u23A1")
```

</details>

#### returns left mid bracket

- returns left mid bracket
   - Expected: bracket_left_mid() equals `\u23A2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left mid bracket")
expect(bracket_left_mid()).to_equal("\u23A2")
```

</details>

#### returns left bot bracket

- returns left bot bracket
   - Expected: bracket_left_bot() equals `\u23A3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left bot bracket")
expect(bracket_left_bot()).to_equal("\u23A3")
```

</details>

#### returns right top bracket

- returns right top bracket
   - Expected: bracket_right_top() equals `\u23A4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right top bracket")
expect(bracket_right_top()).to_equal("\u23A4")
```

</details>

#### returns right mid bracket

- returns right mid bracket
   - Expected: bracket_right_mid() equals `\u23A5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right mid bracket")
expect(bracket_right_mid()).to_equal("\u23A5")
```

</details>

#### returns right bot bracket

- returns right bot bracket
   - Expected: bracket_right_bot() equals `\u23A6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right bot bracket")
expect(bracket_right_bot()).to_equal("\u23A6")
```

</details>

#### parenthesis pieces

#### returns left top paren

- returns left top paren
   - Expected: paren_left_top() equals `\u239B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left top paren")
expect(paren_left_top()).to_equal("\u239B")
```

</details>

#### returns left mid paren

- returns left mid paren
   - Expected: paren_left_mid() equals `\u239C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left mid paren")
expect(paren_left_mid()).to_equal("\u239C")
```

</details>

#### returns left bot paren

- returns left bot paren
   - Expected: paren_left_bot() equals `\u239D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left bot paren")
expect(paren_left_bot()).to_equal("\u239D")
```

</details>

#### returns right top paren

- returns right top paren
   - Expected: paren_right_top() equals `\u239E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right top paren")
expect(paren_right_top()).to_equal("\u239E")
```

</details>

#### returns right mid paren

- returns right mid paren
   - Expected: paren_right_mid() equals `\u239F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right mid paren")
expect(paren_right_mid()).to_equal("\u239F")
```

</details>

#### returns right bot paren

- returns right bot paren
   - Expected: paren_right_bot() equals `\u23A0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right bot paren")
expect(paren_right_bot()).to_equal("\u23A0")
```

</details>

#### brace pieces

#### returns left top brace

- returns left top brace
   - Expected: brace_left_top() equals `\u23A7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left top brace")
expect(brace_left_top()).to_equal("\u23A7")
```

</details>

#### returns left mid brace

- returns left mid brace
   - Expected: brace_left_mid() equals `\u23A8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left mid brace")
expect(brace_left_mid()).to_equal("\u23A8")
```

</details>

#### returns left bot brace

- returns left bot brace
   - Expected: brace_left_bot() equals `\u23A9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns left bot brace")
expect(brace_left_bot()).to_equal("\u23A9")
```

</details>

#### returns right top brace

- returns right top brace
   - Expected: brace_right_top() equals `\u23AB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right top brace")
expect(brace_right_top()).to_equal("\u23AB")
```

</details>

#### returns right mid brace

- returns right mid brace
   - Expected: brace_right_mid() equals `\u23AC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right mid brace")
expect(brace_right_mid()).to_equal("\u23AC")
```

</details>

#### returns right bot brace

- returns right bot brace
   - Expected: brace_right_bot() equals `\u23AD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns right bot brace")
expect(brace_right_bot()).to_equal("\u23AD")
```

</details>

#### returns brace extension

- returns brace extension
   - Expected: brace_ext() equals `\u23AA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns brace extension")
expect(brace_ext()).to_equal("\u23AA")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 112 |
| Active scenarios | 112 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `522f647a423c6ef7b3152a2776d21ea46de4951bccf1392e5c907c975f754521`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `522f647a423c6ef7b3152a2776d21ea46de4951bccf1392e5c907c975f754521`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `522f647a423c6ef7b3152a2776d21ea46de4951bccf1392e5c907c975f754521`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/math_symbols_coverage_spec.spl
mirror: doc/06_spec/unit/lib/common/math_symbols_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/math_symbols_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/math_symbols_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/math_symbols_coverage_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns sum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/math_symbols_coverage_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/math_symbols_coverage_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns coproduct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
