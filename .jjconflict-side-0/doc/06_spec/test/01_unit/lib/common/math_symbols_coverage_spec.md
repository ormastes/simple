# Unicode Math Symbols & Operators Coverage Specification

> Branch coverage tests for `std.unicode_math` symbol/operator lookup functions and box-drawing/bracket pieces. Split from math_coverage_spec.spl for memory.

<!-- sdn-diagram:id=math_symbols_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_symbols_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_symbols_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_symbols_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/common/math_symbols_coverage_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("sum")).to_equal("\u2211")
```

</details>

#### returns product

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("product")).to_equal("\u220F")
```

</details>

#### returns coproduct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("coproduct")).to_equal("\u2210")
```

</details>

#### returns integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("integral")).to_equal("\u222B")
```

</details>

#### returns double_integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("double_integral")).to_equal("\u222C")
```

</details>

#### returns triple_integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("triple_integral")).to_equal("\u222D")
```

</details>

#### returns contour_integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("contour_integral")).to_equal("\u222E")
```

</details>

#### returns surface_integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("surface_integral")).to_equal("\u222F")
```

</details>

#### returns volume_integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("volume_integral")).to_equal("\u2230")
```

</details>

#### root symbols

#### returns sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("sqrt")).to_equal("\u221A")
```

</details>

#### returns cbrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("cbrt")).to_equal("\u221B")
```

</details>

#### returns fourthrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("fourthrt")).to_equal("\u221C")
```

</details>

#### constants

#### returns infinity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("infinity")).to_equal("\u221E")
```

</details>

#### returns pi_sym

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("pi_sym")).to_equal("\u03C0")
```

</details>

#### returns euler

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("euler")).to_equal("\u212F")
```

</details>

#### returns imaginary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("imaginary")).to_equal("\u2111")
```

</details>

#### returns real_part

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("real_part")).to_equal("\u211C")
```

</details>

#### returns planck

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("planck")).to_equal("\u210F")
```

</details>

#### returns aleph

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("aleph")).to_equal("\u2135")
```

</details>

#### quantifiers

#### returns forall

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("forall")).to_equal("\u2200")
```

</details>

#### returns exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("exists")).to_equal("\u2203")
```

</details>

#### returns nexists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("nexists")).to_equal("\u2204")
```

</details>

#### logic symbols

#### returns and

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("and")).to_equal("\u2227")
```

</details>

#### returns or

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("or")).to_equal("\u2228")
```

</details>

#### returns not

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("not")).to_equal("\u00AC")
```

</details>

#### returns top

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("top")).to_equal("\u22A4")
```

</details>

#### returns bot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("bot")).to_equal("\u22A5")
```

</details>

#### returns proves

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("proves")).to_equal("\u22A2")
```

</details>

#### returns models

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("models")).to_equal("\u22A8")
```

</details>

#### returns therefore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("therefore")).to_equal("\u2234")
```

</details>

#### returns because

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("because")).to_equal("\u2235")
```

</details>

#### set symbols

#### returns in

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("in")).to_equal("\u2208")
```

</details>

#### returns notin

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("notin")).to_equal("\u2209")
```

</details>

#### returns subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("subset")).to_equal("\u2282")
```

</details>

#### returns superset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("superset")).to_equal("\u2283")
```

</details>

#### returns subseteq

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("subseteq")).to_equal("\u2286")
```

</details>

#### returns supseteq

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("supseteq")).to_equal("\u2287")
```

</details>

#### returns union

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("union")).to_equal("\u222A")
```

</details>

#### returns intersection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("intersection")).to_equal("\u2229")
```

</details>

#### returns emptyset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("emptyset")).to_equal("\u2205")
```

</details>

#### returns setminus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("setminus")).to_equal("\u2216")
```

</details>

#### number set symbols

#### returns naturals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("naturals")).to_equal("\u2115")
```

</details>

#### returns integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("integers")).to_equal("\u2124")
```

</details>

#### returns rationals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("rationals")).to_equal("\u211A")
```

</details>

#### returns reals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("reals")).to_equal("\u211D")
```

</details>

#### returns complex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("complex")).to_equal("\u2102")
```

</details>

#### returns primes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("primes")).to_equal("\u2119")
```

</details>

#### miscellaneous symbols

#### returns degree

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("degree")).to_equal("\u00B0")
```

</details>

#### returns prime

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("prime")).to_equal("\u2032")
```

</details>

#### returns double_prime

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("double_prime")).to_equal("\u2033")
```

</details>

#### returns triple_prime

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("triple_prime")).to_equal("\u2034")
```

</details>

#### returns ellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("ellipsis")).to_equal("\u2026")
```

</details>

#### returns vellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("vellipsis")).to_equal("\u22EE")
```

</details>

#### returns hellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("hellipsis")).to_equal("\u22EF")
```

</details>

#### returns dellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("dellipsis")).to_equal("\u22F1")
```

</details>

#### returns compose

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("compose")).to_equal("\u2218")
```

</details>

#### returns tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("tensor")).to_equal("\u2297")
```

</details>

#### returns direct_sum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("direct_sum")).to_equal("\u2295")
```

</details>

#### returns dot_product

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("dot_product")).to_equal("\u2299")
```

</details>

#### fallback for unknown symbols

#### returns unknown name unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sym("unknown_sym")).to_equal("unknown_sym")
```

</details>

### unicode_math math_op

#### comparison operators

#### returns leq

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("leq")).to_equal("\u2264")
```

</details>

#### returns geq

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("geq")).to_equal("\u2265")
```

</details>

#### returns neq

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("neq")).to_equal("\u2260")
```

</details>

#### returns approx

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("approx")).to_equal("\u2248")
```

</details>

#### returns equiv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("equiv")).to_equal("\u2261")
```

</details>

#### returns nequiv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("nequiv")).to_equal("\u2262")
```

</details>

#### returns cong

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("cong")).to_equal("\u2245")
```

</details>

#### returns sim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("sim")).to_equal("\u223C")
```

</details>

#### returns ll

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("ll")).to_equal("\u226A")
```

</details>

#### returns gg

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("gg")).to_equal("\u226B")
```

</details>

#### returns propto

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("propto")).to_equal("\u221D")
```

</details>

#### returns defeq

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("defeq")).to_equal("\u2254")
```

</details>

#### arithmetic operators

#### returns pm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("pm")).to_equal("\u00B1")
```

</details>

#### returns mp

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("mp")).to_equal("\u2213")
```

</details>

#### returns times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("times")).to_equal("\u00D7")
```

</details>

#### returns div

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("div")).to_equal("\u00F7")
```

</details>

#### returns cdot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("cdot")).to_equal("\u00B7")
```

</details>

#### returns star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("star")).to_equal("\u2217")
```

</details>

#### arrow operators

#### returns to

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("to")).to_equal("\u2192")
```

</details>

#### returns from

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("from")).to_equal("\u2190")
```

</details>

#### returns lr

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("lr")).to_equal("\u2194")
```

</details>

#### returns implies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("implies")).to_equal("\u21D2")
```

</details>

#### returns implied_by

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("implied_by")).to_equal("\u21D0")
```

</details>

#### returns iff

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("iff")).to_equal("\u21D4")
```

</details>

#### returns mapsto

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("mapsto")).to_equal("\u21A6")
```

</details>

#### returns long_to

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("long_to")).to_equal("\u27F6")
```

</details>

#### returns long_implies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("long_implies")).to_equal("\u27F9")
```

</details>

#### returns long_iff

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("long_iff")).to_equal("\u27FA")
```

</details>

#### returns surjection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("surjection")).to_equal("\u21A0")
```

</details>

#### returns injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("injection")).to_equal("\u21A3")
```

</details>

#### fallback for unknown operators

#### returns unknown name unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_op("unknown_op")).to_equal("unknown_op")
```

</details>

### unicode_math brackets and lines

#### hline

#### creates line of width 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = hline(3)
expect(line.len()).to_be_greater_than(0)
```

</details>

#### creates line of width 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hline(0)).to_equal("")
```

</details>

#### square bracket pieces

#### returns left top bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bracket_left_top()).to_equal("\u23A1")
```

</details>

#### returns left mid bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bracket_left_mid()).to_equal("\u23A2")
```

</details>

#### returns left bot bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bracket_left_bot()).to_equal("\u23A3")
```

</details>

#### returns right top bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bracket_right_top()).to_equal("\u23A4")
```

</details>

#### returns right mid bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bracket_right_mid()).to_equal("\u23A5")
```

</details>

#### returns right bot bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bracket_right_bot()).to_equal("\u23A6")
```

</details>

#### parenthesis pieces

#### returns left top paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(paren_left_top()).to_equal("\u239B")
```

</details>

#### returns left mid paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(paren_left_mid()).to_equal("\u239C")
```

</details>

#### returns left bot paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(paren_left_bot()).to_equal("\u239D")
```

</details>

#### returns right top paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(paren_right_top()).to_equal("\u239E")
```

</details>

#### returns right mid paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(paren_right_mid()).to_equal("\u239F")
```

</details>

#### returns right bot paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(paren_right_bot()).to_equal("\u23A0")
```

</details>

#### brace pieces

#### returns left top brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(brace_left_top()).to_equal("\u23A7")
```

</details>

#### returns left mid brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(brace_left_mid()).to_equal("\u23A8")
```

</details>

#### returns left bot brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(brace_left_bot()).to_equal("\u23A9")
```

</details>

#### returns right top brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(brace_right_top()).to_equal("\u23AB")
```

</details>

#### returns right mid brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(brace_right_mid()).to_equal("\u23AC")
```

</details>

#### returns right bot brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(brace_right_bot()).to_equal("\u23AD")
```

</details>

#### returns brace extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
