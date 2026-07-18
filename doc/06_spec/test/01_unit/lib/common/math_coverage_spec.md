# Unicode Math Greek/Superscript/Subscript Coverage Specification

> Branch coverage tests for `std.unicode_math` greek, superscript, and subscript lookup functions. Split from the original monolithic spec for memory safety. See also: math_symbols_coverage_spec.spl and math_repr_coverage_spec.spl.

<!-- sdn-diagram:id=math_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 103 | 103 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unicode Math Greek/Superscript/Subscript Coverage Specification

Branch coverage tests for `std.unicode_math` greek, superscript, and subscript lookup functions. Split from the original monolithic spec for memory safety. See also: math_symbols_coverage_spec.spl and math_repr_coverage_spec.spl.

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
| Source | `test/01_unit/lib/common/math_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch coverage tests for `std.unicode_math` greek, superscript, and subscript
lookup functions. Split from the original monolithic spec for memory safety.
See also: math_symbols_coverage_spec.spl and math_repr_coverage_spec.spl.

## Key Concepts

| Concept | Description |
|---------|-------------|
| unicode_math | Lookup tables: greek, superscript, subscript |

## Scenarios

### unicode_math greek

#### lowercase greek letters

#### converts alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("alpha")).to_equal("\u03B1")
```

</details>

#### converts beta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("beta")).to_equal("\u03B2")
```

</details>

#### converts gamma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("gamma")).to_equal("\u03B3")
```

</details>

#### converts delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("delta")).to_equal("\u03B4")
```

</details>

#### converts epsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("epsilon")).to_equal("\u03B5")
```

</details>

#### converts zeta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("zeta")).to_equal("\u03B6")
```

</details>

#### converts eta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("eta")).to_equal("\u03B7")
```

</details>

#### converts theta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("theta")).to_equal("\u03B8")
```

</details>

#### converts iota

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("iota")).to_equal("\u03B9")
```

</details>

#### converts kappa

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("kappa")).to_equal("\u03BA")
```

</details>

#### converts lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("lambda")).to_equal("\u03BB")
```

</details>

#### converts mu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("mu")).to_equal("\u03BC")
```

</details>

#### converts nu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("nu")).to_equal("\u03BD")
```

</details>

#### converts xi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("xi")).to_equal("\u03BE")
```

</details>

#### converts omicron

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("omicron")).to_equal("\u03BF")
```

</details>

#### converts pi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("pi")).to_equal("\u03C0")
```

</details>

#### converts rho

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("rho")).to_equal("\u03C1")
```

</details>

#### converts sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("sigma")).to_equal("\u03C3")
```

</details>

#### converts tau

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("tau")).to_equal("\u03C4")
```

</details>

#### converts upsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("upsilon")).to_equal("\u03C5")
```

</details>

#### converts phi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("phi")).to_equal("\u03C6")
```

</details>

#### converts chi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("chi")).to_equal("\u03C7")
```

</details>

#### converts psi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("psi")).to_equal("\u03C8")
```

</details>

#### converts omega

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("omega")).to_equal("\u03C9")
```

</details>

#### variant greek forms

#### converts varepsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("varepsilon")).to_equal("\u03F5")
```

</details>

#### converts vartheta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("vartheta")).to_equal("\u03D1")
```

</details>

#### converts varphi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("varphi")).to_equal("\u03D5")
```

</details>

#### converts varrho

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("varrho")).to_equal("\u03F1")
```

</details>

#### converts varpi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("varpi")).to_equal("\u03D6")
```

</details>

#### converts varkappa

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("varkappa")).to_equal("\u03F0")
```

</details>

#### converts partial

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("partial")).to_equal("\u2202")
```

</details>

#### converts nabla

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("nabla")).to_equal("\u2207")
```

</details>

#### fallback for unknown names

#### returns name unchanged for unknown greek

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("notgreek")).to_equal("notgreek")
```

</details>

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek("")).to_equal("")
```

</details>

#### uppercase greek letters

#### converts Gamma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Gamma")).to_equal("\u0393")
```

</details>

#### converts Delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Delta")).to_equal("\u0394")
```

</details>

#### converts Theta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Theta")).to_equal("\u0398")
```

</details>

#### converts Lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Lambda")).to_equal("\u039B")
```

</details>

#### converts Xi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Xi")).to_equal("\u039E")
```

</details>

#### converts Pi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Pi")).to_equal("\u03A0")
```

</details>

#### converts Sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Sigma")).to_equal("\u03A3")
```

</details>

#### converts Upsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Upsilon")).to_equal("\u03A5")
```

</details>

#### converts Phi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Phi")).to_equal("\u03A6")
```

</details>

#### converts Psi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Psi")).to_equal("\u03A8")
```

</details>

#### converts Omega

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("Omega")).to_equal("\u03A9")
```

</details>

#### returns unknown uppercase unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greek_upper("NotUpper")).to_equal("NotUpper")
```

</details>

### unicode_math superscript

#### superscript_char digits

#### converts 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("0")).to_equal("\u2070")
```

</details>

#### converts 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("1")).to_equal("\u00B9")
```

</details>

#### converts 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("2")).to_equal("\u00B2")
```

</details>

#### converts 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("3")).to_equal("\u00B3")
```

</details>

#### converts 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("4")).to_equal("\u2074")
```

</details>

#### converts 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("5")).to_equal("\u2075")
```

</details>

#### converts 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("6")).to_equal("\u2076")
```

</details>

#### converts 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("7")).to_equal("\u2077")
```

</details>

#### converts 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("8")).to_equal("\u2078")
```

</details>

#### converts 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("9")).to_equal("\u2079")
```

</details>

#### superscript_char operators and letters

#### converts plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("+")).to_equal("\u207A")
```

</details>

#### converts minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("-")).to_equal("\u207B")
```

</details>

#### converts equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("=")).to_equal("\u207C")
```

</details>

#### converts left paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("(")).to_equal("\u207D")
```

</details>

#### converts right paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char(")")).to_equal("\u207E")
```

</details>

#### converts n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("n")).to_equal("\u207F")
```

</details>

#### converts i

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("i")).to_equal("\u2071")
```

</details>

#### converts x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("x")).to_equal("\u02E3")
```

</details>

#### superscript_char fallback

#### returns unknown char unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("z")).to_equal("z")
```

</details>

#### returns q unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript_char("q")).to_equal("q")
```

</details>

#### superscript multi-char string

#### converts digit string 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = superscript("23")
expect(result).to_contain("\u00B2")
expect(result).to_contain("\u00B3")
```

</details>

#### converts mixed n+1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = superscript("n+1")
expect(result).to_contain("\u207F")
expect(result).to_contain("\u207A")
expect(result).to_contain("\u00B9")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(superscript("")).to_equal("")
```

</details>

### unicode_math subscript

#### subscript_char digits

#### converts 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("0")).to_equal("\u2080")
```

</details>

#### converts 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("1")).to_equal("\u2081")
```

</details>

#### converts 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("2")).to_equal("\u2082")
```

</details>

#### converts 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("3")).to_equal("\u2083")
```

</details>

#### converts 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("4")).to_equal("\u2084")
```

</details>

#### converts 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("5")).to_equal("\u2085")
```

</details>

#### converts 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("6")).to_equal("\u2086")
```

</details>

#### converts 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("7")).to_equal("\u2087")
```

</details>

#### converts 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("8")).to_equal("\u2088")
```

</details>

#### converts 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("9")).to_equal("\u2089")
```

</details>

#### subscript_char operators

#### converts plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("+")).to_equal("\u208A")
```

</details>

#### converts minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("-")).to_equal("\u208B")
```

</details>

#### converts equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("=")).to_equal("\u208C")
```

</details>

#### converts left paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("(")).to_equal("\u208D")
```

</details>

#### converts right paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char(")")).to_equal("\u208E")
```

</details>

#### subscript_char letters

#### converts a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("a")).to_equal("\u2090")
```

</details>

#### converts e

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("e")).to_equal("\u2091")
```

</details>

#### converts o

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("o")).to_equal("\u2092")
```

</details>

#### converts x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("x")).to_equal("\u2093")
```

</details>

#### converts h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("h")).to_equal("\u2095")
```

</details>

#### converts k

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("k")).to_equal("\u2096")
```

</details>

#### converts l

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("l")).to_equal("\u2097")
```

</details>

#### converts m

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("m")).to_equal("\u2098")
```

</details>

#### converts n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("n")).to_equal("\u2099")
```

</details>

#### converts p

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("p")).to_equal("\u209A")
```

</details>

#### converts s

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("s")).to_equal("\u209B")
```

</details>

#### converts t

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("t")).to_equal("\u209C")
```

</details>

#### converts i

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("i")).to_equal("\u1D62")
```

</details>

#### converts j

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("j")).to_equal("\u2C7C")
```

</details>

#### converts r

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("r")).to_equal("\u1D63")
```

</details>

#### subscript_char fallback

#### returns unknown char unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("z")).to_equal("z")
```

</details>

#### returns Q unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript_char("Q")).to_equal("Q")
```

</details>

#### subscript multi-char string

#### converts digit string 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = subscript("12")
expect(result).to_contain("\u2081")
expect(result).to_contain("\u2082")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subscript("")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 103 |
| Active scenarios | 103 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
