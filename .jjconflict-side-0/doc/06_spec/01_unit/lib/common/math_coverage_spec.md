# Unicode Math Greek/Superscript/Subscript Coverage Specification

> Branch coverage tests for `std.unicode_math` greek, superscript, and subscript lookup functions. Split from the original monolithic spec for memory safety. See also: math_symbols_coverage_spec.spl and math_repr_coverage_spec.spl.

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
| Updated | 2026-08-26 |
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

- converts alpha
   - Expected: greek("alpha") equals `\u03B1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts alpha")
expect(greek("alpha")).to_equal("\u03B1")
```

</details>

#### converts beta

- converts beta
   - Expected: greek("beta") equals `\u03B2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts beta")
expect(greek("beta")).to_equal("\u03B2")
```

</details>

#### converts gamma

- converts gamma
   - Expected: greek("gamma") equals `\u03B3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts gamma")
expect(greek("gamma")).to_equal("\u03B3")
```

</details>

#### converts delta

- converts delta
   - Expected: greek("delta") equals `\u03B4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts delta")
expect(greek("delta")).to_equal("\u03B4")
```

</details>

#### converts epsilon

- converts epsilon
   - Expected: greek("epsilon") equals `\u03B5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts epsilon")
expect(greek("epsilon")).to_equal("\u03B5")
```

</details>

#### converts zeta

- converts zeta
   - Expected: greek("zeta") equals `\u03B6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts zeta")
expect(greek("zeta")).to_equal("\u03B6")
```

</details>

#### converts eta

- converts eta
   - Expected: greek("eta") equals `\u03B7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts eta")
expect(greek("eta")).to_equal("\u03B7")
```

</details>

#### converts theta

- converts theta
   - Expected: greek("theta") equals `\u03B8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts theta")
expect(greek("theta")).to_equal("\u03B8")
```

</details>

#### converts iota

- converts iota
   - Expected: greek("iota") equals `\u03B9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts iota")
expect(greek("iota")).to_equal("\u03B9")
```

</details>

#### converts kappa

- converts kappa
   - Expected: greek("kappa") equals `\u03BA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts kappa")
expect(greek("kappa")).to_equal("\u03BA")
```

</details>

#### converts lambda

- converts lambda
   - Expected: greek("lambda") equals `\u03BB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts lambda")
expect(greek("lambda")).to_equal("\u03BB")
```

</details>

#### converts mu

- converts mu
   - Expected: greek("mu") equals `\u03BC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts mu")
expect(greek("mu")).to_equal("\u03BC")
```

</details>

#### converts nu

- converts nu
   - Expected: greek("nu") equals `\u03BD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nu")
expect(greek("nu")).to_equal("\u03BD")
```

</details>

#### converts xi

- converts xi
   - Expected: greek("xi") equals `\u03BE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts xi")
expect(greek("xi")).to_equal("\u03BE")
```

</details>

#### converts omicron

- converts omicron
   - Expected: greek("omicron") equals `\u03BF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts omicron")
expect(greek("omicron")).to_equal("\u03BF")
```

</details>

#### converts pi

- converts pi
   - Expected: greek("pi") equals `\u03C0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts pi")
expect(greek("pi")).to_equal("\u03C0")
```

</details>

#### converts rho

- converts rho
   - Expected: greek("rho") equals `\u03C1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts rho")
expect(greek("rho")).to_equal("\u03C1")
```

</details>

#### converts sigma

- converts sigma
   - Expected: greek("sigma") equals `\u03C3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts sigma")
expect(greek("sigma")).to_equal("\u03C3")
```

</details>

#### converts tau

- converts tau
   - Expected: greek("tau") equals `\u03C4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts tau")
expect(greek("tau")).to_equal("\u03C4")
```

</details>

#### converts upsilon

- converts upsilon
   - Expected: greek("upsilon") equals `\u03C5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts upsilon")
expect(greek("upsilon")).to_equal("\u03C5")
```

</details>

#### converts phi

- converts phi
   - Expected: greek("phi") equals `\u03C6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts phi")
expect(greek("phi")).to_equal("\u03C6")
```

</details>

#### converts chi

- converts chi
   - Expected: greek("chi") equals `\u03C7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts chi")
expect(greek("chi")).to_equal("\u03C7")
```

</details>

#### converts psi

- converts psi
   - Expected: greek("psi") equals `\u03C8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts psi")
expect(greek("psi")).to_equal("\u03C8")
```

</details>

#### converts omega

- converts omega
   - Expected: greek("omega") equals `\u03C9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts omega")
expect(greek("omega")).to_equal("\u03C9")
```

</details>

#### variant greek forms

#### converts varepsilon

- converts varepsilon
   - Expected: greek("varepsilon") equals `\u03F5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts varepsilon")
expect(greek("varepsilon")).to_equal("\u03F5")
```

</details>

#### converts vartheta

- converts vartheta
   - Expected: greek("vartheta") equals `\u03D1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts vartheta")
expect(greek("vartheta")).to_equal("\u03D1")
```

</details>

#### converts varphi

- converts varphi
   - Expected: greek("varphi") equals `\u03D5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts varphi")
expect(greek("varphi")).to_equal("\u03D5")
```

</details>

#### converts varrho

- converts varrho
   - Expected: greek("varrho") equals `\u03F1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts varrho")
expect(greek("varrho")).to_equal("\u03F1")
```

</details>

#### converts varpi

- converts varpi
   - Expected: greek("varpi") equals `\u03D6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts varpi")
expect(greek("varpi")).to_equal("\u03D6")
```

</details>

#### converts varkappa

- converts varkappa
   - Expected: greek("varkappa") equals `\u03F0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts varkappa")
expect(greek("varkappa")).to_equal("\u03F0")
```

</details>

#### converts partial

- converts partial
   - Expected: greek("partial") equals `\u2202`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts partial")
expect(greek("partial")).to_equal("\u2202")
```

</details>

#### converts nabla

- converts nabla
   - Expected: greek("nabla") equals `\u2207`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nabla")
expect(greek("nabla")).to_equal("\u2207")
```

</details>

#### fallback for unknown names

#### returns name unchanged for unknown greek

- returns name unchanged for unknown greek
   - Expected: greek("notgreek") equals `notgreek`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns name unchanged for unknown greek")
expect(greek("notgreek")).to_equal("notgreek")
```

</details>

#### returns empty string unchanged

- returns empty string unchanged
   - Expected: greek("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string unchanged")
expect(greek("")).to_equal("")
```

</details>

#### uppercase greek letters

#### converts Gamma

- converts Gamma
   - Expected: greek_upper("Gamma") equals `\u0393`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Gamma")
expect(greek_upper("Gamma")).to_equal("\u0393")
```

</details>

#### converts Delta

- converts Delta
   - Expected: greek_upper("Delta") equals `\u0394`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Delta")
expect(greek_upper("Delta")).to_equal("\u0394")
```

</details>

#### converts Theta

- converts Theta
   - Expected: greek_upper("Theta") equals `\u0398`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Theta")
expect(greek_upper("Theta")).to_equal("\u0398")
```

</details>

#### converts Lambda

- converts Lambda
   - Expected: greek_upper("Lambda") equals `\u039B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Lambda")
expect(greek_upper("Lambda")).to_equal("\u039B")
```

</details>

#### converts Xi

- converts Xi
   - Expected: greek_upper("Xi") equals `\u039E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Xi")
expect(greek_upper("Xi")).to_equal("\u039E")
```

</details>

#### converts Pi

- converts Pi
   - Expected: greek_upper("Pi") equals `\u03A0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Pi")
expect(greek_upper("Pi")).to_equal("\u03A0")
```

</details>

#### converts Sigma

- converts Sigma
   - Expected: greek_upper("Sigma") equals `\u03A3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Sigma")
expect(greek_upper("Sigma")).to_equal("\u03A3")
```

</details>

#### converts Upsilon

- converts Upsilon
   - Expected: greek_upper("Upsilon") equals `\u03A5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Upsilon")
expect(greek_upper("Upsilon")).to_equal("\u03A5")
```

</details>

#### converts Phi

- converts Phi
   - Expected: greek_upper("Phi") equals `\u03A6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Phi")
expect(greek_upper("Phi")).to_equal("\u03A6")
```

</details>

#### converts Psi

- converts Psi
   - Expected: greek_upper("Psi") equals `\u03A8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Psi")
expect(greek_upper("Psi")).to_equal("\u03A8")
```

</details>

#### converts Omega

- converts Omega
   - Expected: greek_upper("Omega") equals `\u03A9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Omega")
expect(greek_upper("Omega")).to_equal("\u03A9")
```

</details>

#### returns unknown uppercase unchanged

- returns unknown uppercase unchanged
   - Expected: greek_upper("NotUpper") equals `NotUpper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown uppercase unchanged")
expect(greek_upper("NotUpper")).to_equal("NotUpper")
```

</details>

### unicode_math superscript

#### superscript_char digits

#### converts 0

- converts 0
   - Expected: superscript_char("0") equals `\u2070`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 0")
expect(superscript_char("0")).to_equal("\u2070")
```

</details>

#### converts 1

- converts 1
   - Expected: superscript_char("1") equals `\u00B9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 1")
expect(superscript_char("1")).to_equal("\u00B9")
```

</details>

#### converts 2

- converts 2
   - Expected: superscript_char("2") equals `\u00B2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 2")
expect(superscript_char("2")).to_equal("\u00B2")
```

</details>

#### converts 3

- converts 3
   - Expected: superscript_char("3") equals `\u00B3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 3")
expect(superscript_char("3")).to_equal("\u00B3")
```

</details>

#### converts 4

- converts 4
   - Expected: superscript_char("4") equals `\u2074`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 4")
expect(superscript_char("4")).to_equal("\u2074")
```

</details>

#### converts 5

- converts 5
   - Expected: superscript_char("5") equals `\u2075`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 5")
expect(superscript_char("5")).to_equal("\u2075")
```

</details>

#### converts 6

- converts 6
   - Expected: superscript_char("6") equals `\u2076`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 6")
expect(superscript_char("6")).to_equal("\u2076")
```

</details>

#### converts 7

- converts 7
   - Expected: superscript_char("7") equals `\u2077`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 7")
expect(superscript_char("7")).to_equal("\u2077")
```

</details>

#### converts 8

- converts 8
   - Expected: superscript_char("8") equals `\u2078`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 8")
expect(superscript_char("8")).to_equal("\u2078")
```

</details>

#### converts 9

- converts 9
   - Expected: superscript_char("9") equals `\u2079`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 9")
expect(superscript_char("9")).to_equal("\u2079")
```

</details>

#### superscript_char operators and letters

#### converts plus

- converts plus
   - Expected: superscript_char("+") equals `\u207A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts plus")
expect(superscript_char("+")).to_equal("\u207A")
```

</details>

#### converts minus

- converts minus
   - Expected: superscript_char("-") equals `\u207B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts minus")
expect(superscript_char("-")).to_equal("\u207B")
```

</details>

#### converts equals

- converts equals
   - Expected: superscript_char("=") equals `\u207C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts equals")
expect(superscript_char("=")).to_equal("\u207C")
```

</details>

#### converts left paren

- converts left paren
   - Expected: superscript_char("(") equals `\u207D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts left paren")
expect(superscript_char("(")).to_equal("\u207D")
```

</details>

#### converts right paren

- converts right paren
   - Expected: superscript_char(")") equals `\u207E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts right paren")
expect(superscript_char(")")).to_equal("\u207E")
```

</details>

#### converts n

- converts n
   - Expected: superscript_char("n") equals `\u207F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts n")
expect(superscript_char("n")).to_equal("\u207F")
```

</details>

#### converts i

- converts i
   - Expected: superscript_char("i") equals `\u2071`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts i")
expect(superscript_char("i")).to_equal("\u2071")
```

</details>

#### converts x

- converts x
   - Expected: superscript_char("x") equals `\u02E3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts x")
expect(superscript_char("x")).to_equal("\u02E3")
```

</details>

#### superscript_char fallback

#### returns unknown char unchanged

- returns unknown char unchanged
   - Expected: superscript_char("z") equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown char unchanged")
expect(superscript_char("z")).to_equal("z")
```

</details>

#### returns q unchanged

- returns q unchanged
   - Expected: superscript_char("q") equals `q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns q unchanged")
expect(superscript_char("q")).to_equal("q")
```

</details>

#### superscript multi-char string

#### converts digit string 23

- converts digit string 23


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts digit string 23")
val result = superscript("23")
expect(result).to_contain("\u00B2")
expect(result).to_contain("\u00B3")
```

</details>

#### converts mixed n+1

- converts mixed n+1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts mixed n+1")
val result = superscript("n+1")
expect(result).to_contain("\u207F")
expect(result).to_contain("\u207A")
expect(result).to_contain("\u00B9")
```

</details>

#### handles empty string

- handles empty string
   - Expected: superscript("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
expect(superscript("")).to_equal("")
```

</details>

### unicode_math subscript

#### subscript_char digits

#### converts 0

- converts 0
   - Expected: subscript_char("0") equals `\u2080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 0")
expect(subscript_char("0")).to_equal("\u2080")
```

</details>

#### converts 1

- converts 1
   - Expected: subscript_char("1") equals `\u2081`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 1")
expect(subscript_char("1")).to_equal("\u2081")
```

</details>

#### converts 2

- converts 2
   - Expected: subscript_char("2") equals `\u2082`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 2")
expect(subscript_char("2")).to_equal("\u2082")
```

</details>

#### converts 3

- converts 3
   - Expected: subscript_char("3") equals `\u2083`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 3")
expect(subscript_char("3")).to_equal("\u2083")
```

</details>

#### converts 4

- converts 4
   - Expected: subscript_char("4") equals `\u2084`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 4")
expect(subscript_char("4")).to_equal("\u2084")
```

</details>

#### converts 5

- converts 5
   - Expected: subscript_char("5") equals `\u2085`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 5")
expect(subscript_char("5")).to_equal("\u2085")
```

</details>

#### converts 6

- converts 6
   - Expected: subscript_char("6") equals `\u2086`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 6")
expect(subscript_char("6")).to_equal("\u2086")
```

</details>

#### converts 7

- converts 7
   - Expected: subscript_char("7") equals `\u2087`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 7")
expect(subscript_char("7")).to_equal("\u2087")
```

</details>

#### converts 8

- converts 8
   - Expected: subscript_char("8") equals `\u2088`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 8")
expect(subscript_char("8")).to_equal("\u2088")
```

</details>

#### converts 9

- converts 9
   - Expected: subscript_char("9") equals `\u2089`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 9")
expect(subscript_char("9")).to_equal("\u2089")
```

</details>

#### subscript_char operators

#### converts plus

- converts plus
   - Expected: subscript_char("+") equals `\u208A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts plus")
expect(subscript_char("+")).to_equal("\u208A")
```

</details>

#### converts minus

- converts minus
   - Expected: subscript_char("-") equals `\u208B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts minus")
expect(subscript_char("-")).to_equal("\u208B")
```

</details>

#### converts equals

- converts equals
   - Expected: subscript_char("=") equals `\u208C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts equals")
expect(subscript_char("=")).to_equal("\u208C")
```

</details>

#### converts left paren

- converts left paren
   - Expected: subscript_char("(") equals `\u208D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts left paren")
expect(subscript_char("(")).to_equal("\u208D")
```

</details>

#### converts right paren

- converts right paren
   - Expected: subscript_char(")") equals `\u208E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts right paren")
expect(subscript_char(")")).to_equal("\u208E")
```

</details>

#### subscript_char letters

#### converts a

- converts a
   - Expected: subscript_char("a") equals `\u2090`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts a")
expect(subscript_char("a")).to_equal("\u2090")
```

</details>

#### converts e

- converts e
   - Expected: subscript_char("e") equals `\u2091`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts e")
expect(subscript_char("e")).to_equal("\u2091")
```

</details>

#### converts o

- converts o
   - Expected: subscript_char("o") equals `\u2092`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts o")
expect(subscript_char("o")).to_equal("\u2092")
```

</details>

#### converts x

- converts x
   - Expected: subscript_char("x") equals `\u2093`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts x")
expect(subscript_char("x")).to_equal("\u2093")
```

</details>

#### converts h

- converts h
   - Expected: subscript_char("h") equals `\u2095`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts h")
expect(subscript_char("h")).to_equal("\u2095")
```

</details>

#### converts k

- converts k
   - Expected: subscript_char("k") equals `\u2096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts k")
expect(subscript_char("k")).to_equal("\u2096")
```

</details>

#### converts l

- converts l
   - Expected: subscript_char("l") equals `\u2097`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts l")
expect(subscript_char("l")).to_equal("\u2097")
```

</details>

#### converts m

- converts m
   - Expected: subscript_char("m") equals `\u2098`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts m")
expect(subscript_char("m")).to_equal("\u2098")
```

</details>

#### converts n

- converts n
   - Expected: subscript_char("n") equals `\u2099`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts n")
expect(subscript_char("n")).to_equal("\u2099")
```

</details>

#### converts p

- converts p
   - Expected: subscript_char("p") equals `\u209A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts p")
expect(subscript_char("p")).to_equal("\u209A")
```

</details>

#### converts s

- converts s
   - Expected: subscript_char("s") equals `\u209B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts s")
expect(subscript_char("s")).to_equal("\u209B")
```

</details>

#### converts t

- converts t
   - Expected: subscript_char("t") equals `\u209C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts t")
expect(subscript_char("t")).to_equal("\u209C")
```

</details>

#### converts i

- converts i
   - Expected: subscript_char("i") equals `\u1D62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts i")
expect(subscript_char("i")).to_equal("\u1D62")
```

</details>

#### converts j

- converts j
   - Expected: subscript_char("j") equals `\u2C7C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts j")
expect(subscript_char("j")).to_equal("\u2C7C")
```

</details>

#### converts r

- converts r
   - Expected: subscript_char("r") equals `\u1D63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts r")
expect(subscript_char("r")).to_equal("\u1D63")
```

</details>

#### subscript_char fallback

#### returns unknown char unchanged

- returns unknown char unchanged
   - Expected: subscript_char("z") equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown char unchanged")
expect(subscript_char("z")).to_equal("z")
```

</details>

#### returns Q unchanged

- returns Q unchanged
   - Expected: subscript_char("Q") equals `Q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Q unchanged")
expect(subscript_char("Q")).to_equal("Q")
```

</details>

#### subscript multi-char string

#### converts digit string 12

- converts digit string 12


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts digit string 12")
val result = subscript("12")
expect(result).to_contain("\u2081")
expect(result).to_contain("\u2082")
```

</details>

#### handles empty string

- handles empty string
   - Expected: subscript("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e380089f053db3ddc01d6894514cb0fc1a084b387cd7e34b45f324d911643c01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e380089f053db3ddc01d6894514cb0fc1a084b387cd7e34b45f324d911643c01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e380089f053db3ddc01d6894514cb0fc1a084b387cd7e34b45f324d911643c01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_coverage_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts alpha' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_coverage_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts beta' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_coverage_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts gamma' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
