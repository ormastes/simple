# String Core Exhaustive Char Table Specification

> Purpose: Prove that string_core - char_code_inline exhaustive digits.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 106 | 106 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Exhaustive Char Table Specification

Purpose: Prove that string_core - char_code_inline exhaustive digits.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-STRING-CORE |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/string_core_exhaustive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that string_core - char_code_inline exhaustive digits.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### string_core - char_code_inline exhaustive digits

#### all digits

#### returns 49 for 1

- returns 49 for 1
- Verify: returns 49 for 1
   - Expected: char_code_inline("1") equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 49 for 1")
step("Verify: returns 49 for 1")
# @req: REQ-LIB-COMMON-001
expect(char_code_inline("1")).to_equal(49)
```

</details>

#### returns 50 for 2

- returns 50 for 2
- Verify: returns 50 for 2
   - Expected: char_code_inline("2") equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 50 for 2")
step("Verify: returns 50 for 2")
expect(char_code_inline("2")).to_equal(50)
```

</details>

#### returns 51 for 3

- returns 51 for 3
- Verify: returns 51 for 3
   - Expected: char_code_inline("3") equals `51`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 51 for 3")
step("Verify: returns 51 for 3")
expect(char_code_inline("3")).to_equal(51)
```

</details>

#### returns 52 for 4

- returns 52 for 4
- Verify: returns 52 for 4
   - Expected: char_code_inline("4") equals `52`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 52 for 4")
step("Verify: returns 52 for 4")
expect(char_code_inline("4")).to_equal(52)
```

</details>

#### returns 54 for 6

- returns 54 for 6
- Verify: returns 54 for 6
   - Expected: char_code_inline("6") equals `54`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 54 for 6")
step("Verify: returns 54 for 6")
expect(char_code_inline("6")).to_equal(54)
```

</details>

#### returns 55 for 7

- returns 55 for 7
- Verify: returns 55 for 7
   - Expected: char_code_inline("7") equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 55 for 7")
step("Verify: returns 55 for 7")
expect(char_code_inline("7")).to_equal(55)
```

</details>

#### returns 56 for 8

- returns 56 for 8
- Verify: returns 56 for 8
   - Expected: char_code_inline("8") equals `56`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 56 for 8")
step("Verify: returns 56 for 8")
expect(char_code_inline("8")).to_equal(56)
```

</details>

### string_core - char_code_inline exhaustive uppercase

#### uppercase B through L

#### returns 66 for B

- returns 66 for B
- Verify: returns 66 for B
   - Expected: char_code_inline("B") equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 66 for B")
step("Verify: returns 66 for B")
expect(char_code_inline("B")).to_equal(66)
```

</details>

#### returns 67 for C

- returns 67 for C
- Verify: returns 67 for C
   - Expected: char_code_inline("C") equals `67`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 67 for C")
step("Verify: returns 67 for C")
expect(char_code_inline("C")).to_equal(67)
```

</details>

#### returns 68 for D

- returns 68 for D
- Verify: returns 68 for D
   - Expected: char_code_inline("D") equals `68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 68 for D")
step("Verify: returns 68 for D")
expect(char_code_inline("D")).to_equal(68)
```

</details>

#### returns 69 for E

- returns 69 for E
- Verify: returns 69 for E
   - Expected: char_code_inline("E") equals `69`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 69 for E")
step("Verify: returns 69 for E")
expect(char_code_inline("E")).to_equal(69)
```

</details>

#### returns 70 for F

- returns 70 for F
- Verify: returns 70 for F
   - Expected: char_code_inline("F") equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 70 for F")
step("Verify: returns 70 for F")
expect(char_code_inline("F")).to_equal(70)
```

</details>

#### returns 71 for G

- returns 71 for G
- Verify: returns 71 for G
   - Expected: char_code_inline("G") equals `71`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 71 for G")
step("Verify: returns 71 for G")
expect(char_code_inline("G")).to_equal(71)
```

</details>

#### returns 72 for H

- returns 72 for H
- Verify: returns 72 for H
   - Expected: char_code_inline("H") equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 72 for H")
step("Verify: returns 72 for H")
expect(char_code_inline("H")).to_equal(72)
```

</details>

#### returns 73 for I

- returns 73 for I
- Verify: returns 73 for I
   - Expected: char_code_inline("I") equals `73`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 73 for I")
step("Verify: returns 73 for I")
expect(char_code_inline("I")).to_equal(73)
```

</details>

#### returns 74 for J

- returns 74 for J
- Verify: returns 74 for J
   - Expected: char_code_inline("J") equals `74`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 74 for J")
step("Verify: returns 74 for J")
expect(char_code_inline("J")).to_equal(74)
```

</details>

#### returns 75 for K

- returns 75 for K
- Verify: returns 75 for K
   - Expected: char_code_inline("K") equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 75 for K")
step("Verify: returns 75 for K")
expect(char_code_inline("K")).to_equal(75)
```

</details>

#### returns 76 for L

- returns 76 for L
- Verify: returns 76 for L
   - Expected: char_code_inline("L") equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 76 for L")
step("Verify: returns 76 for L")
expect(char_code_inline("L")).to_equal(76)
```

</details>

#### uppercase N through Y

#### returns 78 for N

- returns 78 for N
- Verify: returns 78 for N
   - Expected: char_code_inline("N") equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 78 for N")
step("Verify: returns 78 for N")
expect(char_code_inline("N")).to_equal(78)
```

</details>

#### returns 79 for O

- returns 79 for O
- Verify: returns 79 for O
   - Expected: char_code_inline("O") equals `79`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 79 for O")
step("Verify: returns 79 for O")
expect(char_code_inline("O")).to_equal(79)
```

</details>

#### returns 80 for P

- returns 80 for P
- Verify: returns 80 for P
   - Expected: char_code_inline("P") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 80 for P")
step("Verify: returns 80 for P")
expect(char_code_inline("P")).to_equal(80)
```

</details>

#### returns 81 for Q

- returns 81 for Q
- Verify: returns 81 for Q
   - Expected: char_code_inline("Q") equals `81`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 81 for Q")
step("Verify: returns 81 for Q")
expect(char_code_inline("Q")).to_equal(81)
```

</details>

#### returns 82 for R

- returns 82 for R
- Verify: returns 82 for R
   - Expected: char_code_inline("R") equals `82`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 82 for R")
step("Verify: returns 82 for R")
expect(char_code_inline("R")).to_equal(82)
```

</details>

#### returns 83 for S

- returns 83 for S
- Verify: returns 83 for S
   - Expected: char_code_inline("S") equals `83`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 83 for S")
step("Verify: returns 83 for S")
expect(char_code_inline("S")).to_equal(83)
```

</details>

#### returns 84 for T

- returns 84 for T
- Verify: returns 84 for T
   - Expected: char_code_inline("T") equals `84`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 84 for T")
step("Verify: returns 84 for T")
expect(char_code_inline("T")).to_equal(84)
```

</details>

#### returns 85 for U

- returns 85 for U
- Verify: returns 85 for U
   - Expected: char_code_inline("U") equals `85`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 85 for U")
step("Verify: returns 85 for U")
expect(char_code_inline("U")).to_equal(85)
```

</details>

#### returns 86 for V

- returns 86 for V
- Verify: returns 86 for V
   - Expected: char_code_inline("V") equals `86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 86 for V")
step("Verify: returns 86 for V")
expect(char_code_inline("V")).to_equal(86)
```

</details>

#### returns 87 for W

- returns 87 for W
- Verify: returns 87 for W
   - Expected: char_code_inline("W") equals `87`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 87 for W")
step("Verify: returns 87 for W")
expect(char_code_inline("W")).to_equal(87)
```

</details>

#### returns 88 for X

- returns 88 for X
- Verify: returns 88 for X
   - Expected: char_code_inline("X") equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 88 for X")
step("Verify: returns 88 for X")
expect(char_code_inline("X")).to_equal(88)
```

</details>

#### returns 89 for Y

- returns 89 for Y
- Verify: returns 89 for Y
   - Expected: char_code_inline("Y") equals `89`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 89 for Y")
step("Verify: returns 89 for Y")
expect(char_code_inline("Y")).to_equal(89)
```

</details>

### string_core - char_code_inline exhaustive lowercase

#### lowercase b through l

#### returns 98 for b

- returns 98 for b
- Verify: returns 98 for b
   - Expected: char_code_inline("b") equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 98 for b")
step("Verify: returns 98 for b")
expect(char_code_inline("b")).to_equal(98)
```

</details>

#### returns 99 for c

- returns 99 for c
- Verify: returns 99 for c
   - Expected: char_code_inline("c") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 99 for c")
step("Verify: returns 99 for c")
expect(char_code_inline("c")).to_equal(99)
```

</details>

#### returns 100 for d

- returns 100 for d
- Verify: returns 100 for d
   - Expected: char_code_inline("d") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 100 for d")
step("Verify: returns 100 for d")
expect(char_code_inline("d")).to_equal(100)
```

</details>

#### returns 101 for e

- returns 101 for e
- Verify: returns 101 for e
   - Expected: char_code_inline("e") equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 101 for e")
step("Verify: returns 101 for e")
expect(char_code_inline("e")).to_equal(101)
```

</details>

#### returns 102 for f

- returns 102 for f
- Verify: returns 102 for f
   - Expected: char_code_inline("f") equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 102 for f")
step("Verify: returns 102 for f")
expect(char_code_inline("f")).to_equal(102)
```

</details>

#### returns 103 for g

- returns 103 for g
- Verify: returns 103 for g
   - Expected: char_code_inline("g") equals `103`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 103 for g")
step("Verify: returns 103 for g")
expect(char_code_inline("g")).to_equal(103)
```

</details>

#### returns 104 for h

- returns 104 for h
- Verify: returns 104 for h
   - Expected: char_code_inline("h") equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 104 for h")
step("Verify: returns 104 for h")
expect(char_code_inline("h")).to_equal(104)
```

</details>

#### returns 105 for i

- returns 105 for i
- Verify: returns 105 for i
   - Expected: char_code_inline("i") equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 105 for i")
step("Verify: returns 105 for i")
expect(char_code_inline("i")).to_equal(105)
```

</details>

#### returns 106 for j

- returns 106 for j
- Verify: returns 106 for j
   - Expected: char_code_inline("j") equals `106`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 106 for j")
step("Verify: returns 106 for j")
expect(char_code_inline("j")).to_equal(106)
```

</details>

#### returns 107 for k

- returns 107 for k
- Verify: returns 107 for k
   - Expected: char_code_inline("k") equals `107`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 107 for k")
step("Verify: returns 107 for k")
expect(char_code_inline("k")).to_equal(107)
```

</details>

#### returns 108 for l

- returns 108 for l
- Verify: returns 108 for l
   - Expected: char_code_inline("l") equals `108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 108 for l")
step("Verify: returns 108 for l")
expect(char_code_inline("l")).to_equal(108)
```

</details>

#### lowercase n through y

#### returns 110 for n

- returns 110 for n
- Verify: returns 110 for n
   - Expected: char_code_inline("n") equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 110 for n")
step("Verify: returns 110 for n")
expect(char_code_inline("n")).to_equal(110)
```

</details>

#### returns 111 for o

- returns 111 for o
- Verify: returns 111 for o
   - Expected: char_code_inline("o") equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 111 for o")
step("Verify: returns 111 for o")
expect(char_code_inline("o")).to_equal(111)
```

</details>

#### returns 112 for p

- returns 112 for p
- Verify: returns 112 for p
   - Expected: char_code_inline("p") equals `112`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 112 for p")
step("Verify: returns 112 for p")
expect(char_code_inline("p")).to_equal(112)
```

</details>

#### returns 113 for q

- returns 113 for q
- Verify: returns 113 for q
   - Expected: char_code_inline("q") equals `113`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 113 for q")
step("Verify: returns 113 for q")
expect(char_code_inline("q")).to_equal(113)
```

</details>

#### returns 114 for r

- returns 114 for r
- Verify: returns 114 for r
   - Expected: char_code_inline("r") equals `114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 114 for r")
step("Verify: returns 114 for r")
expect(char_code_inline("r")).to_equal(114)
```

</details>

#### returns 115 for s

- returns 115 for s
- Verify: returns 115 for s
   - Expected: char_code_inline("s") equals `115`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 115 for s")
step("Verify: returns 115 for s")
expect(char_code_inline("s")).to_equal(115)
```

</details>

#### returns 116 for t

- returns 116 for t
- Verify: returns 116 for t
   - Expected: char_code_inline("t") equals `116`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 116 for t")
step("Verify: returns 116 for t")
expect(char_code_inline("t")).to_equal(116)
```

</details>

#### returns 117 for u

- returns 117 for u
- Verify: returns 117 for u
   - Expected: char_code_inline("u") equals `117`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 117 for u")
step("Verify: returns 117 for u")
expect(char_code_inline("u")).to_equal(117)
```

</details>

#### returns 118 for v

- returns 118 for v
- Verify: returns 118 for v
   - Expected: char_code_inline("v") equals `118`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 118 for v")
step("Verify: returns 118 for v")
expect(char_code_inline("v")).to_equal(118)
```

</details>

#### returns 119 for w

- returns 119 for w
- Verify: returns 119 for w
   - Expected: char_code_inline("w") equals `119`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 119 for w")
step("Verify: returns 119 for w")
expect(char_code_inline("w")).to_equal(119)
```

</details>

#### returns 120 for x

- returns 120 for x
- Verify: returns 120 for x
   - Expected: char_code_inline("x") equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 120 for x")
step("Verify: returns 120 for x")
expect(char_code_inline("x")).to_equal(120)
```

</details>

#### returns 121 for y

- returns 121 for y
- Verify: returns 121 for y
   - Expected: char_code_inline("y") equals `121`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 121 for y")
step("Verify: returns 121 for y")
expect(char_code_inline("y")).to_equal(121)
```

</details>

### string_core - char_from_code_inline exhaustive digits

#### all digit codes

#### returns 1 for 49

- returns 1 for 49
- Verify: returns 1 for 49
   - Expected: char_from_code_inline(49) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 1 for 49")
step("Verify: returns 1 for 49")
expect(char_from_code_inline(49)).to_equal("1")
```

</details>

#### returns 2 for 50

- returns 2 for 50
- Verify: returns 2 for 50
   - Expected: char_from_code_inline(50) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 2 for 50")
step("Verify: returns 2 for 50")
expect(char_from_code_inline(50)).to_equal("2")
```

</details>

#### returns 3 for 51

- returns 3 for 51
- Verify: returns 3 for 51
   - Expected: char_from_code_inline(51) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 3 for 51")
step("Verify: returns 3 for 51")
expect(char_from_code_inline(51)).to_equal("3")
```

</details>

#### returns 4 for 52

- returns 4 for 52
- Verify: returns 4 for 52
   - Expected: char_from_code_inline(52) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 4 for 52")
step("Verify: returns 4 for 52")
expect(char_from_code_inline(52)).to_equal("4")
```

</details>

#### returns 6 for 54

- returns 6 for 54
- Verify: returns 6 for 54
   - Expected: char_from_code_inline(54) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 6 for 54")
step("Verify: returns 6 for 54")
expect(char_from_code_inline(54)).to_equal("6")
```

</details>

#### returns 7 for 55

- returns 7 for 55
- Verify: returns 7 for 55
   - Expected: char_from_code_inline(55) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 7 for 55")
step("Verify: returns 7 for 55")
expect(char_from_code_inline(55)).to_equal("7")
```

</details>

#### returns 8 for 56

- returns 8 for 56
- Verify: returns 8 for 56
   - Expected: char_from_code_inline(56) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 8 for 56")
step("Verify: returns 8 for 56")
expect(char_from_code_inline(56)).to_equal("8")
```

</details>

### string_core - char_from_code_inline exhaustive uppercase

#### uppercase codes B through L

#### returns B for 66

- returns B for 66
- Verify: returns B for 66
   - Expected: char_from_code_inline(66) equals `B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns B for 66")
step("Verify: returns B for 66")
expect(char_from_code_inline(66)).to_equal("B")
```

</details>

#### returns C for 67

- returns C for 67
- Verify: returns C for 67
   - Expected: char_from_code_inline(67) equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns C for 67")
step("Verify: returns C for 67")
expect(char_from_code_inline(67)).to_equal("C")
```

</details>

#### returns D for 68

- returns D for 68
- Verify: returns D for 68
   - Expected: char_from_code_inline(68) equals `D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns D for 68")
step("Verify: returns D for 68")
expect(char_from_code_inline(68)).to_equal("D")
```

</details>

#### returns E for 69

- returns E for 69
- Verify: returns E for 69
   - Expected: char_from_code_inline(69) equals `E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns E for 69")
step("Verify: returns E for 69")
expect(char_from_code_inline(69)).to_equal("E")
```

</details>

#### returns F for 70

- returns F for 70
- Verify: returns F for 70
   - Expected: char_from_code_inline(70) equals `F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns F for 70")
step("Verify: returns F for 70")
expect(char_from_code_inline(70)).to_equal("F")
```

</details>

#### returns G for 71

- returns G for 71
- Verify: returns G for 71
   - Expected: char_from_code_inline(71) equals `G`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns G for 71")
step("Verify: returns G for 71")
expect(char_from_code_inline(71)).to_equal("G")
```

</details>

#### returns H for 72

- returns H for 72
- Verify: returns H for 72
   - Expected: char_from_code_inline(72) equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns H for 72")
step("Verify: returns H for 72")
expect(char_from_code_inline(72)).to_equal("H")
```

</details>

#### returns I for 73

- returns I for 73
- Verify: returns I for 73
   - Expected: char_from_code_inline(73) equals `I`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns I for 73")
step("Verify: returns I for 73")
expect(char_from_code_inline(73)).to_equal("I")
```

</details>

#### returns J for 74

- returns J for 74
- Verify: returns J for 74
   - Expected: char_from_code_inline(74) equals `J`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns J for 74")
step("Verify: returns J for 74")
expect(char_from_code_inline(74)).to_equal("J")
```

</details>

#### returns K for 75

- returns K for 75
- Verify: returns K for 75
   - Expected: char_from_code_inline(75) equals `K`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns K for 75")
step("Verify: returns K for 75")
expect(char_from_code_inline(75)).to_equal("K")
```

</details>

#### returns L for 76

- returns L for 76
- Verify: returns L for 76
   - Expected: char_from_code_inline(76) equals `L`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns L for 76")
step("Verify: returns L for 76")
expect(char_from_code_inline(76)).to_equal("L")
```

</details>

#### uppercase codes N through Y

#### returns N for 78

- returns N for 78
- Verify: returns N for 78
   - Expected: char_from_code_inline(78) equals `N`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns N for 78")
step("Verify: returns N for 78")
expect(char_from_code_inline(78)).to_equal("N")
```

</details>

#### returns O for 79

- returns O for 79
- Verify: returns O for 79
   - Expected: char_from_code_inline(79) equals `O`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns O for 79")
step("Verify: returns O for 79")
expect(char_from_code_inline(79)).to_equal("O")
```

</details>

#### returns P for 80

- returns P for 80
- Verify: returns P for 80
   - Expected: char_from_code_inline(80) equals `P`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns P for 80")
step("Verify: returns P for 80")
expect(char_from_code_inline(80)).to_equal("P")
```

</details>

#### returns Q for 81

- returns Q for 81
- Verify: returns Q for 81
   - Expected: char_from_code_inline(81) equals `Q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Q for 81")
step("Verify: returns Q for 81")
expect(char_from_code_inline(81)).to_equal("Q")
```

</details>

#### returns R for 82

- returns R for 82
- Verify: returns R for 82
   - Expected: char_from_code_inline(82) equals `R`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns R for 82")
step("Verify: returns R for 82")
expect(char_from_code_inline(82)).to_equal("R")
```

</details>

#### returns S for 83

- returns S for 83
- Verify: returns S for 83
   - Expected: char_from_code_inline(83) equals `S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns S for 83")
step("Verify: returns S for 83")
expect(char_from_code_inline(83)).to_equal("S")
```

</details>

#### returns T for 84

- returns T for 84
- Verify: returns T for 84
   - Expected: char_from_code_inline(84) equals `T`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns T for 84")
step("Verify: returns T for 84")
expect(char_from_code_inline(84)).to_equal("T")
```

</details>

#### returns U for 85

- returns U for 85
- Verify: returns U for 85
   - Expected: char_from_code_inline(85) equals `U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns U for 85")
step("Verify: returns U for 85")
expect(char_from_code_inline(85)).to_equal("U")
```

</details>

#### returns V for 86

- returns V for 86
- Verify: returns V for 86
   - Expected: char_from_code_inline(86) equals `V`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns V for 86")
step("Verify: returns V for 86")
expect(char_from_code_inline(86)).to_equal("V")
```

</details>

#### returns W for 87

- returns W for 87
- Verify: returns W for 87
   - Expected: char_from_code_inline(87) equals `W`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns W for 87")
step("Verify: returns W for 87")
expect(char_from_code_inline(87)).to_equal("W")
```

</details>

#### returns X for 88

- returns X for 88
- Verify: returns X for 88
   - Expected: char_from_code_inline(88) equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns X for 88")
step("Verify: returns X for 88")
expect(char_from_code_inline(88)).to_equal("X")
```

</details>

#### returns Y for 89

- returns Y for 89
- Verify: returns Y for 89
   - Expected: char_from_code_inline(89) equals `Y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Y for 89")
step("Verify: returns Y for 89")
expect(char_from_code_inline(89)).to_equal("Y")
```

</details>

### string_core - char_from_code_inline exhaustive lowercase

#### lowercase codes b through l

#### returns b for 98

- returns b for 98
- Verify: returns b for 98
   - Expected: char_from_code_inline(98) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns b for 98")
step("Verify: returns b for 98")
expect(char_from_code_inline(98)).to_equal("b")
```

</details>

#### returns c for 99

- returns c for 99
- Verify: returns c for 99
   - Expected: char_from_code_inline(99) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns c for 99")
step("Verify: returns c for 99")
expect(char_from_code_inline(99)).to_equal("c")
```

</details>

#### returns d for 100

- returns d for 100
- Verify: returns d for 100
   - Expected: char_from_code_inline(100) equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns d for 100")
step("Verify: returns d for 100")
expect(char_from_code_inline(100)).to_equal("d")
```

</details>

#### returns e for 101

- returns e for 101
- Verify: returns e for 101
   - Expected: char_from_code_inline(101) equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns e for 101")
step("Verify: returns e for 101")
expect(char_from_code_inline(101)).to_equal("e")
```

</details>

#### returns f for 102

- returns f for 102
- Verify: returns f for 102
   - Expected: char_from_code_inline(102) equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns f for 102")
step("Verify: returns f for 102")
expect(char_from_code_inline(102)).to_equal("f")
```

</details>

#### returns g for 103

- returns g for 103
- Verify: returns g for 103
   - Expected: char_from_code_inline(103) equals `g`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns g for 103")
step("Verify: returns g for 103")
expect(char_from_code_inline(103)).to_equal("g")
```

</details>

#### returns h for 104

- returns h for 104
- Verify: returns h for 104
   - Expected: char_from_code_inline(104) equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns h for 104")
step("Verify: returns h for 104")
expect(char_from_code_inline(104)).to_equal("h")
```

</details>

#### returns i for 105

- returns i for 105
- Verify: returns i for 105
   - Expected: char_from_code_inline(105) equals `i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns i for 105")
step("Verify: returns i for 105")
expect(char_from_code_inline(105)).to_equal("i")
```

</details>

#### returns j for 106

- returns j for 106
- Verify: returns j for 106
   - Expected: char_from_code_inline(106) equals `j`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns j for 106")
step("Verify: returns j for 106")
expect(char_from_code_inline(106)).to_equal("j")
```

</details>

#### returns k for 107

- returns k for 107
- Verify: returns k for 107
   - Expected: char_from_code_inline(107) equals `k`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns k for 107")
step("Verify: returns k for 107")
expect(char_from_code_inline(107)).to_equal("k")
```

</details>

#### returns l for 108

- returns l for 108
- Verify: returns l for 108
   - Expected: char_from_code_inline(108) equals `l`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns l for 108")
step("Verify: returns l for 108")
expect(char_from_code_inline(108)).to_equal("l")
```

</details>

#### lowercase codes n through y

#### returns n for 110

- returns n for 110
- Verify: returns n for 110
   - Expected: char_from_code_inline(110) equals `n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns n for 110")
step("Verify: returns n for 110")
expect(char_from_code_inline(110)).to_equal("n")
```

</details>

#### returns o for 111

- returns o for 111
- Verify: returns o for 111
   - Expected: char_from_code_inline(111) equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns o for 111")
step("Verify: returns o for 111")
expect(char_from_code_inline(111)).to_equal("o")
```

</details>

#### returns p for 112

- returns p for 112
- Verify: returns p for 112
   - Expected: char_from_code_inline(112) equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns p for 112")
step("Verify: returns p for 112")
expect(char_from_code_inline(112)).to_equal("p")
```

</details>

#### returns q for 113

- returns q for 113
- Verify: returns q for 113
   - Expected: char_from_code_inline(113) equals `q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns q for 113")
step("Verify: returns q for 113")
expect(char_from_code_inline(113)).to_equal("q")
```

</details>

#### returns r for 114

- returns r for 114
- Verify: returns r for 114
   - Expected: char_from_code_inline(114) equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns r for 114")
step("Verify: returns r for 114")
expect(char_from_code_inline(114)).to_equal("r")
```

</details>

#### returns s for 115

- returns s for 115
- Verify: returns s for 115
   - Expected: char_from_code_inline(115) equals `s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns s for 115")
step("Verify: returns s for 115")
expect(char_from_code_inline(115)).to_equal("s")
```

</details>

#### returns t for 116

- returns t for 116
- Verify: returns t for 116
   - Expected: char_from_code_inline(116) equals `t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns t for 116")
step("Verify: returns t for 116")
expect(char_from_code_inline(116)).to_equal("t")
```

</details>

#### returns u for 117

- returns u for 117
- Verify: returns u for 117
   - Expected: char_from_code_inline(117) equals `u`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns u for 117")
step("Verify: returns u for 117")
expect(char_from_code_inline(117)).to_equal("u")
```

</details>

#### returns v for 118

- returns v for 118
- Verify: returns v for 118
   - Expected: char_from_code_inline(118) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns v for 118")
step("Verify: returns v for 118")
expect(char_from_code_inline(118)).to_equal("v")
```

</details>

#### returns w for 119

- returns w for 119
- Verify: returns w for 119
   - Expected: char_from_code_inline(119) equals `w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns w for 119")
step("Verify: returns w for 119")
expect(char_from_code_inline(119)).to_equal("w")
```

</details>

#### returns x for 120

- returns x for 120
- Verify: returns x for 120
   - Expected: char_from_code_inline(120) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns x for 120")
step("Verify: returns x for 120")
expect(char_from_code_inline(120)).to_equal("x")
```

</details>

#### returns y for 121

- returns y for 121
- Verify: returns y for 121
   - Expected: char_from_code_inline(121) equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns y for 121")
step("Verify: returns y for 121")
expect(char_from_code_inline(121)).to_equal("y")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 106 |
| Active scenarios | 106 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc4a1f7564857eb3efd267f6146a514be239eb03e324bc304397f27428bb61c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc4a1f7564857eb3efd267f6146a514be239eb03e324bc304397f27428bb61c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc4a1f7564857eb3efd267f6146a514be239eb03e324bc304397f27428bb61c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/string_core_exhaustive_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_core_exhaustive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/string_core_exhaustive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_core_exhaustive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_core_exhaustive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 53 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/string_core_exhaustive_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 49 for 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_exhaustive_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 50 for 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_exhaustive_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 51 for 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
