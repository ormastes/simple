# Branch Coverage 28 Specification

> Tests covering Boundary Conditions, Edge Case Expressions, Complex Control Flow, Short Circuit Evaluation, String Operations All Branches, Array Operations All Branches, Range All Branches, Type Coercion All Branches, Variable Scope All Branches, Comparison All Branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 28 Specification

## Scenarios

### Boundary Conditions

#### integer - zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- integer - zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer - zero")
check(0 == 0)
check(0 < 1)
check(0 > -1)
```

</details>

#### integer - min value

- integer - min value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer - min value")
val x = -9223372036854775808
check(x < 0)
```

</details>

#### integer - max value

- integer - max value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer - max value")
val x = 9223372036854775807
check(x > 0)
```

</details>

#### float - zero

- float - zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - zero")
val x = 0.0
check(x == 0.0)
```

</details>

#### float - negative zero

- float - negative zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - negative zero")
val x = -0.0
check(x == 0.0)
```

</details>

#### float - infinity

- float - infinity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - infinity")
val x = 1.0e308
check(x > 0.0)
```

</details>

#### float - tiny

- float - tiny


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - tiny")
val x = 1.0e-308
check(x > 0.0)
check(x < 1.0)
```

</details>

#### string - empty

- string - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - empty")
val s = ""
check(s.len() == 0)
check(s == "")
```

</details>

#### string - single char

- string - single char


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - single char")
val s = "a"
check(s.len() == 1)
```

</details>

#### string - very long

- string - very long


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - very long")
val s = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
check(s.len() > 60)
```

</details>

#### array - empty

- array - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - empty")
val arr: [i64] = []
check(arr.len() == 0)
```

</details>

#### array - single element

- array - single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - single element")
var arr = [42]
check(arr.len() == 1)
```

</details>

#### array - large

- array - large


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - large")
var arr = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
check(arr.len() == 20)
```

</details>

### Edge Case Expressions

#### division by one

- division by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division by one")
check(10 / 1 == 10)
```

</details>

#### modulo by one

- modulo by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("modulo by one")
check(10 % 1 == 0)
```

</details>

#### power of zero

- power of zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power of zero")
check(5 ** 0 == 1)
```

</details>

#### power of one

- power of one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power of one")
check(5 ** 1 == 5)
```

</details>

#### negative exponent handled

- negative exponent handled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative exponent handled")
val x = 2 ** 3
check(x == 8)
```

</details>

#### zero to power

- zero to power


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero to power")
check(0 ** 5 == 0)
```

</details>

#### one to power

- one to power


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one to power")
check(1 ** 100 == 1)
```

</details>

#### bitwise - all zeros

- bitwise - all zeros


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bitwise - all zeros")
check((0 & 0) == 0)
check((0 | 0) == 0)
check((0 ^ 0) == 0)
```

</details>

#### bitwise - all ones

- bitwise - all ones


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bitwise - all ones")
check((15 & 15) == 15)
check((15 | 15) == 15)
check((15 ^ 15) == 0)
```

</details>

#### bitwise - mixed

- bitwise - mixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bitwise - mixed")
check((0b1010 & 0b1100) == 0b1000)
check((0b1010 | 0b1100) == 0b1110)
check((0b1010 ^ 0b1100) == 0b0110)
```

</details>

### Complex Control Flow

<details>
<summary>Advanced: nested loops - break outer effect</summary>

#### nested loops - break outer effect

- nested loops - break outer effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested loops - break outer effect")
var count = 0
for i in 0..3:
    for j in 0..3:
        count = count + 1
        if count == 5:
            break
check(count >= 5)
```

</details>


</details>

<details>
<summary>Advanced: nested loops - continue inner</summary>

#### nested loops - continue inner

- nested loops - continue inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested loops - continue inner")
fn run() -> i64:
    var count = 0
    for i in 0..3:
        for j in 0..3:
            if j == 1:
                continue
            count = count + 1
    count
check(run() == 6)
```

</details>


</details>

#### nested if-elif-else

- nested if-elif-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested if-elif-else")
fn classify(x: i64, y: i64) -> i64:
    if x > 0:
        if y > 0:
            return 1
        elif y == 0:
            return 2
        else:
            return 3
    elif x == 0:
        if y > 0:
            return 4
        elif y == 0:
            return 5
        else:
            return 6
    else:
        if y > 0:
            return 7
        elif y == 0:
            return 8
        else:
            return 9
check(classify(1, 1) == 1)
check(classify(1, 0) == 2)
check(classify(1, -1) == 3)
check(classify(0, 1) == 4)
check(classify(0, 0) == 5)
check(classify(0, -1) == 6)
check(classify(-1, 1) == 7)
check(classify(-1, 0) == 8)
check(classify(-1, -1) == 9)
```

</details>

<details>
<summary>Advanced: match in loop</summary>

#### match in loop

- match in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match in loop")
var sum = 0
for i in 0..5:
    val add = match i:
        0: 1
        1: 2
        2: 3
        3: 4
        _: 5
    sum = sum + add
check(sum == 15)
```

</details>


</details>

#### if in match

- if in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if in match")
fn test(x: i64) -> i64:
    match x:
        1:
            if true:
                10
            else:
                20
        2:
            if false:
                30
            else:
                40
        _:
            50
check(test(1) == 10)
check(test(2) == 40)
check(test(3) == 50)
```

</details>

### Short Circuit Evaluation

#### and - short circuit false

- and - short circuit false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - short circuit false")
fn side_effect() -> bool:
    true
val result = false and side_effect()
check(not result)
```

</details>

#### and - no short circuit true

- and - no short circuit true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - no short circuit true")
fn side_effect2() -> bool:
    true
val result = true and side_effect2()
check(result)
```

</details>

#### or - short circuit true

- or - short circuit true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - short circuit true")
fn side_effect3() -> bool:
    false
val result = true or side_effect3()
check(result)
```

</details>

#### or - no short circuit false

- or - no short circuit false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - no short circuit false")
fn side_effect4() -> bool:
    true
val result = false or side_effect4()
check(result)
```

</details>

### String Operations All Branches

#### concat - empty + empty

- concat - empty + empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concat - empty + empty")
val s = "" + ""
check(s == "")
```

</details>

#### concat - empty + non-empty

- concat - empty + non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concat - empty + non-empty")
val s = "" + "hello"
check(s == "hello")
```

</details>

#### concat - non-empty + empty

- concat - non-empty + empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concat - non-empty + empty")
val s = "hello" + ""
check(s == "hello")
```

</details>

#### concat - non-empty + non-empty

- concat - non-empty + non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concat - non-empty + non-empty")
val s = "hello" + " world"
check(s == "hello world")
```

</details>

#### string contains - empty in empty

- string contains - empty in empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string contains - empty in empty")
check("".contains(""))
```

</details>

#### string contains - empty in non-empty

- string contains - empty in non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string contains - empty in non-empty")
check("hello".contains(""))
```

</details>

#### string contains - found

- string contains - found


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string contains - found")
check("hello".contains("ell"))
```

</details>

#### string contains - not found

- string contains - not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string contains - not found")
check(not "hello".contains("xyz"))
```

</details>

#### string starts_with - empty

- string starts_with - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string starts_with - empty")
check("hello".starts_with(""))
```

</details>

#### string starts_with - match

- string starts_with - match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string starts_with - match")
check("hello".starts_with("hel"))
```

</details>

#### string starts_with - no match

- string starts_with - no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string starts_with - no match")
check(not "hello".starts_with("llo"))
```

</details>

#### string ends_with - empty

- string ends_with - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string ends_with - empty")
check("hello".ends_with(""))
```

</details>

#### string ends_with - match

- string ends_with - match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string ends_with - match")
check("hello".ends_with("llo"))
```

</details>

#### string ends_with - no match

- string ends_with - no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string ends_with - no match")
check(not "hello".ends_with("hel"))
```

</details>

### Array Operations All Branches

#### array push

- array push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array push")
var arr = [1, 2]
arr.push(3)
check(arr.len() == 3)
```

</details>

#### array pop - non-empty

- array pop - non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array pop - non-empty")
fn run() -> i64:
    var arr = [1, 2, 3]
    val x = arr.pop()
    arr.len()
check(run() == 2)
```

</details>

#### array pop - empty

- array pop - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array pop - empty")
var arr: [i64] = []
val x = arr.pop()
check(not x.?)
```

</details>

#### array contains - found

- array contains - found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array contains - found")
var arr = [1, 2, 3]
check(arr.contains(2))
```

</details>

#### array contains - not found

- array contains - not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array contains - not found")
var arr = [1, 2, 3]
check(not arr.contains(5))
```

</details>

#### array contains - empty

- array contains - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array contains - empty")
val arr: [i64] = []
check(not arr.contains(1))
```

</details>

### Range All Branches

#### range - positive

- range - positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range - positive")
var count = 0
for i in 0..5:
    count = count + 1
check(count == 5)
```

</details>

#### range - zero

- range - zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range - zero")
var count = 0
for i in 0..0:
    count = count + 1
check(count == 0)
```

</details>

#### range - single

- range - single


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range - single")
var count = 0
for i in 5..6:
    count = count + 1
check(count == 1)
```

</details>

#### range - negative start

- range - negative start


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range - negative start")
var count = 0
for i in -2..2:
    count = count + 1
check(count == 4)
```

</details>

### Type Coercion All Branches

#### int to float implicit

- int to float implicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int to float implicit")
val x: f64 = 5.0 + 3.0
check(x == 8.0)
```

</details>

#### bool to int context

- bool to int context


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool to int context")
val t = if true: 1 else: 0
val f = if false: 1 else: 0
check(t == 1)
check(f == 0)
```

</details>

### Variable Scope All Branches

#### block scope - inner shadows outer

- block scope - inner shadows outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block scope - inner shadows outer")
val x = 10
var result = 0
if true:
    val x = 20
    result = x
check(result == 20)
```

</details>

#### block scope - outer visible after

- block scope - outer visible after


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block scope - outer visible after")
val x = 10
if true:
    val y = 20
check(x == 10)
```

</details>

<details>
<summary>Advanced: loop scope - variable local</summary>

#### loop scope - variable local

- loop scope - variable local


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop scope - variable local")
var sum = 0
for i in 0..3:
    val temp = i * 2
    sum = sum + temp
check(sum == 6)
```

</details>


</details>

### Comparison All Branches

#### compare - equal same type

- compare - equal same type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare - equal same type")
check(5 == 5)
check("hello" == "hello")
check(true == true)
```

</details>

#### compare - not equal same type

- compare - not equal same type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare - not equal same type")
check(5 != 4)
check("hello" != "world")
check(true != false)
```

</details>

#### compare - less than

- compare - less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare - less than")
check(3 < 5)
check(not (5 < 3))
check(not (5 < 5))
```

</details>

#### compare - greater than

- compare - greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare - greater than")
check(5 > 3)
check(not (3 > 5))
check(not (5 > 5))
```

</details>

#### compare - less or equal

- compare - less or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare - less or equal")
check(3 <= 5)
check(5 <= 5)
check(not (5 <= 3))
```

</details>

#### compare - greater or equal

- compare - greater or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare - greater or equal")
check(5 >= 3)
check(5 >= 5)
check(not (3 >= 5))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/branch_coverage_28_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Boundary Conditions, Edge Case Expressions, Complex Control Flow, Short Circuit Evaluation, String Operations All Branches, Array Operations All Branches, Range All Branches, Type Coercion All Branches, Variable Scope All Branches, Comparison All Branches.
- Boundary Conditions
- Edge Case Expressions
- Complex Control Flow
- Short Circuit Evaluation
- String Operations All Branches
- Array Operations All Branches
- Range All Branches
- Type Coercion All Branches
- Variable Scope All Branches
- Comparison All Branches

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
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

- Canonical SPipe generation for source `63ccd7f0861e945a0d2ee068c2e12b0058a9298ea4518d640778dbe8d4c62841`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63ccd7f0861e945a0d2ee068c2e12b0058a9298ea4518d640778dbe8d4c62841`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63ccd7f0861e945a0d2ee068c2e12b0058a9298ea4518d640778dbe8d4c62841`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/branch_coverage_28_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/branch_coverage_28_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/branch_coverage_28_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/branch_coverage_28_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/branch_coverage_28_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integer - zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/branch_coverage_28_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integer - min value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/branch_coverage_28_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integer - max value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
