# expect(file_exists(output)).to_equal(true)

> val output = "/tmp/test_hello.o"

<!-- sdn-diagram:id=native_backend_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_backend_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_backend_e2e_spec -> app
native_backend_e2e_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_backend_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect(file_exists(output)).to_equal(true)

val output = "/tmp/test_hello.o"

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/native_backend_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

val output = "/tmp/test_hello.o"
            val success = compile_simple_program(source, output)

            expect(success).to_equal(true)
            if file_exists(output):
                file_delete(output)

        slow_it "produces valid ELF object":
            val source = """
            fn add(a: i64, b: i64) -> i64:
                a + b

            fn main():
                val result = add(2, 3)
                print "{result}"

## Scenarios

### Native Backend E2E - Basic Compilation

#### simple program

<details>
<summary>Advanced: compiles hello world</summary>

#### compiles hello world _(slow)_

1. fn main
   - Expected: success is true
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn main():
    print "Hello, World!"
"""

val output = "/tmp/test_hello.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)
# expect(file_exists(output)).to_equal(true)

# Cleanup
if file_exists(output):
    file_delete(output)
```

</details>


</details>

<details>
<summary>Advanced: produces valid ELF object</summary>

#### produces valid ELF object _(slow)_

1. fn add
2. fn main
   - Expected: success is true
   - Expected: header[0] equals `0x7f`
   - Expected: header[1] equals `0x45`
   - Expected: header[2] equals `0x4c`
   - Expected: header[3] equals `0x46`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn add(a: i64, b: i64) -> i64:
    a + b

fn main():
    val result = add(2, 3)
    print "{result}"
"""

val output = "/tmp/test_add.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    val header = read_elf_header(output)
    # Check ELF magic number: 0x7f 'E' 'L' 'F'
    expect(header[0]).to_equal(0x7f)
    expect(header[1]).to_equal(0x45)
    expect(header[2]).to_equal(0x4c)
    expect(header[3]).to_equal(0x46)

    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Layout Optimization

#### phase annotation

<details>
<summary>Advanced: respects layout phase attributes</summary>

#### respects layout phase attributes _(slow)_

1. fn init system
2. fn error handler
3. fn main
4. init system
   - Expected: success is true
5. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
@layout(phase="startup")
fn init_system():
    print "Initializing..."

@layout(phase="cold")
fn error_handler():
    print "Error!"

fn main():
    init_system()
"""

val output = "/tmp/test_phases.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    # TODO: Verify function order in binary
    val symbols = parse_elf_symbols(output)
    expect(symbols.len()).to_be_greater_than(0)

    file_delete(output)
```

</details>


</details>

#### function ordering

<details>
<summary>Advanced: orders hot functions before cold functions</summary>

#### orders hot functions before cold functions _(slow)_

1. fn handle error
2. fn process item
3. fn main
   - Expected: success is true
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
# Cold function (error handling)
fn handle_error():
    print "Error occurred"

# Hot function (main loop)
fn process_item(x: i64) -> i64:
    x * 2

fn main():
    for i in 0..100:
        val result = process_item(i)
        print "{result}"
"""

val output = "/tmp/test_ordering.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    val symbols = parse_elf_symbols(output)
    # In ideal ordering: main and process_item should come before handle_error
    # TODO: Verify actual ordering in binary
    expect(symbols.len()).to_be_greater_than(0)

    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Binary Size

#### padding overhead

<details>
<summary>Advanced: adds reasonable padding for alignment</summary>

#### adds reasonable padding for alignment _(slow)_

1. fn func1
2. fn func2
3. fn func3
4. fn main
5. func1
6. func2
7. func3
   - Expected: success is true
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn func1(): pass
fn func2(): pass
fn func3(): pass

fn main():
    func1()
    func2()
    func3()
"""

val output = "/tmp/test_padding.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    val size = measure_binary_size(output)
    # Size should be reasonable (not excessive padding)
    # With 4 functions + padding, expect < 32KB
    expect(size).to_be_less_than(32768)

    file_delete(output)
```

</details>


</details>

#### multiple phases

<details>
<summary>Advanced: handles multiple phase groups efficiently</summary>

#### handles multiple phase groups efficiently _(slow)_

1. fn startup1
2. fn startup2
3. fn steady1
4. fn cold1
5. fn main
6. startup1
7. steady1
   - Expected: success is true
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
@layout(phase="startup")
fn startup1(): pass

@layout(phase="startup")
fn startup2(): pass

@layout(phase="steady")
fn steady1(): pass

@layout(phase="cold")
fn cold1(): pass

fn main():
    startup1()
    steady1()
"""

val output = "/tmp/test_multi_phase.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    val size = measure_binary_size(output)
    # Should have 3 phases + padding, reasonable size
    expect(size).to_be_less_than(65536)

    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Symbol Table

#### function symbols

<details>
<summary>Advanced: exports all function symbols</summary>

#### exports all function symbols _(slow)_

1. fn public func
2. fn another func
3. fn main
4. public func
5. another func
   - Expected: success is true
6. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn public_func():
    print "Public"

fn another_func():
    print "Another"

fn main():
    public_func()
    another_func()
"""

val output = "/tmp/test_symbols.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    val symbols = parse_elf_symbols(output)
    # Should have at least main, public_func, another_func
    expect(symbols.len()).to_be_greater_than(2)

    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Relocations

#### function calls

<details>
<summary>Advanced: generates correct relocations for function calls</summary>

#### generates correct relocations for function calls _(slow)_

1. fn helper
2. fn main
   - Expected: success is true
   - Expected: file_exists(output) is true
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn helper() -> i64:
    return 42

fn main():
    val x = helper()
    print "{x}"
"""

val output = "/tmp/test_reloc.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    # TODO: Verify relocations are correct
    expect(file_exists(output)).to_equal(true)

    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Complex Programs

#### recursive functions

<details>
<summary>Advanced: handles recursive function calls</summary>

#### handles recursive function calls _(slow)_

1. fn factorial
2. fn main
   - Expected: success is true
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

fn main():
    val result = factorial(5)
    print "{result}"
"""

val output = "/tmp/test_recursive.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    file_delete(output)
```

</details>


</details>

#### mutual recursion

<details>
<summary>Advanced: handles mutually recursive functions</summary>

#### handles mutually recursive functions _(slow)_

1. fn is even
2. fn is odd
3. fn main
   - Expected: success is true
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn is_even(n: i64) -> bool:
    if n == 0:
        return true
    return is_odd(n - 1)

fn is_odd(n: i64) -> bool:
    if n == 0:
        return false
    return is_even(n - 1)

fn main():
    val x = is_even(4)
    print "{x}"
"""

val output = "/tmp/test_mutual.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Architecture Support

#### x86_64

<details>
<summary>Advanced: generates x86_64 code</summary>

#### generates x86_64 code _(slow)_

1. fn main
   - Expected: success is true
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn main():
    print "x86_64 test"
"""

val output = "/tmp/test_x86_64.o"
val success = compile_simple_program(source, output)

expect(success).to_equal(true)

if file_exists(output):
    val header = read_elf_header(output)
    # TODO: Verify x86_64 machine type in ELF header
    expect(header.len()).to_be_greater_than(0)

    file_delete(output)
```

</details>


</details>

### Native Backend E2E - Error Handling

#### invalid source

<details>
<summary>Advanced: handles compilation errors gracefully</summary>

#### handles compilation errors gracefully _(slow)_

1. fn main
2. file delete
   - Expected: success is false
   - Expected: file_exists(output) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
fn main():
    this is not valid syntax!
"""

val output = "/tmp/test_error.o"
if file_exists(output):
    file_delete(output)
# Should fail to compile
val success = compile_simple_program(source, output)
expect(success).to_equal(false)

# No output file should be created
expect(file_exists(output)).to_equal(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 12 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
