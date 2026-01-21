# Fuzzing and Mutation Testing Libraries for Simple

**Research Date:** 2026-01-21
**Status:** Design Proposal
**Target:** Testing libraries written IN Simple language

## Executive Summary

Design for two lightweight testing libraries:
1. **`std.fuzz`** - Property-based fuzzing for Simple programs
2. **`std.mutate`** - Mutation testing to validate test quality

Both leverage existing `std.random` and `std.spec` infrastructure.

## 1. Fuzzing Library: `std.fuzz`

### 1.1 Design Goals

- **Lightweight:** ~300 LOC, single file
- **No external deps:** Uses `std.random` only
- **Simple API:** `fuzz(fn, generator, iterations)`
- **Property-based:** Similar to QuickCheck/Hypothesis

### 1.2 API Design

```simple
# simple/std_lib/src/testing/fuzz.spl

import std.random
import std.spec

# Generator - produces random test inputs
trait Generator<T>:
    fn generate(rng: RandomState) -> T

# Built-in generators
struct IntGen:
    min: i32
    max: i32

impl Generator<i32> for IntGen:
    fn generate(rng: RandomState) -> i32:
        rng.next() % (self.max - self.min + 1) + self.min

struct TextGen:
    min_len: i32
    max_len: i32

impl Generator<text> for TextGen:
    fn generate(rng: RandomState) -> text:
        val len = rng.next() % (self.max_len - self.min_len + 1) + self.min_len
        var result = ""
        for _ in 0..len:
            # Printable ASCII (32-126)
            val ch = (rng.next() % 95 + 32) as char
            result = result + ch
        result

struct ListGen<T>:
    item_gen: Generator<T>
    min_len: i32
    max_len: i32

impl<T> Generator<List<T>> for ListGen<T>:
    fn generate(rng: RandomState) -> List<T>:
        val len = rng.next() % (self.max_len - self.min_len + 1) + self.min_len
        var result = []
        for _ in 0..len:
            result.append(self.item_gen.generate(rng))
        result

# Shrinking - simplify failing inputs
trait Shrinker<T>:
    fn shrink(value: T) -> List<T>

# Fuzz result
enum FuzzResult:
    Pass(iterations: i32)
    Fail(input: any, error: text, iterations: i32)
    Crash(input: any, stack_trace: text)

# Main fuzzing function
pub fn fuzz<T>(
    property: fn(T) -> bool,
    gen: Generator<T>,
    iterations: i32 = 100,
    seed: Option<i32> = None
) -> FuzzResult:
    """
    Run property-based fuzzing.

    Args:
        property: Function that returns true if input is valid
        gen: Generator for random inputs
        iterations: Number of test cases (default 100)
        seed: Optional seed for reproducibility

    Returns:
        FuzzResult with pass/fail status

    Example:
        # Test that reverse(reverse(x)) == x
        fn prop_reverse(xs: List<i32>) -> bool:
            xs.reverse().reverse() == xs

        result = fuzz(prop_reverse, ListGen(IntGen(-100, 100), 0, 50))
        expect result is Pass
    """
    val rng = if seed.is_some():
        RandomState.new(seed.unwrap())
    else:
        RandomState.new((rt_time_now_seconds() * 1000000.0) as i32)

    for i in 0..iterations:
        val input = gen.generate(rng)

        try:
            val passed = property(input)
            if not passed:
                return FuzzResult::Fail(
                    input: input,
                    error: "Property returned false",
                    iterations: i + 1
                )
        catch e:
            return FuzzResult::Crash(
                input: input,
                stack_trace: e.to_string()
            )

    FuzzResult::Pass(iterations: iterations)

# Convenience generators
pub fn int(min: i32 = -1000, max: i32 = 1000) -> IntGen:
    IntGen(min: min, max: max)

pub fn text(min_len: i32 = 0, max_len: i32 = 100) -> TextGen:
    TextGen(min_len: min_len, max_len: max_len)

pub fn list<T>(item_gen: Generator<T>, min_len: i32 = 0, max_len: i32 = 20) -> ListGen<T>:
    ListGen(item_gen: item_gen, min_len: min_len, max_len: max_len)

# Integration with SSpec
pub fn fuzz_spec<T>(
    name: text,
    property: fn(T) -> bool,
    gen: Generator<T>,
    iterations: i32 = 100
):
    """
    Run fuzzing as a spec test.

    Example:
        import std.fuzz

        describe "List operations":
            fuzz_spec("reverse is involution",
                \xs: xs.reverse().reverse() == xs,
                fuzz.list(fuzz.int(), 0, 50),
                iterations: 1000
            )
    """
    it name:
        val result = fuzz(property, gen, iterations)
        match result:
            Pass(_):
                # Success - no assertion needed
                expect true
            Fail(input, error, iters):
                val msg = "Property failed at iteration {iters}\nInput: {input}\nError: {error}"
                expect false, msg
            Crash(input, trace):
                val msg = "Property crashed\nInput: {input}\nTrace: {trace}"
                expect false, msg
```

### 1.3 Usage Examples

**Example 1: String operations**
```simple
import std.fuzz

describe "String operations":
    fuzz_spec("concatenation length",
        \s1, s2: (s1 + s2).len() == s1.len() + s2.len(),
        fuzz.text(0, 20),
        iterations: 500
    )

    fuzz_spec("split/join roundtrip",
        \s: not s.contains(",") => s.split(",").join(",") == s,
        fuzz.text(0, 50)
    )
```

**Example 2: Math properties**
```simple
import std.fuzz

describe "Math properties":
    fuzz_spec("addition commutative",
        \a, b: a + b == b + a,
        fuzz.int(-1000, 1000)
    )

    fuzz_spec("multiplication associative",
        \a, b, c: (a * b) * c == a * (b * c),
        fuzz.int(-100, 100)
    )
```

**Example 3: Custom generator**
```simple
import std.fuzz

# Generator for sorted lists
struct SortedListGen:
    impl Generator<List<i32>>:
        fn generate(rng: RandomState) -> List<i32>:
            val gen = fuzz.list(fuzz.int(), 5, 20)
            val xs = gen.generate(rng)
            xs.sort()
            xs

describe "Binary search":
    fuzz_spec("finds existing elements",
        \xs:
            if xs.is_empty():
                return true
            val target = xs[xs.len() / 2]
            val found = binary_search(xs, target)
            found.is_some() and found.unwrap() == target
        ,
        SortedListGen()
    )
```

### 1.4 File Structure

```
simple/std_lib/src/testing/
├── fuzz.spl              # Main fuzzing library (~300 LOC)
├── fuzz_generators.spl   # Extra generators (optional, ~200 LOC)
└── fuzz_shrinkers.spl    # Shrinking logic (optional, ~150 LOC)
```

## 2. Mutation Testing Library: `std.mutate`

### 2.1 Design Goals

- **AST-based:** Parse code, mutate AST, regenerate
- **Configurable:** Select mutation operators
- **Reports:** Show mutation survival rate
- **Simple integration:** Works with existing `simple test`

### 2.2 Mutation Operators

| Operator | Description | Example |
|----------|-------------|---------|
| **Replace Binary Op** | `+` → `-`, `*` → `/` | `a + b` → `a - b` |
| **Replace Comparison** | `==` → `!=`, `<` → `>=` | `x == 0` → `x != 0` |
| **Replace Constant** | `0` → `1`, `true` → `false` | `if x > 0` → `if x > 1` |
| **Remove Statement** | Delete line | `x = 5` → *(deleted)* |
| **Negate Condition** | `if x` → `if not x` | `if ready` → `if not ready` |
| **Replace Return** | `return x` → `return 0` | `return result` → `return 0` |

### 2.3 API Design

```simple
# simple/std_lib/src/testing/mutate.spl

import std.file
import std.parser  # AST manipulation
import std.spec

# Mutation operator
enum MutationOp:
    ReplaceBinOp(old: text, new: text)
    ReplaceCmpOp(old: text, new: text)
    ReplaceConstant(old: any, new: any)
    RemoveStatement(line: i32)
    NegateCondition(line: i32)
    ReplaceReturn(line: i32, value: any)

# Mutation result
enum MutantStatus:
    Killed      # Test failed (good - caught the bug)
    Survived    # Test passed (bad - weak test)
    Timeout     # Infinite loop
    BuildError  # Mutant doesn't compile

struct Mutant:
    id: i32
    file: text
    line: i32
    operator: MutationOp
    status: MutantStatus

struct MutationReport:
    total: i32
    killed: i32
    survived: i32
    timeout: i32
    build_errors: i32

    fn score() -> f32:
        """Mutation score: killed / (killed + survived)"""
        val viable = self.killed + self.survived
        if viable == 0:
            return 0.0
        (self.killed as f32) / (viable as f32)

    fn summary() -> text:
        val score_pct = (self.score() * 100.0) as i32
        """
        Mutation Testing Results
        ========================
        Total mutants:   {self.total}
        Killed:          {self.killed}
        Survived:        {self.survived} ⚠️
        Timeout:         {self.timeout}
        Build errors:    {self.build_errors}

        Mutation Score:  {score_pct}%
        """

# Run mutation testing
pub fn mutate(
    source_file: text,
    test_command: text = "simple test",
    operators: List<text> = ["all"],
    timeout_secs: i32 = 30
) -> MutationReport:
    """
    Run mutation testing on a source file.

    Args:
        source_file: Path to .spl file to mutate
        test_command: Command to run tests (default: "simple test")
        operators: Mutation operators to apply (default: all)
        timeout_secs: Timeout per mutant (default: 30s)

    Returns:
        MutationReport with results

    Example:
        report = mutate("src/calculator.spl", "simple test calculator_spec.spl")
        print report.summary()
        expect report.score() > 0.8  # 80% mutation score
    """

    # Parse source file
    val ast = parse_file(source_file)

    # Generate mutants
    val mutants = generate_mutants(ast, operators)

    # Test each mutant
    var results = []
    for mutant in mutants:
        val status = run_mutant(mutant, test_command, timeout_secs)
        results.append(Mutant(
            id: mutant.id,
            file: source_file,
            line: mutant.line,
            operator: mutant.op,
            status: status
        ))

    # Generate report
    create_report(results)

# Helper: Generate mutants from AST
fn generate_mutants(ast: AST, operators: List<text>) -> List<PendingMutant>:
    var mutants = []

    # Visit each node
    for node in ast.walk():
        match node:
            BinOp(left, op, right, line):
                if "binop" in operators or "all" in operators:
                    for new_op in get_binop_mutations(op):
                        mutants.append(PendingMutant(
                            line: line,
                            op: MutationOp::ReplaceBinOp(old: op, new: new_op)
                        ))

            Compare(left, op, right, line):
                if "cmp" in operators or "all" in operators:
                    for new_op in get_cmp_mutations(op):
                        mutants.append(PendingMutant(
                            line: line,
                            op: MutationOp::ReplaceCmpOp(old: op, new: new_op)
                        ))

            # ... other node types

    mutants

# Helper: Run a single mutant
fn run_mutant(
    mutant: PendingMutant,
    test_command: text,
    timeout_secs: i32
) -> MutantStatus:
    # 1. Apply mutation to create temp file
    val mutated_code = apply_mutation(mutant)
    val temp_file = write_temp(mutated_code)

    # 2. Run tests with timeout
    val result = run_with_timeout(test_command, timeout_secs)

    # 3. Classify result
    match result:
        Success:
            MutantStatus::Survived  # Bad - test didn't catch mutation
        Failure:
            MutantStatus::Killed    # Good - test caught mutation
        Timeout:
            MutantStatus::Timeout
        BuildError:
            MutantStatus::BuildError

    # 4. Clean up
    delete_temp(temp_file)

# Mutation mappings
fn get_binop_mutations(op: text) -> List<text>:
    match op:
        "+": ["-", "*"]
        "-": ["+"]
        "*": ["/", "+"]
        "/": ["*"]
        _: []

fn get_cmp_mutations(op: text) -> List<text>:
    match op:
        "==": ["!="]
        "!=": ["=="]
        "<": ["<=", ">="]
        "<=": ["<"]
        ">": [">=", "<="]
        ">=": [">"]
        _: []
```

### 2.4 Usage Examples

**Example 1: Simple function**
```simple
# src/math.spl
fn abs(x: i32) -> i32:
    if x < 0:
        return -x
    else:
        return x

# test/math_spec.spl
import std.mutate

describe "Mutation testing":
    it "has good coverage":
        val report = mutate("src/math.spl", "simple test test/math_spec.spl")
        print report.summary()
        expect report.score() > 0.9  # Require 90% mutation score
```

**Example 2: Integration with CI**
```simple
# ci/mutation_test.spl
import std.mutate
import std.file

fn main():
    val files = [
        "src/calculator.spl",
        "src/parser.spl",
        "src/formatter.spl"
    ]

    var overall_score = 0.0

    for file in files:
        print "Testing {file}..."
        val report = mutate(file)
        print report.summary()
        overall_score = overall_score + report.score()

    overall_score = overall_score / (files.len() as f32)
    print "\nOverall Mutation Score: {(overall_score * 100.0) as i32}%"

    # Fail if below threshold
    if overall_score < 0.8:
        exit(1)
```

**Example 3: Custom operators**
```simple
import std.mutate

describe "Targeted mutation":
    it "tests conditionals only":
        val report = mutate(
            "src/logic.spl",
            operators: ["cmp", "negate"]
        )
        expect report.survived == 0  # All conditional mutants killed
```

### 2.5 CLI Integration

Add `simple mutate` command:

```bash
# Test single file
simple mutate src/calculator.spl

# Test with specific test file
simple mutate src/calculator.spl --test test/calculator_spec.spl

# Only specific operators
simple mutate src/logic.spl --operators binop,cmp

# Parallel execution
simple mutate src/ --jobs 4

# Generate HTML report
simple mutate src/ --report mutants.html
```

### 2.6 File Structure

```
simple/std_lib/src/testing/
├── mutate.spl           # Main mutation library (~400 LOC)
├── mutate_ops.spl       # Mutation operators (~200 LOC)
└── mutate_report.spl    # HTML/JSON reports (~150 LOC)
```

## 3. Comparison: Simple Tools vs. Rust Tools

| Feature | Simple Fuzzing | cargo-fuzz | Simple Mutate | cargo-mutants |
|---------|---------------|------------|---------------|---------------|
| **Language** | Simple | Rust | Simple | Rust |
| **Target** | Simple programs | Rust code | Simple code | Rust code |
| **Setup** | `import std.fuzz` | Install + nightly | `import std.mutate` | Install |
| **LOC** | ~500 | 10K+ | ~750 | 15K+ |
| **Speed** | Medium | Very fast | Slow (recompile) | Fast (incremental) |
| **Coverage** | Property-based | Coverage-guided | AST mutations | Source mutations |
| **Shrinking** | Basic | Advanced | N/A | N/A |

**When to use Simple tools:**
- Testing Simple applications
- Learning fuzzing/mutation concepts
- Quick property tests in CI
- No external dependencies needed

**When to use Rust tools:**
- Testing the Simple compiler itself
- Long-running fuzz campaigns (24h+)
- Maximum performance needed
- Integration with OSS-Fuzz

## 4. Implementation Plan

### Phase 1: Fuzzing Library (Week 1-2)
- [ ] Create `simple/std_lib/src/testing/fuzz.spl`
- [ ] Implement core generators (int, text, list)
- [ ] Add `fuzz()` function with basic shrinking
- [ ] Write specs: `test/unit/testing/fuzz_spec.spl`
- [ ] Add SSpec integration: `fuzz_spec()`
- [ ] Document in `doc/guide/fuzzing.md`

### Phase 2: Mutation Testing (Week 3-4)
- [ ] Create `simple/std_lib/src/testing/mutate.spl`
- [ ] Implement AST mutation (require parser access)
- [ ] Add 6 basic operators (binop, cmp, const, remove, negate, return)
- [ ] Write `run_mutant()` with timeout
- [ ] Generate reports
- [ ] Write specs: `test/unit/testing/mutate_spec.spl`

### Phase 3: CLI Integration (Week 5)
- [ ] Add `simple mutate` command to `simple/app/`
- [ ] Add `--fuzz` flag to `simple test`
- [ ] HTML report generation
- [ ] Parallel execution

### Phase 4: Documentation (Week 6)
- [ ] Tutorial: `doc/guide/property_based_testing.md`
- [ ] Tutorial: `doc/guide/mutation_testing.md`
- [ ] Add examples to SSpec template
- [ ] Update `CLAUDE.md` with new tools

## 5. Dependencies

### Required
- `std.random` - ✅ Already exists
- `std.spec` - ✅ Already exists
- `std.file` - ✅ Already exists

### To Implement
- `std.parser` API - Expose AST for mutation (**blocker for mutate**)
- Process execution with timeout - Need for `run_mutant()`

### Optional
- `std.http` - For sending fuzz results to server
- `std.db` - For storing mutation history

## 6. Example Use Cases

### Use Case 1: Property-Based Tests for Stdlib

```simple
# simple/std_lib/test/unit/core/list_fuzz_spec.spl
import std.fuzz
import std.spec

describe "List properties":
    fuzz_spec("append preserves length",
        \xs, x:
            val original_len = xs.len()
            xs.append(x)
            xs.len() == original_len + 1
        ,
        fuzz.list(fuzz.int(), 0, 100)
    )

    fuzz_spec("sort is idempotent",
        \xs:
            val sorted1 = xs.sort()
            val sorted2 = sorted1.sort()
            sorted1 == sorted2
        ,
        fuzz.list(fuzz.int(), 0, 50),
        iterations: 500
    )
```

### Use Case 2: Mutation Testing for User Code

```simple
# user_project/src/calculator.spl
fn divide(a: i32, b: i32) -> Result<i32, text>:
    if b == 0:
        return Err("Division by zero")
    Ok(a / b)

# user_project/test/calculator_mutation_spec.spl
import std.mutate
import std.spec

describe "Calculator mutation coverage":
    it "has high mutation score":
        val report = mutate("src/calculator.spl")

        # Verify mutation testing works
        expect report.total > 0
        expect report.killed > 0

        # Require 85% score
        expect report.score() >= 0.85,
            "Mutation score too low: {report.score()}"
```

### Use Case 3: Fuzzing Custom Data Structures

```simple
# src/binary_tree.spl
class BinaryTree<T>:
    value: T
    left: Option<BinaryTree<T>>
    right: Option<BinaryTree<T>>

    fn insert(val: T):
        # ... insertion logic

    fn is_valid_bst() -> bool:
        # Check BST property

# test/binary_tree_fuzz_spec.spl
import std.fuzz

struct TreeGen:
    impl Generator<BinaryTree<i32>>:
        fn generate(rng: RandomState) -> BinaryTree<i32>:
            # Generate random tree
            val size = rng.next() % 20
            var tree = BinaryTree.new(0)
            for _ in 0..size:
                tree.insert(rng.next() % 100)
            tree

describe "Binary tree fuzzing":
    fuzz_spec("insert maintains BST property",
        \tree:
            tree.is_valid_bst()
        ,
        TreeGen(),
        iterations: 1000
    )
```

## 7. Performance Considerations

### Fuzzing Performance
- **Target:** 1000 iterations/second for simple properties
- **Bottleneck:** Generator complexity
- **Optimization:** Cache generated values, use faster RNG

### Mutation Testing Performance
- **Target:** 10 mutants/minute (includes recompilation)
- **Bottleneck:** Compiler invocation per mutant
- **Optimization:**
  - Incremental compilation (reuse HIR/MIR)
  - Parallel execution (test multiple mutants concurrently)
  - Cache mutation points (don't re-parse every time)

## 8. Future Enhancements

### Fuzzing
- [ ] Corpus management (save interesting inputs)
- [ ] Coverage-guided fuzzing (requires instrumentation)
- [ ] Better shrinking (binary search, delta debugging)
- [ ] Custom generator combinators
- [ ] Stateful property testing

### Mutation Testing
- [ ] Higher-order mutations (combine multiple operators)
- [ ] Selective mutation (only changed lines)
- [ ] Mutation diff visualization
- [ ] Integration with code review (show uncovered mutants)
- [ ] Machine learning for operator selection

## 9. Conclusion

**Recommended Approach:**

1. **Start with fuzzing** - Simpler, immediate value
   - Implement basic `std.fuzz` in 2 weeks
   - Use for stdlib testing (lists, strings, math)
   - Iterate based on usage

2. **Add mutation testing** - Requires parser API
   - Wait for `std.parser` exposure
   - Implement basic operators first
   - Optimize for parallel execution

3. **Integrate with CI** - Continuous validation
   - Add to `make check`
   - Set mutation score thresholds
   - Track metrics over time

**Expected Benefits:**
- **Better tests:** Properties catch more edge cases than examples
- **Higher confidence:** Mutation testing validates test quality
- **Faster debugging:** Shrinking finds minimal failing cases
- **Developer productivity:** Less time writing manual test cases

---

**Next Steps:**
1. Review design with team
2. Prioritize fuzzing vs. mutation testing
3. Allocate 2-6 weeks for implementation
4. Start with `std.fuzz` prototype (1-2 days)
5. Gather feedback from early users
