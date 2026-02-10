# MC/DC Coverage Design for Simple Language

## Overview

Design document for implementing Modified Condition/Decision Coverage (MC/DC) in Simple language. MC/DC is required for safety-critical systems (DO-178C Level A, ISO 26262 ASIL D).

## Coverage Hierarchy

```
                    MC/DC (strictest)
                       ↑
              Condition/Decision (C/DC)
                    ↑         ↑
           Condition     Decision/Branch
                              ↑
                      Statement/Line (weakest)
```

## Coverage Types Comparison

### 1. Decision/Branch Coverage (Current)
```simple
if (a > 0) and (b > 0):
    x = 1
else:
    x = 2
```

**Requirements:** Decision = true, Decision = false
**Test cases:**
- a=1, b=1 → true ✓
- a=0, b=0 → false ✓
**Coverage: 100% (2 tests)**

### 2. Condition Coverage
**Requirements:** Each condition = true AND false

| Test | a > 0 | b > 0 | Decision |
|------|-------|-------|----------|
| 1    | T     | T     | T        |
| 2    | F     | F     | F        |

**Problem:** Both conditions flip together - doesn't prove independence!

### 3. Condition/Decision Coverage (C/DC)
**Requirements:** Decision coverage + Condition coverage

| Test | a > 0 | b > 0 | Decision |
|------|-------|-------|----------|
| 1    | T     | T     | T        |
| 2    | F     | F     | F        |

**Still same problem** - conditions not tested independently.

### 4. MC/DC (Modified Condition/Decision Coverage)
**Requirements:** Each condition independently affects the decision outcome

For `(a > 0) and (b > 0)`:

| Test | a > 0 | b > 0 | Decision | Independence |
|------|-------|-------|----------|--------------|
| 1    | T     | T     | T        | baseline     |
| 2    | F     | T     | F        | a flips decision |
| 3    | T     | F     | F        | b flips decision |

**Minimum tests for N conditions:** N + 1 (not 2^N)

## MC/DC Independence Pairs

For each condition, find a pair of test cases where:
1. Only that condition changes
2. The decision outcome changes

### Example: `(a and b) or c`

Truth table:
| # | a | b | c | a and b | (a and b) or c |
|---|---|---|---|---------|----------------|
| 1 | F | F | F | F       | F              |
| 2 | F | F | T | F       | T              |
| 3 | F | T | F | F       | F              |
| 4 | F | T | T | F       | T              |
| 5 | T | F | F | F       | F              |
| 6 | T | F | T | F       | T              |
| 7 | T | T | F | T       | T              |
| 8 | T | T | T | T       | T              |

**Independence pairs:**
- **a:** (3,7) or (5,7) - only a changes, decision changes
- **b:** (5,7) or (6,8) - only b changes, decision changes  
- **c:** (1,2) or (3,4) or (5,6) - only c changes, decision changes

**Minimum MC/DC test set:** {2, 5, 6, 7} = 4 tests (N+1 = 3+1 = 4)

## Architecture Design

### 1. Condition Instrumentation

```simple
# Original code
if (a > 0) and (b > 0):
    do_something()

# Instrumented code (conceptual)
val _cond_1 = a > 0
val _cond_2 = b > 0
_mcdc_record("decision_1", [_cond_1, _cond_2], _cond_1 and _cond_2)
if _cond_1 and _cond_2:
    do_something()
```

### 2. Data Structures

```simple
# Condition evaluation record
struct ConditionEval:
    condition_id: i64       # Unique condition ID
    value: bool             # Evaluated value (true/false)
    location: SourceLoc     # Source location

# Decision evaluation record  
struct DecisionEval:
    decision_id: i64        # Unique decision ID
    conditions: [ConditionEval]  # All conditions in this decision
    outcome: bool           # Final decision outcome
    location: SourceLoc     # Source location

# MC/DC coverage data
struct MCDCData:
    decisions: [DecisionInfo]
    evaluations: [DecisionEval]  # All recorded evaluations

struct DecisionInfo:
    id: i64
    expression: text        # Original expression text
    condition_count: i64    # Number of conditions
    location: SourceLoc

struct MCDCResult:
    decision_id: i64
    expression: text
    condition_count: i64
    conditions_covered: i64
    independence_pairs: [(i64, i64)]  # Pairs proving independence
    mcdc_percent: f64
    is_covered: bool
```

### 3. MC/DC Analysis Algorithm

```simple
fn analyze_mcdc(decision: DecisionInfo, evals: [DecisionEval]) -> MCDCResult:
    """Analyze MC/DC coverage for a decision."""
    
    val condition_count = decision.condition_count
    var independence_proven: [bool] = [false] * condition_count
    var independence_pairs: [(i64, i64)] = []
    
    # For each condition, find independence pair
    for cond_idx in 0..condition_count:
        val pair = find_independence_pair(cond_idx, evals)
        if pair != nil:
            independence_proven[cond_idx] = true
            independence_pairs.push(pair)
    
    val covered = independence_proven.filter(\x: x).len()
    val mcdc_percent = (covered as f64 / condition_count as f64) * 100.0
    
    MCDCResult {
        decision_id: decision.id
        expression: decision.expression
        condition_count: condition_count
        conditions_covered: covered
        independence_pairs: independence_pairs
        mcdc_percent: mcdc_percent
        is_covered: covered == condition_count
    }

fn find_independence_pair(
    cond_idx: i64, 
    evals: [DecisionEval]
) -> (i64, i64)?:
    """Find pair of evaluations proving condition independence."""
    
    # For each pair of evaluations
    for i in 0..evals.len():
        for j in (i+1)..evals.len():
            val eval_a = evals[i]
            val eval_b = evals[j]
            
            # Check if only cond_idx differs
            var only_this_differs = true
            for k in 0..eval_a.conditions.len():
                if k == cond_idx:
                    # This condition MUST differ
                    if eval_a.conditions[k].value == eval_b.conditions[k].value:
                        only_this_differs = false
                        break
                else:
                    # Other conditions must be SAME
                    if eval_a.conditions[k].value != eval_b.conditions[k].value:
                        only_this_differs = false
                        break
            
            # Check if decision outcome differs
            if only_this_differs and eval_a.outcome != eval_b.outcome:
                return (i, j)
    
    nil  # No independence pair found
```

### 4. Coverage API Extension

```simple
# Extended check_coverage API
fn check_coverage(
    coverage_type: text,    # "line", "branch", "condition", "mcdc"
    pattern: text,
    minimum: f64 = 0.0,
    maximum: f64 = 100.0,
    minimum_check: bool = true
) -> CoverageResult

# New MC/DC specific API
fn check_mcdc_coverage(
    pattern: text,
    minimum: f64 = 100.0    # MC/DC usually requires 100%
) -> MCDCCoverageResult

struct MCDCCoverageResult:
    passed: bool
    overall_percent: f64
    decisions_total: i64
    decisions_covered: i64
    details: [MCDCResult]
```

### 5. Reporting Format

```json
{
  "mcdc_coverage": {
    "summary": {
      "decisions_total": 15,
      "decisions_covered": 12,
      "overall_percent": 80.0
    },
    "decisions": [
      {
        "id": 1,
        "file": "src/parser/expr.spl",
        "line": 45,
        "expression": "(a > 0) and (b > 0)",
        "conditions": [
          {"id": 0, "text": "a > 0", "covered": true},
          {"id": 1, "text": "b > 0", "covered": true}
        ],
        "independence_pairs": [
          {"condition": 0, "test_pair": [1, 2]},
          {"condition": 1, "test_pair": [1, 3]}
        ],
        "mcdc_percent": 100.0,
        "is_covered": true
      },
      {
        "id": 2,
        "file": "src/parser/expr.spl", 
        "line": 78,
        "expression": "(x or y) and z",
        "conditions": [
          {"id": 0, "text": "x", "covered": true},
          {"id": 1, "text": "y", "covered": false},
          {"id": 2, "text": "z", "covered": true}
        ],
        "independence_pairs": [
          {"condition": 0, "test_pair": [1, 4]},
          {"condition": 2, "test_pair": [2, 5]}
        ],
        "mcdc_percent": 66.7,
        "is_covered": false,
        "missing": ["condition 'y' needs independence pair"]
      }
    ]
  }
}
```

## Implementation Plan

### Phase 1: AST Condition Extraction (Week 1)
- [ ] Parse boolean expressions into condition trees
- [ ] Identify decision points (if, while, ternary, and, or)
- [ ] Extract individual conditions from compound expressions
- [ ] Generate condition IDs and metadata
- [ ] Unit tests for expression parsing

### Phase 2: Instrumentation (Week 2)
- [ ] Add instrumentation pass to compiler
- [ ] Insert condition recording calls
- [ ] Handle short-circuit evaluation correctly
- [ ] Generate instrumented code
- [ ] Verify instrumentation doesn't change behavior

### Phase 3: Runtime Recording (Week 2)
- [ ] Implement condition/decision recording API
- [ ] Thread-safe evaluation storage
- [ ] Efficient data structures for large test suites
- [ ] Memory management for long test runs

### Phase 4: MC/DC Analysis (Week 3)
- [ ] Implement independence pair finder
- [ ] Handle all boolean operators (and, or, not, xor)
- [ ] Support nested expressions
- [ ] Generate coverage reports
- [ ] Unit tests for analysis algorithm

### Phase 5: API Integration (Week 3)
- [ ] Add "mcdc" coverage type to check_coverage()
- [ ] Implement check_mcdc_coverage() function
- [ ] Add MC/DC to coverage reports
- [ ] Update documentation

### Phase 6: Testing & Validation (Week 4)
- [ ] Create MC/DC test suite
- [ ] Validate against known MC/DC tools
- [ ] Performance benchmarks
- [ ] Edge case testing
- [ ] Documentation and examples

## Grammar Extensions

### 1. MC/DC Test Annotations

```simple
# Annotate test for MC/DC tracking
@mcdc_test("decision_1")
it "tests condition a independence":
    # Test case that proves 'a' independence
    val result = check_condition(a: true, b: true)
    expect result == true

@mcdc_test("decision_1") 
it "tests condition a flipped":
    # Test case where only 'a' differs
    val result = check_condition(a: false, b: true)
    expect result == false
```

### 2. MC/DC Coverage Checks

```simple
@coverage
describe "MC/DC Coverage Tests":
    it "validates parser MC/DC coverage":
        val result = check_coverage("mcdc", "src/parser/**/*.spl", 
                                   minimum: 100.0)
        expect result.passed
        
        # Or use specific API
        val mcdc = check_mcdc_coverage("src/parser/**/*.spl", minimum: 100.0)
        expect mcdc.passed
        
        # Print uncovered conditions
        for decision in mcdc.details:
            if not decision.is_covered:
                print "Uncovered: {decision.expression} at {decision.file}:{decision.line}"
                for cond in decision.conditions:
                    if not cond.covered:
                        print "  Missing: {cond.text}"
```

### 3. MC/DC Report Generation

```simple
fn generate_mcdc_report(pattern: text, output: text):
    """Generate detailed MC/DC coverage report."""
    val mcdc = check_mcdc_coverage(pattern, minimum: 0.0)
    
    print "=" * 70
    print "MC/DC Coverage Report"
    print "=" * 70
    print ""
    print "Summary:"
    print "  Decisions: {mcdc.decisions_covered}/{mcdc.decisions_total}"
    print "  Coverage: {mcdc.overall_percent:.1f}%"
    print ""
    
    print "Uncovered Decisions:"
    print "-" * 70
    for decision in mcdc.details:
        if not decision.is_covered:
            print ""
            print "  {decision.file}:{decision.line}"
            print "  Expression: {decision.expression}"
            print "  Coverage: {decision.mcdc_percent:.1f}%"
            print "  Missing conditions:"
            for cond in decision.conditions:
                if not cond.covered:
                    print "    - {cond.text}: needs independence pair"
```

## Short-Circuit Handling

### Problem
```simple
if a and b:   # If a=false, b is never evaluated!
    ...
```

### Solution: Masking MC/DC

For short-circuit operators, use "masking MC/DC":
- A condition is "masked" if short-circuit prevents its evaluation
- Masked conditions don't need independence pairs
- Record masking state in evaluations

```simple
struct ConditionEval:
    condition_id: i64
    value: bool
    evaluated: bool     # false if masked by short-circuit
    masked_by: i64?     # ID of condition that masked this one
```

### Example

```simple
if a and b and c:
    ...
```

| Test | a | b | c | b evaluated | c evaluated | Result |
|------|---|---|---|-------------|-------------|--------|
| 1    | T | T | T | Y           | Y           | T      |
| 2    | F | - | - | N (masked)  | N (masked)  | F      |
| 3    | T | F | - | Y           | N (masked)  | F      |
| 4    | T | T | F | Y           | Y           | F      |

**Independence pairs (with masking):**
- **a:** (1,2) - a changes, b&c masked in test 2
- **b:** (1,3) - b changes, c masked in test 3
- **c:** (1,4) - c changes

## Coupled Conditions

### Problem
```simple
if (a > b) and (a < c):   # Both conditions use 'a'!
```

When conditions share variables, changing one may change another.

### Solution: Unique-Cause MC/DC vs Masking MC/DC

1. **Unique-Cause MC/DC** (stricter): Each condition must be shown independent while others are held constant. May be impossible for coupled conditions.

2. **Masking MC/DC** (practical): Allow condition changes as long as the effect propagates to the decision. Recommended for coupled conditions.

### Example

```simple
if (a > 0) and (a < 10):   # a is in range [1, 9]
```

Test cases:
| Test | a  | a > 0 | a < 10 | Result |
|------|-----|-------|--------|--------|
| 1    | 5   | T     | T      | T      |
| 2    | -1  | F     | T      | F      |
| 3    | 15  | T     | F      | F      |

- **a > 0:** (1,2) proves independence
- **a < 10:** (1,3) proves independence

Even though both use 'a', we can find independence pairs.

## Performance Considerations

### 1. Instrumentation Overhead
- Condition recording: ~10-20 cycles per condition
- Memory: ~32 bytes per evaluation record
- Mitigation: Only instrument when MC/DC enabled

### 2. Analysis Complexity
- Finding independence pairs: O(n * m²) where n=conditions, m=evaluations
- Mitigation: Early termination when pair found
- Mitigation: Index evaluations by condition values

### 3. Storage Optimization
```simple
# Compact evaluation storage
struct CompactEval:
    decision_id: u16        # 65K decisions max
    condition_bits: u64     # Up to 64 conditions as bits
    outcome: bool
    
# 11 bytes per evaluation vs 32+ bytes
```

## Integration with Existing Tools

### 1. LLVM Integration (Future)
```bash
# Use LLVM's experimental MC/DC
clang -fprofile-instr-generate -fcoverage-mapping -fcoverage-mcdc ...
```

### 2. Import External MC/DC Data
```simple
fn import_mcdc_data(format: text, path: text):
    """Import MC/DC data from external tools."""
    match format:
        case "llvm": import_llvm_mcdc(path)
        case "gcov": import_gcov_mcdc(path)
        case "json": import_json_mcdc(path)
```

### 3. Export for Certification
```simple
fn export_mcdc_certification(pattern: text, output: text, format: text):
    """Export MC/DC data for DO-178C/ISO 26262 certification."""
    val mcdc = check_mcdc_coverage(pattern, minimum: 100.0)
    
    match format:
        case "do178c": export_do178c_format(mcdc, output)
        case "iso26262": export_iso26262_format(mcdc, output)
        case "json": export_json_format(mcdc, output)
```

## Example Usage

```simple
use std.spec.*
use std.coverage.*

# Function under test
fn is_valid_range(x: i64, min: i64, max: i64) -> bool:
    (x >= min) and (x <= max)

# MC/DC tests
@coverage
@mcdc
describe "is_valid_range MC/DC":
    # Test 1: All true (baseline)
    it "returns true when x is in range":
        expect is_valid_range(5, 0, 10) == true
    
    # Test 2: First condition false (proves independence of x >= min)
    it "returns false when x < min":
        expect is_valid_range(-1, 0, 10) == false
    
    # Test 3: Second condition false (proves independence of x <= max)
    it "returns false when x > max":
        expect is_valid_range(15, 0, 10) == false
    
    # Verify MC/DC coverage
    it "achieves 100% MC/DC coverage":
        val result = check_coverage("mcdc", "**/range*.spl", minimum: 100.0)
        expect result.passed

# Complex expression MC/DC
fn complex_check(a: bool, b: bool, c: bool) -> bool:
    (a or b) and c

@coverage
@mcdc
describe "complex_check MC/DC":
    # Minimum test set for (a or b) and c: 4 tests
    
    it "T1: a=T, b=T, c=T -> T":
        expect complex_check(true, true, true) == true
    
    it "T2: a=F, b=T, c=T -> T (for 'a' independence with T3)":
        expect complex_check(false, true, true) == true
    
    it "T3: a=T, b=F, c=T -> T (for 'b' independence with T2)":
        expect complex_check(true, false, true) == true
    
    it "T4: a=F, b=F, c=T -> F (proves a and b together affect outcome)":
        expect complex_check(false, false, true) == false
    
    it "T5: a=T, b=T, c=F -> F (proves 'c' independence)":
        expect complex_check(true, true, false) == false
    
    it "validates MC/DC coverage":
        val mcdc = check_mcdc_coverage("**/complex*.spl", minimum: 100.0)
        expect mcdc.passed
        
        # Print coverage details
        print "MC/DC Coverage: {mcdc.overall_percent}%"
        for decision in mcdc.details:
            print "  {decision.expression}: {decision.mcdc_percent}%"
```

## Summary

### What We're Adding

| Coverage Type | Current | New |
|---------------|---------|-----|
| Line | ✓ | ✓ |
| Branch/Decision | ✓ | ✓ |
| Condition | ✗ | ✓ |
| C/DC | ✗ | ✓ |
| **MC/DC** | ✗ | **✓** |

### Key Features
1. **Automatic condition extraction** from boolean expressions
2. **Independence pair analysis** for MC/DC verification
3. **Short-circuit handling** with masking MC/DC
4. **Coupled condition support** for shared variables
5. **Certification export** for DO-178C, ISO 26262
6. **API integration** with existing coverage system

### Timeline
- **Week 1-2:** AST parsing, instrumentation
- **Week 3:** Analysis algorithm, API
- **Week 4:** Testing, validation, documentation

**Total: 4 weeks to production-ready MC/DC support**
