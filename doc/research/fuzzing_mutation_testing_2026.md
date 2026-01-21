# Fuzzing and Mutation Testing for Simple Compiler

**Research Date:** 2026-01-21
**Status:** Proposal - Not Implemented
**Related Issues:** Testing infrastructure, Compiler robustness

## Executive Summary

This document evaluates fuzzing and mutation testing tools for the Simple compiler, recommending:
- **Fuzzing:** `cargo-fuzz` (libFuzzer) for parser/compiler fuzzing
- **Mutation Testing:** `cargo-mutants` for test quality validation
- **Grammar-Based Testing:** `arbitrary` + `bolero` for structured input generation

## 1. Fuzzing

### 1.1 What is Fuzzing?

Fuzzing is automated testing that feeds random or mutated inputs to find crashes, panics, and undefined behavior. For compilers, it targets:
- **Lexer/Parser:** Invalid syntax, edge cases, deeply nested structures
- **Type Checker:** Inconsistent types, circular references
- **HIR/MIR Lowering:** Code generation bugs, optimization crashes
- **Interpreter/Codegen:** Memory safety issues, runtime panics

### 1.2 Available Tools (2026)

| Tool | Type | Platform | Compiler | Status | Best For |
|------|------|----------|----------|--------|----------|
| **cargo-fuzz** | Coverage-guided (libFuzzer) | Unix, x86-64/ARM64 | Nightly | Active | General fuzzing |
| **honggfuzz-rs** | Coverage-guided | Cross-platform | Stable | Active | Security fuzzing |
| **AFL.rs** | Coverage-guided | Unix | Stable | Mature | Traditional AFL users |
| **bolero** | Framework | Cross-platform | Stable | Active | Property-based + fuzzing |
| **arbtest** | Lightweight | Cross-platform | Stable | Active | Quick property tests |

### 1.3 Recommendation: cargo-fuzz

**Why cargo-fuzz:**
- Industry standard (used by Rust compiler team, major projects)
- Excellent corpus management and minimization
- Integrates with libFuzzer's coverage instrumentation
- Simple setup: `cargo install cargo-fuzz`

**Trade-offs:**
- Requires nightly Rust (not a problem for Simple)
- Unix-only (acceptable for development)
- Slower when AddressSanitizer enabled (can disable with `--sanitizer none` for pure Rust)

### 1.4 Specialized Tools (2025-2026 Research)

**deepSURF** (IEEE S&P 2026)
- LLM-augmented harness generation
- Detected 42 memory bugs (12 newly-discovered)
- Promising but experimental

**RusyFuzz** (ICSE 2026)
- Rust OS kernel fuzzing (panic-guided)
- Not directly applicable to Simple

**FourFuzz** (Targeted unsafe fuzzing)
- Focuses on unsafe code blocks
- Useful for runtime FFI testing

## 2. Mutation Testing

### 2.1 What is Mutation Testing?

Mutation testing validates test quality by injecting bugs ("mutants") into code and checking if tests catch them. It measures:
- **Test coverage quality** (not just line coverage)
- **Missing assertions** (tests that run but don't verify)
- **Dead code** (uncovered by any test)

### 2.2 Available Tools

| Tool | Approach | Maintenance | Compiler | Invasiveness |
|------|----------|-------------|----------|--------------|
| **cargo-mutants** | Black-box | Active (2025+) | Stable | None (zero modifications) |
| **mutagen** | White-box | Abandoned (2022) | Nightly | Requires `#[mutate]` attributes |

### 2.3 Recommendation: cargo-mutants

**Why cargo-mutants:**
- **Zero source modifications** - works with existing code
- **Actively maintained** (latest release 2025)
- **Incremental builds** per mutant
- **Stable Rust** compatible
- **Easy setup:** `cargo install cargo-mutants`

**Example workflow:**
```bash
# Test all mutations in parser crate
cargo mutants --package simple-parser

# Test specific file
cargo mutants --file src/parser/src/lexer.rs

# Parallel execution
cargo mutants --jobs 8

# Generate report
cargo mutants --output mutants.json
```

**Expected benefits:**
- Find weak tests (pass even with bugs)
- Identify missing edge case tests
- Validate error handling paths

## 3. Grammar-Based Fuzzing

### 3.1 Compiler-Specific Challenges

Standard fuzzing generates invalid inputs (rejected by lexer/parser). Grammar-based fuzzing generates **valid** programs to test:
- Type checking
- HIR/MIR lowering
- Code generation
- Optimization passes

### 3.2 Recommended Approach

**Tools:** `arbitrary` crate + `bolero` framework

**Strategy:**
1. Define `Arbitrary` implementations for Simple AST nodes
2. Use `bolero` to bridge property testing and fuzzing
3. Generate valid Simple programs from grammar

**Example structure:**
```rust
// In src/parser/src/ast/mod.rs
use arbitrary::Arbitrary;

#[derive(Debug, Arbitrary)]
pub struct Expr {
    // Existing fields...
}

// In fuzz/fuzz_targets/parser.rs
use bolero::generator::*;

fn fuzz_parser(input: &[u8]) {
    let expr = Expr::arbitrary(&mut Unstructured::new(input))?;
    // Test parsing roundtrip
    let source = expr.to_source();
    let parsed = parse(&source)?;
    assert_eq!(expr, parsed);
}
```

### 3.3 Property Testing vs. Fuzzing

| Aspect | Property Testing | Fuzzing |
|--------|------------------|---------|
| Duration | Seconds (unit test) | Hours/days |
| Feedback | Test suite | Black-box crashes |
| Input | Structured (Arbitrary) | Raw bytes |
| Shrinking | Automatic | Manual minimization |

**Recommendation:** Use both
- `proptest` for fast feedback in CI
- `cargo-fuzz` for long-running discovery

## 4. Implementation Plan for Simple

### 4.1 Priority Targets

**High Priority:**
1. **Lexer** (`src/parser/src/lexer.rs`)
   - Fuzz token stream generation
   - Test edge cases: Unicode, escapes, string interpolation

2. **Parser** (`src/parser/src/parser.rs`)
   - Fuzz AST construction
   - Test deeply nested expressions, large files

3. **Type Checker** (`src/compiler/src/hir/lower/type_resolver.rs`)
   - Fuzz type unification
   - Test generic resolution, trait bounds

4. **HIR Lowering** (`src/compiler/src/hir/lower/`)
   - Fuzz statement/expression lowering
   - Test memory capability inference

**Medium Priority:**
5. **MIR Generation** (`src/compiler/src/mir/`)
   - Fuzz instruction generation
   - Test optimization passes

6. **Interpreter** (`src/compiler/src/interpreter*.rs`)
   - Fuzz runtime evaluation
   - Test GC, reference counting

**Low Priority (Future):**
7. **Cranelift Codegen** - Complex, needs specialized harness
8. **Package System** - Higher-level fuzzing

### 4.2 Suggested Directory Structure

```
simple/
├── fuzz/                          # cargo-fuzz targets
│   ├── Cargo.toml
│   └── fuzz_targets/
│       ├── lexer.rs               # Fuzz lexer token generation
│       ├── parser.rs              # Fuzz parser AST construction
│       ├── type_checker.rs        # Fuzz type resolution
│       ├── hir_lowering.rs        # Fuzz HIR generation
│       └── interpreter.rs         # Fuzz runtime evaluation
├── src/parser/
│   └── src/
│       └── arbitrary_impl.rs      # Arbitrary for AST (feature-gated)
└── doc/research/
    └── fuzzing_results/           # Corpus, crashes, reports
```

### 4.3 Setup Commands

**1. Install tools:**
```bash
# Fuzzing
cargo install cargo-fuzz
rustup toolchain install nightly

# Mutation testing
cargo install cargo-mutants

# Property testing (add to Cargo.toml)
cargo add --dev arbitrary bolero proptest
```

**2. Initialize fuzzing:**
```bash
cargo fuzz init
cargo fuzz add lexer
cargo fuzz add parser
```

**3. Run initial fuzz campaign:**
```bash
# Fuzz lexer for 10 minutes
cargo +nightly fuzz run lexer -- -max_total_time=600

# Parallel fuzzing (use all cores)
cargo +nightly fuzz run parser --jobs=$(nproc)
```

**4. Run mutation testing:**
```bash
# Test parser crate
cargo mutants --package simple-parser

# Only test changed files
cargo mutants --in-diff origin/main
```

### 4.4 Integration with CI

**GitHub Actions example:**
```yaml
name: Fuzzing & Mutation Testing

on:
  schedule:
    - cron: '0 2 * * *'  # Nightly at 2 AM
  workflow_dispatch:

jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - run: cargo install cargo-fuzz
      - name: Fuzz lexer (5 min)
        run: cargo fuzz run lexer -- -max_total_time=300
      - name: Upload crashes
        if: failure()
        uses: actions/upload-artifact@v4
        with:
          name: fuzz-crashes
          path: fuzz/artifacts/

  mutants:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cargo install cargo-mutants
      - name: Run mutation tests
        run: cargo mutants --package simple-parser --package simple-compiler
      - name: Upload report
        uses: actions/upload-artifact@v4
        with:
          name: mutants-report
          path: mutants.out/
```

### 4.5 Expected Outcomes

**Fuzzing:**
- **Crash reports** in `fuzz/artifacts/<target>/crash-*`
- **Corpus growth** (saved interesting inputs)
- **Coverage maps** (show tested code paths)

**Mutation Testing:**
- **Survival rate** (% of mutants not caught)
- **Timeout mutants** (infinite loops)
- **Unviable mutants** (don't compile)

**Goals:**
- 0 crashes in 24-hour fuzz campaigns
- <5% mutation survival rate for critical crates

## 5. Best Practices from 2026 Research

### 5.1 Compiler Fuzzing Patterns

**Parser-Directed Fuzzing** (PLDI 2019)
- Track comparison operations during parsing
- Satisfy comparisons leading to rejections
- Systematically cover input space

**Code Fragment Fuzzing** (USENIX Security 2012)
- Use existing code fragments as mutation seeds
- Preserve syntactic validity
- Test deeper compilation stages

**Grammar-Based Mutation**
- AST-level mutations (not byte-level)
- Preserve semantic constraints
- Use unparsers to regenerate source

### 5.2 Rust-Specific Considerations

**Sanitizers:**
- AddressSanitizer: Memory safety (default, slow for pure Rust)
- ThreadSanitizer: Concurrency bugs
- MemorySanitizer: Uninitialized reads
- **Disable for pure Rust:** `--sanitizer none` for 10x speedup

**Panic vs. Crash:**
- Rust panics are "expected failures" (user errors)
- Configure fuzz harness to allow panics for invalid input
- Only fail on unexpected panics (compiler bugs)

**Cargo Features:**
- Test with different feature combinations
- Example: `--features "lean-verify gpu-support"`

### 5.3 Continuous Fuzzing

**OSS-Fuzz Integration** (Google's continuous fuzzing service)
- Free for open-source projects
- 24/7 fuzzing on Google infrastructure
- Automatic crash reporting
- ClusterFuzz corpus management

**Self-Hosted Alternatives:**
- Dedicated fuzzing server
- Cron jobs for nightly campaigns
- Store corpus in git-lfs or object storage

## 6. Comparison with Similar Projects

### 6.1 Rust Compiler (rustc)

**Fuzzing:**
- Uses `cargo-fuzz` extensively
- Targets: parser, type checker, MIR, LLVM IR
- Found 100+ bugs via OSS-Fuzz

**Mutation Testing:**
- Not widely used (too slow for massive codebase)
- Focus on integration tests instead

### 6.2 Smaller Compilers

**Tree-sitter** (parser generator)
- Heavy fuzzing with custom grammar generators
- Grammar-based corpus seeding

**SWC** (JavaScript/TypeScript compiler)
- Uses `cargo-fuzz` for parser
- Property tests with `quickcheck`

### 6.3 Lessons for Simple

- Start with **lexer + parser** (highest ROI)
- Use **corpus seeding** from SSpec examples
- **Grammar-based fuzzing** for type checker
- **Mutation testing** for critical algorithms (GC, borrow checker)

## 7. Cost-Benefit Analysis

### 7.1 Time Investment

| Activity | Initial Setup | Maintenance | ROI |
|----------|---------------|-------------|-----|
| cargo-fuzz (lexer/parser) | 4-8 hours | Low | High |
| Grammar-based fuzzing | 8-16 hours | Medium | Very High |
| cargo-mutants | 1-2 hours | Low | Medium-High |
| CI integration | 2-4 hours | Low | High |
| **Total** | **15-30 hours** | - | - |

### 7.2 Benefits

**Discovered bugs:**
- Edge cases not covered by unit tests
- Panics in error handling paths
- Type system soundness holes
- Memory safety issues in FFI code

**Improved test quality:**
- Mutation testing forces better assertions
- Identifies redundant tests
- Validates error handling

**User confidence:**
- Fewer production crashes
- Predictable compiler behavior
- Better error messages

### 7.3 Costs

**Compute resources:**
- Fuzzing: CPU-intensive (use spare cycles)
- Mutation testing: Slow (parallelize)

**Developer time:**
- Triaging crashes (some false positives)
- Writing grammar definitions
- Corpus management

**Recommendation:** Start small (lexer + parser fuzzing), expand based on bug finds.

## 8. Action Items

### 8.1 Phase 1: Basic Fuzzing (Week 1)
- [ ] Install `cargo-fuzz`
- [ ] Create `fuzz/` directory
- [ ] Implement lexer fuzz target
- [ ] Implement parser fuzz target
- [ ] Run 24-hour campaign, analyze results

### 8.2 Phase 2: Mutation Testing (Week 2)
- [ ] Install `cargo-mutants`
- [ ] Run baseline on `simple-parser`
- [ ] Improve weak tests (survival rate >10%)
- [ ] Run on `simple-compiler`

### 8.3 Phase 3: Grammar-Based Fuzzing (Week 3-4)
- [ ] Add `arbitrary` derives to AST
- [ ] Implement `Arbitrary` for complex nodes
- [ ] Create grammar-based fuzz targets
- [ ] Seed corpus from SSpec examples

### 8.4 Phase 4: CI Integration (Week 5)
- [ ] Add nightly fuzzing job
- [ ] Add mutation testing to PR checks
- [ ] Configure artifact uploads
- [ ] Document triage process

### 8.5 Phase 5: Advanced (Future)
- [ ] OSS-Fuzz integration
- [ ] Differential testing (interpreter vs. codegen)
- [ ] Symbolic execution (consider `kani` for verification)

## 9. References

### Fuzzing Resources
- [Rust Fuzz Book](https://rust-fuzz.github.io/book/cargo-fuzz.html) - Official cargo-fuzz documentation
- [Introduction to Rust Fuzzing](https://fuzzinglabs.com/introduction-rust-fuzzing-tutorial/) - Tutorial
- [cargo-fuzz GitHub](https://github.com/rust-fuzz/cargo-fuzz) - Source and examples
- [honggfuzz-rs](https://github.com/rust-fuzz/honggfuzz-rs) - Alternative fuzzer
- [Testing Compilers - The Fuzzing Book](https://www.fuzzingbook.org/html/PythonFuzzer.html) - Academic resource
- [A Survey of Modern Compiler Fuzzing](https://arxiv.org/pdf/2306.06884) - Research survey
- [deepSURF Paper](https://arxiv.org/abs/2506.15648) - LLM-augmented fuzzing (IEEE S&P 2026)
- [RusyFuzz](https://conf.researchr.org/details/icse-2026/icse-2026-research-track/96/) - Rust kernel fuzzing (ICSE 2026)
- [Targeted Fuzzing for Unsafe Rust](https://arxiv.org/abs/2505.02464) - FourFuzz paper

### Mutation Testing Resources
- [cargo-mutants Documentation](https://mutants.rs/) - Official docs
- [cargo-mutants GitHub](https://github.com/sourcefrog/cargo-mutants) - Source repository
- [cargo-mutants Comparison](https://github.com/sourcefrog/cargo-mutants/wiki/Compared) - vs. other tools
- [Mutation Testing in Rust - DEV](https://dev.to/nfrankel/mutation-testing-in-rust-3hpl) - Tutorial
- [Mutation Testing in Rust - Blog](https://blog.frankel.ch/mutation-testing-rust/) - Overview
- [mutagen GitHub](https://github.com/llogiq/mutagen) - Alternative (unmaintained)

### Grammar-Based Fuzzing
- [Bolero + Kani Blog Post](https://model-checking.github.io/kani-verifier-blog/2022/10/27/using-kani-with-the-bolero-property-testing-framework.html) - Property testing integration
- [Property Testing in Rust with Arbitrary](https://www.greyblake.com/blog/property-based-testing-in-rust-with-arbitrary/) - Tutorial
- [Fuzzing with Grammars - The Fuzzing Book](https://www.fuzzingbook.org/html/Grammars.html) - Theory
- [Awesome Grammar Fuzzing](https://github.com/Microsvuln/Awesome-Grammar-Fuzzing) - Curated resources
- [arbtest Documentation](https://docs.rs/arbtest/latest/arbtest/) - Lightweight testing
- [Parser-Directed Fuzzing (PLDI 2019)](https://dl.acm.org/doi/abs/10.1145/3314221.3314651) - Research paper
- [Rust Property Testing Guide](https://rustprojectprimer.com/testing/property.html) - Overview

### Security & Best Practices
- [Sherlock Rust Security Guide 2026](https://sherlock.xyz/post/rust-security-auditing-guide-2026) - Security audit patterns
- [Denial of Fuzzing: Rust in Windows Kernel](https://research.checkpoint.com/2025/denial-of-fuzzing-rust-in-the-windows-kernel/) - Real-world case study

## 10. Conclusion

**Recommended Implementation:**
1. **Start with cargo-fuzz** for lexer/parser (high impact, low effort)
2. **Add cargo-mutants** to validate test quality (quick wins)
3. **Expand to grammar-based fuzzing** for type checker (medium effort, high value)
4. **Integrate into CI** for continuous validation (low maintenance)

**Expected Impact:**
- **10-50 bugs discovered** in first month (based on similar projects)
- **20-40% improvement** in test quality (mutation survival reduction)
- **Increased confidence** in compiler stability

**Next Steps:**
1. Review this document with team
2. Prioritize Phase 1 targets
3. Allocate 2-4 hours for initial setup
4. Run first 24-hour fuzz campaign
5. Evaluate results and adjust strategy

---

**Document Metadata:**
- **Author:** Research conducted via web search and codebase analysis
- **Date:** 2026-01-21
- **Status:** Proposal - Awaiting approval for implementation
- **Related:** `TODO.md` (add fuzzing tasks), `CLAUDE.md` (update testing section)
