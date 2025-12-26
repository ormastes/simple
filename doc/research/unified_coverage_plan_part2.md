# Unified Coverage Plan - Part 2: Implementation & Integration

**Part of:** [Unified Coverage Plan](./unified_coverage_plan_part1.md)

---

**Goal:** Merge Rust + Simple coverage into unified report

#### Step 1: FFI Mapping Table
```rust
// src/util/coverage_tools/src/ffi_map.rs

pub struct FfiMap {
    mappings: HashMap<String, FfiBinding>,
}

pub struct FfiBinding {
    simple_function: String,
    rust_ffi: String,
    rust_file: PathBuf,
    rust_line: usize,
}

impl FfiMap {
    pub fn from_annotations() -> Self {
        // Parse FFI annotations from Rust code
        // Example: #[ffi(simple = "Array.push")]
        // Or read from generated ffi_map.json
    }
}
```

#### Step 2: Merger Implementation
```rust
// src/util/coverage_tools/src/bin/coverage_merge.rs

fn main() -> Result<()> {
    let args = Args::parse();

    let rust_cov = RustCoverage::from_file(&args.rust)?;
    let simple_cov = SimpleCoverage::from_file(&args.simple)?;
    let ffi_map = FfiMap::from_annotations()?;

    let merger = CoverageMerger::new(rust_cov, simple_cov, ffi_map);
    let unified = merger.merge()?;

    unified.save_json(&args.output)?;
    unified.save_html(&args.output.with_extension("html"))?;

    Ok(())
}
```

### Phase 3: HTML Dashboard (Week 3)

**Goal:** Interactive coverage dashboard

#### Dashboard Features
- **Overview:** Rust vs Simple coverage percentages
- **File Browser:** Navigate Rust and Simple files
- **FFI View:** List all FFI bindings with status
- **Feature View:** Per-feature coverage breakdown
- **Gap Highlights:** Red highlights for untested paths

#### Template
```html
<!-- target/coverage/unified/index.html -->
<!DOCTYPE html>
<html>
<head>
    <title>Simple Unified Coverage</title>
    <style>
        .coverage-high { background: #c8e6c9; }
        .coverage-medium { background: #fff9c4; }
        .coverage-low { background: #ffccbc; }
        .coverage-none { background: #ffebee; }
        .ffi-both-tested { color: green; }
        .ffi-gap { color: red; font-weight: bold; }
    </style>
</head>
<body>
    <h1>Simple Unified Coverage Report</h1>

    <div class="summary">
        <div class="metric">
            <h3>Rust Coverage</h3>
            <div class="percentage">85.0%</div>
            <div>8500 / 10000 lines</div>
        </div>
        <div class="metric">
            <h3>Simple Coverage</h3>
            <div class="percentage">65.3%</div>
            <div>980 / 1500 lines</div>
        </div>
        <div class="metric">
            <h3>FFI Bindings</h3>
            <div class="percentage">80%</div>
            <div>40 / 50 tested</div>
        </div>
    </div>

    <h2>Coverage Gaps</h2>
    <ul class="gaps">
        <li class="ffi-gap">
            Array.filter - Rust tested (100%) but Simple wrapper not tested
            <a href="#simple/std_lib/test/unit/core/array_spec.spl">Add test</a>
        </li>
    </ul>

    <h2>Feature Coverage</h2>
    <table>
        <tr>
            <th>Feature</th>
            <th>Rust</th>
            <th>Simple</th>
            <th>System</th>
        </tr>
        <tr>
            <td>Collections</td>
            <td class="coverage-high">92.5%</td>
            <td class="coverage-medium">68.0%</td>
            <td>3 tests</td>
        </tr>
    </table>
</body>
</html>
```

### Phase 4: Makefile Integration (Week 3)

**Goal:** Add coverage targets to Makefile

```makefile
# Unified coverage (Rust + Simple)
coverage-unified:
	@echo "=== UNIFIED COVERAGE (Rust + Simple) ==="
	@mkdir -p $(COVERAGE_DIR)/unified

	# Run Rust tests with coverage
	LLVM_PROFILE_FILE="$(COVERAGE_DIR)/rust_%p.profraw" \
		cargo test --workspace

	# Convert to JSON
	cargo llvm-cov --no-run --json \
		--output-path=$(COVERAGE_DIR)/rust_coverage.json

	# Run Simple tests with coverage
	SIMPLE_COVERAGE=1 \
	SIMPLE_COVERAGE_OUTPUT=$(COVERAGE_DIR)/simple_coverage.json \
		cargo test -p simple-driver -- simple_stdlib

	# Merge coverage
	cargo run -p simple-coverage-tools --bin coverage-merge \
		--rust $(COVERAGE_DIR)/rust_coverage.json \
		--simple $(COVERAGE_DIR)/simple_coverage.json \
		--output $(COVERAGE_DIR)/unified/unified_coverage.json

	# Generate HTML
	cargo run -p simple-coverage-tools --bin coverage-html \
		--input $(COVERAGE_DIR)/unified/unified_coverage.json \
		--output $(COVERAGE_DIR)/unified/index.html

	@echo ""
	@echo "Unified coverage report: $(COVERAGE_DIR)/unified/index.html"
	@echo "  Rust:   $(shell jq -r '.rust.percent' $(COVERAGE_DIR)/unified/unified_coverage.json)%"
	@echo "  Simple: $(shell jq -r '.simple.percent' $(COVERAGE_DIR)/unified/unified_coverage.json)%"
	@echo "  Gaps:   $(shell jq -r '.gaps | length' $(COVERAGE_DIR)/unified/unified_coverage.json)"

# Coverage check with thresholds
coverage-check-unified:
	@make coverage-unified
	@echo ""
	@echo "=== CHECKING COVERAGE THRESHOLDS ==="
	@cargo run -p simple-coverage-tools --bin coverage-check \
		--input $(COVERAGE_DIR)/unified/unified_coverage.json \
		--rust-threshold 85 \
		--simple-threshold 80 \
		--ffi-threshold 90
```

### Phase 5: CI Integration (Week 4)

**Goal:** Run unified coverage on every PR

#### GitHub Actions Workflow
```yaml
# .github/workflows/coverage.yml
name: Coverage

on:
  pull_request:
  push:
    branches: [main]

jobs:
  unified-coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Install cargo-llvm-cov
        run: cargo install cargo-llvm-cov

      - name: Run unified coverage
        run: make coverage-unified

      - name: Check coverage thresholds
        run: make coverage-check-unified

      - name: Upload coverage report
        uses: actions/upload-artifact@v4
        with:
          name: coverage-report
          path: target/coverage/unified/

      - name: Comment coverage summary on PR
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const coverage = JSON.parse(
              fs.readFileSync('target/coverage/unified/unified_coverage.json', 'utf8')
            );

            const comment = `
            ## Coverage Report

            | Component | Coverage | Change |
            |-----------|----------|--------|
            | Rust      | ${coverage.rust.percent}% | +0.5% |
            | Simple    | ${coverage.simple.percent}% | +2.1% |
            | FFI       | ${(coverage.ffi_bindings.filter(b => b.status === 'both_tested').length / coverage.ffi_bindings.length * 100).toFixed(1)}% | +1.0% |

            ### Gaps Detected
            ${coverage.gaps.map(g => `- ${g.function}: ${g.recommendation}`).join('\n')}

            [View full report](https://github.com/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId})
            `;

            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: comment
            });
```

---

## 6. Coverage Report Format

### 6.1 Dashboard Overview

```
┌─────────────────────────────────────────────────────────────┐
│              Simple Unified Coverage Report                 │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ Rust         │  │ Simple       │  │ FFI Bindings │     │
│  │ 85.0%        │  │ 65.3%        │  │ 80%          │     │
│  │ 8500/10000   │  │ 980/1500     │  │ 40/50        │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
│                                                             │
│  Coverage Trend:                                            │
│  ████████████████████░░░░░░░░░ 85% ↑ +2.3%                │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│ Coverage Gaps (10)                                          │
├─────────────────────────────────────────────────────────────┤
│ ⚠️  Array.filter - Rust tested, Simple wrapper not tested  │
│ ⚠️  Dict.merge - No system tests                           │
│ ⚠️  Actor.spawn - FFI binding not verified                 │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 Feature Coverage View

```
┌──────────────────────────────────────────────────────────────┐
│ Feature: Collections (#15)                                   │
├──────────────────────────────────────────────────────────────┤
│ Rust Implementation: 92.5% (185/200 lines)                   │
│   ✅ src/runtime/src/value/collections.rs                    │
│   ✅ src/compiler/src/codegen/instr_collections.rs           │
│                                                              │
│ Simple Stdlib: 68.0% (102/150 lines)                         │
│   ✅ simple/std_lib/src/core/array.spl (80%)                 │
│   ⚠️  simple/std_lib/src/core/dict.spl (55%)                 │
│                                                              │
│ System Tests: 3 tests                                        │
│   ✅ array_types_spec.spl                                    │
│   ✅ dictionary_types_spec.spl                               │
│   ❌ No integration test for Dict+Array interaction          │
│                                                              │
│ FFI Bindings: 8/10 tested                                    │
│   ✅ simple_array_push                                       │
│   ✅ simple_array_pop                                        │
│   ⚠️  simple_array_filter (Rust tested, Simple not)         │
│   ⚠️  simple_dict_merge (Neither tested)                     │
└──────────────────────────────────────────────────────────────┘
```

---

## 7. CI Integration

### 7.1 Coverage Enforcement

**PR Check Requirements:**
- ✅ Rust coverage ≥ 85%
- ✅ Simple coverage ≥ 80%
- ✅ FFI bindings ≥ 90% verified
- ✅ No new gaps introduced

**Example CI Output:**
```
Running unified coverage...

Rust Coverage:    85.2% ✅ (threshold: 85%)
Simple Coverage:  81.3% ✅ (threshold: 80%)
FFI Coverage:     88.0% ❌ (threshold: 90%)

❌ Coverage check FAILED

Gaps detected:
  - Array.filter: Rust tested (100%), Simple wrapper not tested
  - Actor.send: FFI binding not verified

Recommendations:
  1. Add test to simple/std_lib/test/unit/core/array_spec.spl for Array.filter
  2. Add system test for Actor.send in simple/test/system/features/actors/

View full report: https://github.com/.../actions/runs/12345
```

### 7.2 Coverage Diff

**Show coverage changes in PR:**
```
Coverage Changes:

src/runtime/src/value/collections.rs
  Lines:    185/200 → 192/200 (+7)
  Branches: 48/60 → 52/60 (+4)
  Coverage: 92.5% → 96.0% (+3.5%) ✅

simple/std_lib/src/core/array.spl
  Lines:    102/150 → 120/150 (+18)
  Coverage: 68.0% → 80.0% (+12.0%) ✅

FFI Bindings:
  + simple_array_filter now tested ✅
  - simple_dict_merge still untested ⚠️
```

---

## 8. Feature Tracking

### 8.1 Per-Feature Coverage Matrix

**Track coverage at all levels for each feature:**

| Feature | Rust | Simple | System | FFI | Status |
|---------|------|--------|--------|-----|--------|
| **Collections (#15)** | 92% | 68% | 3 tests | 80% | ⚠️ Gaps |
| **Actors (#27)** | 88% | 75% | 2 tests | 100% | ✅ Complete |
| **Async (#28)** | 95% | 60% | 1 test | 75% | ⚠️ Gaps |
| **Generators (#29)** | 90% | 0% | 0 tests | 0% | ❌ Not Tested |

### 8.2 Feature Coverage Report

**Generate per-feature report:**
```bash
cargo run -p simple-coverage-tools --bin feature-coverage \
    --input target/coverage/unified/unified_coverage.json \
    --output target/coverage/feature_coverage.md
```

**Output (feature_coverage.md):**
```markdown
# Feature Coverage Report

## Collections (#15) - ⚠️ Gaps Detected

**Overall:** 82.5% covered

### Rust Implementation
- **Coverage:** 92.5% (185/200 lines)
- **Files:**
  - src/runtime/src/value/collections.rs (95%)
  - src/compiler/src/codegen/instr_collections.rs (90%)

### Simple Stdlib
- **Coverage:** 68.0% (102/150 lines)
- **Files:**
  - simple/std_lib/src/core/array.spl (80%)
  - simple/std_lib/src/core/dict.spl (55%)

### System Tests
- **Count:** 3 tests
- **Files:**
  - array_types_spec.spl ✅
  - dictionary_types_spec.spl ✅

### FFI Bindings
- **Verified:** 8/10 (80%)
- **Gaps:**
  - simple_array_filter - Rust tested, Simple not
  - simple_dict_merge - Neither tested

### Recommendations
1. Add tests for Dict methods (merge, filter)
2. Add system test for Array+Dict interaction
3. Verify simple_array_filter FFI binding
```

---

## 9. Appendix A: New Feature IDs

| ID | Feature | Impact | Effort | Priority |
|----|---------|--------|--------|----------|
| **#674** | Simple Coverage Instrumentation | Enable Simple test coverage | 1 week | 🔥 High |
| **#675** | Coverage Merger Tool | Unified Rust+Simple reports | 1 week | 🔥 High |
| **#676** | FFI Mapping Generator | Auto-generate FFI mapping table | 3 days | 🟡 Medium |
| **#677** | Unified Coverage Dashboard | Interactive HTML report | 1 week | 🟡 Medium |
| **#678** | CI Coverage Checks | Automated PR coverage checks | 2 days | 🔥 High |
| **#679** | Feature Coverage Tracker | Per-feature coverage matrix | 3 days | 🟢 Low |

**Total:** 6 features, estimated **4 weeks** (1 engineer)

**Quick Win (2 weeks):**
1. #674 Simple Coverage Instrumentation (1 week)
2. #675 Coverage Merger Tool (1 week)
3. Basic HTML report (no fancy dashboard)

---

## 10. Appendix B: Migration Path

### Current State → Unified Coverage

**Week 1: No Breaking Changes**
```bash
# Old commands still work
make coverage-unit        # Rust only
make coverage-merged      # Rust only

# New command available
make coverage-unified     # Rust + Simple
```

**Week 2: Gradual Adoption**
```bash
# Optional: Enable Simple coverage for specific tests
SIMPLE_COVERAGE=1 cargo test simple_stdlib
```

**Week 3: CI Integration**
```bash
# CI runs unified coverage (non-blocking warnings)
make coverage-unified
make coverage-check-unified || echo "Coverage gaps detected (warning)"
```

**Week 4: Enforcement**
```bash
# CI fails on coverage gaps
make coverage-check-unified  # Exit 1 if thresholds not met
```

---

## Conclusion

Unified coverage reporting bridges the gap between Rust compiler tests and Simple stdlib tests, providing **complete visibility** into end-to-end test coverage.

**Key Benefits:**
- ✅ **100% Visibility** - See exactly what's tested at all levels
- ✅ **Automated Gap Detection** - Catch untested FFI paths automatically
- ✅ **Feature Tracking** - Per-feature coverage dashboards
- ✅ **CI Integration** - Automated coverage checks on every PR

**Implementation:** 4 weeks, 6 new features, backwards-compatible rollout

**Next Steps:**
1. Review and approve this plan
2. Implement Phase 1 (Simple coverage instrumentation)
3. Build coverage merger tool
4. Deploy unified dashboard
5. Integrate with CI

---

**END OF DOCUMENT**
