# Build & Audit Infrastructure Specification (#911-915)

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** Medium  
**Difficulty:** 2-3

## Overview

Build and audit infrastructure to ensure reproducibility, track LLM-generated code provenance, and measure specification coverage. Makes LLM output auditable and builds deterministic.

## Features

### #911: Deterministic Build Mode (Difficulty: 3)

**Goal:** Produce byte-identical binaries from same source, regardless of build environment.

**Requirements:**
- Stable symbol ordering
- Reproducible timestamps
- Deterministic random seeds
- Fixed compiler version info
- Canonical file paths

**Implementation:**
```bash
# Enable deterministic mode
simple compile --deterministic app.spl

# Set build timestamp explicitly
simple compile --build-timestamp=2025-01-15T10:00:00Z app.spl

# Verify reproducibility
simple compile --deterministic app.spl -o build1.smf
simple compile --deterministic app.spl -o build2.smf
diff build1.smf build2.smf  # Should be identical
```

**Features:**
- Stable symbol table ordering (alphabetical)
- Reproducible UUID generation (seeded)
- Build timestamp override
- Source path normalization (relative paths)
- Deterministic random number seeds

**Configuration:**
```toml
# simple.toml
[build]
deterministic = true
timestamp = "2025-01-15T10:00:00Z"
seed = 42
normalize_paths = true
```

### #912: Replay Logs (Difficulty: 3)

**Goal:** Record and replay compilation sessions for debugging and auditing.

**Log Format:**
```json
{
  "session_id": "550e8400-e29b-41d4-a716-446655440000",
  "timestamp": "2025-01-15T10:30:00Z",
  "compiler_version": "0.1.0",
  "command": "simple compile app.spl",
  "environment": {
    "SIMPLE_LOG": "debug",
    "working_dir": "/home/user/project"
  },
  "inputs": {
    "source_files": ["app.spl", "lib.spl"],
    "dependencies": {"http": "1.0.0"}
  },
  "phases": [
    {
      "name": "parse",
      "duration_ms": 50,
      "result": "success"
    },
    {
      "name": "type_check",
      "duration_ms": 120,
      "result": "success"
    }
  ],
  "output": {
    "binary": "app.smf",
    "size_bytes": 102400,
    "hash": "sha256:abc123..."
  }
}
```

**Usage:**
```bash
# Enable logging
simple compile --log=build.json app.spl

# Replay build
simple replay build.json

# Compare builds
simple replay --compare build1.json build2.json

# Extract diagnostics
simple replay --extract-errors build.json
```

**Features:**
- Record all compilation phases
- Timing information
- Input/output file tracking
- Error/warning capture
- Environment variables
- Replay for debugging

### #913: `@generated_by` Provenance (Difficulty: 2)

**Goal:** Track LLM-generated code with metadata for auditing.

**Syntax:**
```simple
# Function-level provenance
@generated_by(
    tool: "claude",
    version: "3.5",
    prompt_hash: "sha256:abc123...",
    timestamp: "2025-01-15T10:30:00Z"
)
fn calculate_tax(amount: i64) -> i64:
    return amount * 0.15

# Module-level provenance
@generated_by(tool: "copilot", session: "sess_12345")
module generated.validators:
    ...

# With verification
@generated_by(
    tool: "claude",
    verified: true,
    reviewer: "alice@example.com",
    review_date: "2025-01-16"
)
fn process_payment(order: Order) -> Result<Payment>:
    ...
```

**Metadata Captured:**
- Tool name and version
- Prompt hash (for reproducibility)
- Generation timestamp
- Session/request ID
- Human verification info
- Review status

**Queries:**
```bash
# Find all generated code
simple query --generated

# Find unverified generated code
simple query --generated --unverified

# Find code by specific tool
simple query --generated-by=claude

# Show provenance for function
simple info calculate_tax --provenance
```

**Output:**
```
Function: calculate_tax
Provenance:
  Tool: claude v3.5
  Generated: 2025-01-15 10:30:00 UTC
  Prompt hash: sha256:abc123...
  Status: verified
  Reviewer: alice@example.com
  Review date: 2025-01-16
```

### #914: API Surface Lock File (✅ Already Complete)

**Status:** ✅ Implemented

See `doc/LLM_FRIENDLY_API_SURFACE.md` for details.

### #915: Spec Coverage Metric (Difficulty: 3)

**Goal:** Measure how much of the language specification is covered by tests and implementations.

**Specification Tracking:**
```yaml
# specs/language.yaml
features:
  - id: pattern_matching
    spec: "doc/spec/language.md#pattern-matching"
    status: implemented
    tests:
      - "tests/pattern_matching_spec.rs"
      - "tests/exhaustiveness_spec.rs"
    coverage: 95.0
  
  - id: async_await
    spec: "doc/spec/concurrency.md#async-await"
    status: partial
    tests:
      - "tests/async_spec.rs"
    coverage: 70.0
    missing:
      - "async generators"
      - "async drop"
```

**Commands:**
```bash
# Show overall coverage
simple spec-coverage
Output:
  Total features: 150
  Implemented: 120 (80%)
  Tested: 110 (73%)
  Coverage: 85.5%

# Show by category
simple spec-coverage --by-category
Output:
  Core Language: 95%
  Concurrency: 70%
  Memory Management: 90%
  Type System: 85%

# Find untested features
simple spec-coverage --missing
Output:
  - Async generators (spec: doc/spec/concurrency.md#async-gen)
  - Capability inference (spec: doc/spec/memory.md#capabilities)
  - SIMD operations (spec: doc/spec/gpu_simd.md#simd)

# Generate coverage report
simple spec-coverage --report=html > coverage.html
```

**HTML Report:**
```html
<!DOCTYPE html>
<html>
<head><title>Spec Coverage Report</title></head>
<body>
  <h1>Simple Language Specification Coverage</h1>
  <div class="summary">
    <div class="metric">
      <span class="label">Overall Coverage</span>
      <span class="value">85.5%</span>
      <div class="progress" style="width: 85.5%"></div>
    </div>
  </div>
  
  <table>
    <tr>
      <th>Feature</th>
      <th>Status</th>
      <th>Tests</th>
      <th>Coverage</th>
    </tr>
    <tr class="implemented">
      <td>Pattern Matching</td>
      <td>✓ Implemented</td>
      <td>2 test files</td>
      <td>95%</td>
    </tr>
    <tr class="partial">
      <td>Async/Await</td>
      <td>⚠ Partial</td>
      <td>1 test file</td>
      <td>70%</td>
    </tr>
  </table>
</body>
</html>
```

## Implementation

### Deterministic Build

**Symbol Ordering:**
```rust
// Sort symbols alphabetically before emission
symbols.sort_by(|a, b| a.name.cmp(&b.name));

// Use stable random seed
let mut rng = StdRng::seed_from_u64(build_config.seed);

// Normalize paths to relative
fn normalize_path(path: &Path, root: &Path) -> PathBuf {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_path_buf()
}
```

**Timestamp Override:**
```rust
let build_timestamp = if let Some(ts) = config.timestamp {
    ts
} else {
    SystemTime::now()
};
```

### Replay Logs

**Logging Framework:**
```rust
struct BuildLogger {
    session_id: Uuid,
    phases: Vec<Phase>,
    start_time: Instant,
}

impl BuildLogger {
    fn log_phase(&mut self, name: &str, result: Result<()>) {
        let phase = Phase {
            name: name.to_string(),
            duration: self.start_time.elapsed(),
            result,
        };
        self.phases.push(phase);
    }
    
    fn save(&self, path: &Path) -> Result<()> {
        let json = serde_json::to_string_pretty(self)?;
        fs::write(path, json)
    }
}
```

### Provenance Decorator

**AST Node:**
```rust
#[derive(Debug, Clone)]
pub struct Provenance {
    pub tool: String,
    pub version: Option<String>,
    pub prompt_hash: Option<String>,
    pub timestamp: Option<DateTime<Utc>>,
    pub session_id: Option<String>,
    pub verified: bool,
    pub reviewer: Option<String>,
    pub review_date: Option<NaiveDate>,
}

pub struct FunctionDef {
    pub name: String,
    pub provenance: Option<Provenance>,
    // ... other fields
}
```

**Parser Support:**
```rust
fn parse_generated_by_decorator(&mut self) -> Result<Provenance> {
    self.expect(Token::At)?;
    self.expect_ident("generated_by")?;
    self.expect(Token::LParen)?;
    
    let mut prov = Provenance::default();
    
    // Parse key-value pairs
    while self.current() != Token::RParen {
        let key = self.expect_ident()?;
        self.expect(Token::Colon)?;
        
        match key.as_str() {
            "tool" => prov.tool = self.expect_string()?,
            "version" => prov.version = Some(self.expect_string()?),
            "prompt_hash" => prov.prompt_hash = Some(self.expect_string()?),
            // ... other fields
            _ => return Err(ParseError::UnknownProvenanceField(key)),
        }
        
        if self.current() == Token::Comma {
            self.advance();
        }
    }
    
    self.expect(Token::RParen)?;
    Ok(prov)
}
```

### Spec Coverage

**Coverage Tracker:**
```rust
struct SpecCoverage {
    features: HashMap<String, FeatureCoverage>,
}

struct FeatureCoverage {
    id: String,
    spec_location: String,
    status: FeatureStatus,
    tests: Vec<String>,
    coverage_percent: f64,
    missing_items: Vec<String>,
}

impl SpecCoverage {
    fn compute_overall(&self) -> f64 {
        let total = self.features.len() as f64;
        let covered: f64 = self.features.values()
            .map(|f| f.coverage_percent / 100.0)
            .sum();
        (covered / total) * 100.0
    }
    
    fn report_html(&self) -> String {
        // Generate HTML report
    }
}
```

## Benefits for LLM Tools

1. **Reproducibility** - Same code → same binary every time
2. **Auditability** - Track LLM-generated code origin
3. **Debugging** - Replay failed builds
4. **Verification** - Review generated code with provenance
5. **Coverage** - Identify untested features

## Implementation Plan

### Phase 1: Deterministic Build (2 days)
- [ ] Symbol ordering (alphabetical)
- [ ] Timestamp override support
- [ ] Random seed configuration
- [ ] Path normalization
- [ ] Tests for reproducibility

### Phase 2: Replay Logs (2 days)
- [ ] Build logger framework
- [ ] JSON log format
- [ ] Phase tracking
- [ ] Replay command
- [ ] Comparison tool

### Phase 3: Provenance (1 day)
- [ ] `@generated_by` decorator parser
- [ ] AST node support
- [ ] Query commands
- [ ] Verification tracking
- [ ] Provenance display

### Phase 4: Spec Coverage (2 days)
- [ ] Specification YAML format
- [ ] Coverage computation
- [ ] HTML report generation
- [ ] Missing feature detection
- [ ] Category grouping

**Total Estimated Effort:** 7 days

## File Structure

```
src/compiler/src/audit/
├── mod.rs                 # Main exports
├── deterministic.rs       # Deterministic build
├── replay.rs              # Build replay
├── provenance.rs          # Provenance tracking
└── spec_coverage.rs       # Coverage metrics

specs/
├── language.yaml          # Language spec tracking
├── stdlib.yaml            # Stdlib spec tracking
└── runtime.yaml           # Runtime spec tracking

tools/
└── spec-coverage.sh       # Coverage report generator
```

## Related Features

- #888: JSON error format (similar logging)
- #890-893: Context pack (audit information)
- #894-898: Property tests (coverage)
- #899-902: Snapshot tests (reproducibility)

## Success Metrics

- [ ] 100% reproducible builds
- [ ] All LLM code has provenance
- [ ] 90%+ spec coverage
- [ ] <1s to generate coverage report
- [ ] Zero false positives in provenance

---

**Next Steps:**
1. Review and approve specification
2. Implement deterministic build first
3. Add provenance tracking
4. Create spec coverage tool
5. Add to feature.md when complete
