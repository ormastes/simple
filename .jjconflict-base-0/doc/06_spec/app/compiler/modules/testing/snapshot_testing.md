# Snapshot/Golden Testing Specification (#899-902)

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** Medium  
**Difficulty:** 2-3

## Overview

Snapshot testing captures and compares output against stored "golden" files, making LLM-generated output regressions obvious and reviewable through diffs.

## Features

### #899: `@snapshot_test` Decorator (Difficulty: 3)

**Syntax:**
```simple
@snapshot_test
@snapshot_test(name: "custom_name")
@snapshot_test(format: "json")
fn test_output():
    let result = generate_output()
    expect_snapshot(result)
```

**Behavior:**
1. On first run: Capture output → save to `.snapshots/` directory
2. On subsequent runs: Compare output to saved snapshot
3. On mismatch: Show diff and fail test
4. Update with `--snapshot-update` flag

### #900: Snapshot Storage (Difficulty: 2)

**Directory Structure:**
```
test/
├── user_service_spec.spl
└── .snapshots/
    └── user_service_spec/
        ├── test_render_user_json.snap
        ├── test_format_address.snap
        └── test_error_messages.snap
```

**Snapshot File Format:**
```yaml
# Snapshot: test_render_user_json
# Created: 2025-12-24 00:10:00 UTC
# Format: json

{
  "id": 42,
  "name": "Alice Smith",
  "email": "alice@example.com",
  "created_at": "2025-01-15T10:30:00Z"
}
```

**Features:**
- Human-readable format (YAML/JSON/Plain text)
- Metadata header (creation date, format, description)
- Git-friendly (line-by-line diffs)
- Organized by test file and function name

### #901: `--snapshot-update` Flag (Difficulty: 2)

**CLI Usage:**
```bash
# Run tests (fail on snapshot mismatch)
simple test user_service_spec.spl

# Update all snapshots
simple test user_service_spec.spl --snapshot-update

# Update specific snapshot
simple test user_service_spec.spl --snapshot-update=test_render_user_json

# Interactive mode (prompt for each mismatch)
simple test --snapshot-update=interactive

# Review mode (show diffs before updating)
simple test --snapshot-review
```

**Environment Variable:**
```bash
SIMPLE_UPDATE_SNAPSHOTS=1 simple test
```

**Safety:**
- Never update automatically in CI
- Require explicit flag or env var
- Show diff before updating (interactive mode)
- Warn if updating many snapshots at once

### #902: Multi-Format Snapshots (Difficulty: 3)

**Supported Formats:**

**JSON:**
```simple
@snapshot_test(format: "json")
fn test_api_response():
    let response = api.get_user(42)
    expect_snapshot(response, format: "json")
```

**YAML:**
```simple
@snapshot_test(format: "yaml")
fn test_config_output():
    let config = generate_config()
    expect_snapshot(config)  # Default: YAML
```

**Plain Text:**
```simple
@snapshot_test(format: "text")
fn test_error_message():
    let err = validate_input("invalid")
    expect_snapshot(err.message)
```

**HTML:**
```simple
@snapshot_test(format: "html")
fn test_render_page():
    let html = render_user_page(user)
    expect_snapshot(html)
```

**Binary (with encoding):**
```simple
@snapshot_test(format: "base64")
fn test_image_generation():
    let image_bytes = render_chart(data)
    expect_snapshot(image_bytes)
```

**Custom Serializers:**
```simple
# Register custom serializer
Snapshot.register_format("csv", to_csv, from_csv)

@snapshot_test(format: "csv")
fn test_export_users():
    let csv = export_users_csv(users)
    expect_snapshot(csv)
```

## Implementation Details

### Snapshot Matching Algorithm

```
1. Load expected snapshot from file
2. Serialize actual output using same format
3. Normalize both (strip timestamps, sort keys, etc.)
4. Compare line-by-line
5. On mismatch:
   - Generate unified diff
   - Show context lines (±3)
   - Highlight differences
   - Report file location
```

### Normalization Strategies

**Timestamp Normalization:**
```simple
@snapshot_test(normalize: true)
fn test_with_timestamps():
    let result = api.create_user("Alice")
    # Timestamps replaced with <TIMESTAMP> placeholder
    expect_snapshot(result)
```

**ID Normalization:**
```simple
@snapshot_test(normalize_ids: true)
fn test_with_generated_ids():
    let users = [create_user("A"), create_user("B")]
    # IDs replaced with <ID-1>, <ID-2>, etc.
    expect_snapshot(users)
```

**Custom Normalization:**
```simple
fn normalize_output(value):
    # Replace volatile data
    value.created_at = "<TIMESTAMP>"
    value.id = "<ID>"
    return value

@snapshot_test(normalizer: normalize_output)
fn test_api_call():
    let result = api.call()
    expect_snapshot(result)
```

### Diff Display

**Unified Diff:**
```diff
Snapshot mismatch: test_render_user_json

Expected: test/.snapshots/user_service_spec/test_render_user_json.snap
Actual:   <test output>

--- Expected
+++ Actual
@@ -1,5 +1,5 @@
 {
   "id": 42,
-  "name": "Alice Smith",
+  "name": "Alice Johnson",
   "email": "alice@example.com",
   "created_at": "2025-01-15T10:30:00Z"
 }

To update this snapshot, run:
  simple test --snapshot-update=test_render_user_json
```

**Side-by-Side Diff (TUI):**
```
┌─ Expected ─────────────────┬─ Actual ───────────────────┐
│ {                          │ {                          │
│   "id": 42,                │   "id": 42,                │
│   "name": "Alice Smith",   │   "name": "Alice Johnson", │ ←
│   "email": "alice@ex...",  │   "email": "alice@ex...",  │
│ }                          │ }                          │
└────────────────────────────┴────────────────────────────┘

[u] Update  [s] Skip  [q] Quit
```

## Benefits for LLM Tools

1. **Regression Detection** - Catch unintended output changes
2. **Reviewable Changes** - Git diffs show exactly what changed
3. **Documentation** - Snapshots serve as examples
4. **No Manual Assertions** - Automatic comparison
5. **LLM Output Validation** - Verify generated code produces correct output

## Implementation Plan

### Phase 1: Core Framework (2 days)
- [ ] `@snapshot_test` decorator parser support
- [ ] Snapshot file I/O (read/write)
- [ ] Basic comparison (string equality)
- [ ] `.snapshots/` directory management
- [ ] Failure reporting

### Phase 2: Update Mechanism (1 day)
- [ ] `--snapshot-update` CLI flag
- [ ] Selective update by test name
- [ ] Safety checks (prevent CI updates)
- [ ] Update confirmation prompts

### Phase 3: Format Support (2 days)
- [ ] JSON serialization/comparison
- [ ] YAML serialization/comparison
- [ ] Plain text handling
- [ ] HTML formatting
- [ ] Binary/base64 encoding
- [ ] Custom serializer registration

### Phase 4: Normalization (1 day)
- [ ] Timestamp normalization
- [ ] ID normalization
- [ ] Custom normalizer support
- [ ] Whitespace/formatting normalization
- [ ] Configuration options

### Phase 5: Diff Display (1 day)
- [ ] Unified diff generation
- [ ] Color-coded output
- [ ] Context lines (±3)
- [ ] Line number annotations
- [ ] Side-by-side diff (TUI optional)

### Phase 6: Interactive Mode (1 day)
- [ ] Prompt for each mismatch
- [ ] Show diff before update
- [ ] Batch update options
- [ ] Review mode with git diff

**Total Estimated Effort:** 8 days

## File Structure

```
simple/std_lib/src/testing/snapshot/
├── __init__.spl          # Main exports
├── decorator.spl         # @snapshot_test implementation
├── storage.spl           # File I/O operations
├── formats/
│   ├── json.spl          # JSON serialization
│   ├── yaml.spl          # YAML serialization
│   ├── text.spl          # Plain text
│   └── custom.spl        # Custom format registry
├── comparison.spl        # Snapshot comparison
├── normalization.spl     # Data normalization
├── diff.spl              # Diff generation
└── update.spl            # Update mechanism

simple/std_lib/test/system/snapshot/
├── basic_spec.spl        # Basic snapshot tests
├── formats_spec.spl      # Format tests
├── update_spec.spl       # Update mechanism tests
└── normalization_spec.spl # Normalization tests
```

## Example Use Cases

### 1. API Response Testing
```simple
@snapshot_test(format: "json")
fn test_get_user_api():
    let response = api.get_user(42)
    expect_snapshot(response)
```

### 2. HTML Rendering
```simple
@snapshot_test(format: "html", name: "user_profile_page")
fn test_render_user_profile():
    let html = render_profile(user)
    expect_snapshot(html)
```

### 3. Error Messages
```simple
@snapshot_test
fn test_validation_errors():
    let errors = validate_form(invalid_data)
    expect_snapshot(errors.to_string())
```

### 4. Configuration Output
```simple
@snapshot_test(format: "yaml")
fn test_generate_config():
    let config = generate_nginx_config(app_settings)
    expect_snapshot(config)
```

### 5. CSV Export
```simple
@snapshot_test(format: "csv")
fn test_export_report():
    let csv = generate_report(data)
    expect_snapshot(csv)
```

## CI Integration

**GitLab CI:**
```yaml
test:
  script:
    - simple test --snapshot-fail-on-missing
    - simple test --no-snapshot-update
```

**GitHub Actions:**
```yaml
- name: Run tests
  run: simple test
  env:
    CI: true  # Prevents snapshot updates
```

**Pre-commit Hook:**
```bash
#!/bin/bash
# Check for modified snapshots without --snapshot-update
if git diff --cached --name-only | grep -q ".snapshots/"; then
  echo "Warning: Snapshot files modified"
  echo "Run 'simple test --snapshot-review' to verify changes"
fi
```

## Related Features

- #894-898: Property-based testing (complementary)
- #908-910: Canonical formatter (consistent output)
- #914: API surface lock file (similar concept)

## Success Metrics

- [ ] 50+ snapshot tests in stdlib
- [ ] Zero false positives (normalization works)
- [ ] <1 minute to review and update snapshots
- [ ] LLM output changes detected immediately
- [ ] 90%+ developer satisfaction

## References

- **Jest** (JavaScript) - Popular snapshot testing framework
- **Insta** (Rust) - Snapshot testing for Rust
- **Approval Tests** - Golden master testing concept
- **pytest-snapshot** (Python) - Python snapshot testing

---

**Next Steps:**
1. Review and approve specification
2. Implement Phase 1 (core framework)
3. Add to feature.md when complete
4. Create example test suite
