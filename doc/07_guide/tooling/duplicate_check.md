# Code Duplication Detection Guide

The Simple compiler includes a built-in code duplication detector using Karp-Rabin rolling hash with token-based analysis.

---

## Quick Start

```bash
# Scan directory
simple duplicate-check src/

# Scan specific path
simple duplicate-check src/app/

# Run via build system
simple build duplication

# Include in all quality checks
simple build check
```

---

## Configuration

Create `simple.duplicate-check.sdn` in the project root:

```sdn
duplicate-check:
  min-tokens: 30              # Minimum tokens per duplicate block
  min-lines: 5                # Minimum lines per duplicate block
  min-impact: 100             # Minimum impact score (occurrences x lines)

  ignore-identifiers: true    # Treat all identifiers as equivalent
  ignore-literals: false      # Keep literal values distinct
  ignore-comments: true       # Skip comments
  ignore-whitespace: true     # Normalize whitespace

  output-format: text         # text | json | sdn
  report-path: doc/analysis/duplicate_db.sdn
  max-allowed: 0              # Fail build if > N duplicates

  exclude:
    - "test/"
    - "doc/"
    - "**/*_spec.spl"
    - "**/*_test.spl"
```

### Command-Line Options

```bash
simple duplicate-check src/ --min-tokens 20 --min-lines 5
simple duplicate-check src/ --min-impact 50
simple duplicate-check src/ --format json
simple duplicate-check src/ --exclude "vendor/"
simple duplicate-check src/ --max-allowed 5
```

### Duplication Modes

```bash
# Exact token-window duplication, using the default five-line minimum
simple duplicate-check src/ --min-lines 5

# Cosine similarity over token-frequency vectors
simple duplicate-check src/ --cosine --min-lines 5

# Semantic documentation similarity
simple duplicate-check src/ --semantic
```

Cosine mode preserves identifier and literal detail so unrelated helpers are not collapsed by normalization. Semantic mode uses Ollama embeddings only when `SIMPLE_DUPCHECK_USE_OLLAMA_HTTP=1` is set; otherwise it prints a text-based fallback notice and uses local text similarity.

---

## Understanding Results

**Impact Score = Occurrences x Lines per Block** -- higher scores indicate more significant duplication.

### Text Output

```
Found 3 duplicate groups (142 total lines duplicated)

1. Impact Score: 140 (5 occurrences, 28 lines each)
   Files:
   - src/app/ffi_gen/specs/cranelift_ops.spl:34-42
   - src/app/ffi_gen/specs/cranelift_advanced.spl:25-33
   Code preview:
      let mut contexts = FUNC_CONTEXTS.lock().unwrap();
      ...
```

### JSON Output

```bash
simple duplicate-check src/ --format=json > duplicates.json
simple duplicate-check src/ --format=json | jq '.summary.total_groups'
```

### SDN Database

```bash
simple duplicate-check src/ --format=sdn
# Creates doc/analysis/duplicate_db.sdn
```

---

## Detection Algorithm

1. **Tokenize** -- Convert source to tokens (keywords, identifiers, operators, literals)
2. **Normalize** -- Apply configured normalizations
3. **Hash** -- Compute rolling hashes over token windows
4. **Match** -- Find identical hash sequences across files
5. **Group** -- Group matching blocks by hash
6. **Rank** -- Sort by impact score

With `ignore-identifiers: true`, structurally similar code is detected even with different variable names:

```simple
# These are detected as duplicates:
fn process_user(user_id):
    val user = fetch_user(user_id)
    val data = transform(user)
    return save_result(data)

fn handle_item(item_id):
    val item = fetch_item(item_id)
    val result = transform(item)
    return save_result(result)
```

---

## Best Practices

1. **Start with high thresholds** (`min-impact: 100`) to focus on significant duplicates
2. **Enable identifier normalization** to find structural duplicates
3. **Exclude test code** -- tests often have intentional duplication
4. **Track over time** -- commit `duplicate_db.sdn` and use `--max-allowed` in CI
5. **Refactor incrementally** -- start with highest impact scores, extract helpers

---

## CI/CD Integration

```yaml
- name: Check Code Duplication
  run: |
    bin/simple duplicate-check src/ --format=json > duplicates.json
    bin/simple duplicate-check src/ --max-allowed=5
```

---

## Troubleshooting

**Slow performance**: Use exclusion patterns, increase `min-tokens`, or run only on changed files.

**False positives**: Increase `min-tokens` and `min-lines`, or use `ignore-identifiers: false`.

**False negatives**: Enable `ignore-identifiers: true` and `ignore-literals: true`, lower `min-impact`.

---

## Related Commands

- `simple lint` -- Code quality linting
- `simple fmt` -- Code formatting
- `simple build check` -- All quality checks (includes duplication)
