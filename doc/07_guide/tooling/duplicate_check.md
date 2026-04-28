# Code Duplication Detection Guide

`simple duplicate-check` now runs semantic documentation similarity analysis by default.

---

## Quick Start

```bash
# Scan a directory with semantic analysis
simple duplicate-check src/

# Scan a focused subtree
simple duplicate-check src/app/

# Tune semantic sensitivity
simple duplicate-check src/ --semantic-threshold 0.92

# Force JSON output
simple duplicate-check src/ --format json
```

`--semantic` is still accepted, but it is optional because semantic analysis is already the default.

---

## Compatibility With Removed Lexical Modes

Legacy lexical flags such as `--min-tokens`, `--min-lines`, `--min-impact`, `--cosine`, `--parallel`, `--jobs`, `--no-cache`, and `--cache-path` are still accepted temporarily.

When those flags are used, `simple duplicate-check` prints a deprecation warning and continues with semantic-only analysis. The command no longer performs token-window or cosine/token-feature duplication scans.

---

## Configuration

Create `simple.duplicate-check.sdn` in the project root:

```sdn
duplicate-check:
  output-format: text
  max-allowed: 0

  use-semantic: true
  semantic-threshold: 0.90
  semantic-drift-threshold: 0.40
  semantic-model: nomic-embed-text
  ollama-url: http://localhost:11434
  rebuild-embeddings: false

  exclude:
    - "test/"
    - "doc/"
    - "**/*_spec.spl"
    - "**/*_test.spl"
```

Lexical config keys may still parse for migration compatibility, but they no longer affect command behavior.

---

## Output Modes

```bash
simple duplicate-check src/ --format=json > duplicates.json
simple duplicate-check src/ --max-allowed 5
```

- `text` prints the semantic similarity report.
- `json` emits semantic matches and summary fields.

---

## Ollama And Fallback Behavior

Semantic mode uses Ollama embeddings only when `SIMPLE_DUPCHECK_USE_OLLAMA_HTTP=1` is set and Ollama is reachable.

If Ollama is unavailable, the command prints a warning and falls back to local text-based similarity scoring so the CLI still completes.

---

## Understanding Results

The report focuses on:

1. Similar documented items whose comments appear copy-pasted or near-identical.
2. Missing documentation coverage in the scanned scope.
3. Optional drift warnings when semantic scoring indicates documentation mismatch behavior.

Example:

```text
Semantic Doc Similarity Report
==============================

Source: 42 items, 31 documented [text-based fallback]

Similar Docs (>0.90): 2 pairs
  [1.00] src/app/a.spl:add_score (L2) <-> src/app/b.spl:merge_score (L2) [COPY-PASTE]
```

---

## CI Integration

```yaml
- name: Check semantic doc duplication
  run: |
    bin/simple duplicate-check src/ --format=json > duplicates.json
    bin/simple duplicate-check src/ --max-allowed=5
```

---

## Related Commands

- `simple lint` — Code quality linting
- `simple fmt` — Code formatting
- `simple build check` — Aggregate quality checks
