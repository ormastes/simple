# Code Duplication Detection Guide

`simple duplicate-check` is a multi-mode duplication toolkit behind one CLI entrypoint.

---

## Quick Start

```bash
# Scan a directory with semantic analysis
simple duplicate-check src/

# Run lexical duplicate detection at the refactor default
simple duplicate-check src/app/ --mode token --min-lines 5

# Run fuzzy lexical similarity
simple duplicate-check src/ --mode cosine --similarity-threshold 0.85

# Tune semantic sensitivity
simple duplicate-check src/ --semantic-threshold 0.92

# Force JSON output
simple duplicate-check src/ --format json
```

Modes:
- `semantic` is the default and looks for documentation/concept duplication.
- `token` finds concrete lexical duplication and honors `--min-lines` and `--min-tokens`.
- `cosine` finds fuzzy lexical near-duplicates and honors `--similarity-threshold`, `--min-lines`, and `--min-tokens`.

---

## Modes And Thresholds

`simple duplicate-check` supports:
- `--mode semantic`
- `--mode token`
- `--mode cosine`

The compatibility aliases `--semantic` and `--cosine` are still accepted. Lexical thresholds are active again:
- `--min-lines`
- `--min-tokens`
- `--min-impact`
- `--similarity-threshold`

---

## Configuration

Create `simple.duplicate-check.sdn` in the project root:

```sdn
duplicate-check:
  output-format: text
  max-allowed: 0
  mode: semantic

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
  min-lines: 5
  min-tokens: 30
  similarity-threshold: 0.85
```

---

## Output Modes

```bash
simple duplicate-check src/ --format=json > duplicates.json
simple duplicate-check src/ --max-allowed 5
```

- `text` prints a mode-specific report.
- `json` emits a stable top-level `mode` field plus mode-specific result arrays.

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

## Refactor Workflow

For refactors, run:
- `bin/simple duplicate-check <dir> --mode semantic`
- `bin/simple duplicate-check <dir> --mode token --min-lines 5`
- `bin/simple duplicate-check <dir> --mode cosine --similarity-threshold 0.85`

Use token mode as the default concrete extraction pass before helper consolidation.

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
