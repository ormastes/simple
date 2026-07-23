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

# Show progress and resource usage during long lexical scans
simple duplicate-check src/ --mode token --progress
simple duplicate-check src/ --mode cosine --progress --progress-interval-ms 10000

# Tune semantic sensitivity
simple duplicate-check src/ --semantic-threshold 0.92

# Force JSON output
simple duplicate-check src/ --format json
```

Modes:
- `semantic` is the default and looks for documentation/concept duplication. It
  compares candidates across the whole scanned tree, so a clone whose copies
  live in different directories is still reported.
- `token` finds concrete lexical duplication and honors `--min-lines` and `--min-tokens`.
- `cosine` finds fuzzy lexical near-duplicates and honors `--similarity-threshold`, `--min-lines`, and `--min-tokens`.

---

## Modes And Thresholds

`simple duplicate-check` supports:
- `--mode semantic`
- `--mode semantic-llm`
- `--mode token`
- `--mode cosine`

The compatibility aliases `--semantic` and `--cosine` are still accepted. Lexical thresholds are active again:
- `--min-lines`
- `--min-tokens`
- `--min-impact`
- `--similarity-threshold`

Similarity, semantic, and semantic-drift thresholds are probabilities and must
remain between `0` and `1`, inclusive. Invalid CLI or configuration values are
usage errors rather than empty-match success.

Use `--no-default-excludes` when the requested scan root is itself under a
normally excluded directory such as `test/`. Normal newline-terminated source
is counted by logical lines; the terminal split artifact is not a candidate
line or duplicate window.

---

## Progress And Resource Usage

Lexical scans can take longer than a minute on large trees, especially `cosine`.
Use `--progress` to print periodic progress to stderr while keeping stdout
reserved for the normal text or JSON report:

```bash
bin/simple duplicate-check src/compiler --mode token --progress
bin/simple duplicate-check src/compiler --mode cosine --progress --progress-interval-ms 10000
```

Progress lines include phase, completed work, elapsed seconds, and current RSS.
The main phases are:

| Phase | Meaning | Main cost |
| --- | --- | --- |
| `hash pass` | tokenize files and count rolling hashes | roughly linear in tokens |
| `extract pass` | materialize repeated candidate windows | roughly linear in candidate files |
| `feature pass` | build feature vectors for candidate blocks | roughly linear in sampled blocks |
| `compare pass` | pairwise cosine comparison | bounded, but the slowest fuzzy phase |

Expected wall time depends on token count, repeated code density, disk speed, and
whether cache data is warm. As a practical guide on a developer laptop:

| Scope size | Typical command | Expected time | Expected RSS |
| --- | --- | --- | --- |
| 1-25 files / under 20k tokens | `--mode token` | seconds | under 150 MB |
| 25-200 files / 20k-250k tokens | `--mode token --progress` | 10-90 seconds | 100-400 MB |
| 200-1000 files / 250k-1M tokens | `--mode token --progress` | 1-5 minutes | 250-900 MB |
| Any large fuzzy scan | `--mode cosine --progress` | token time plus compare pass; can exceed 5 minutes | 300 MB-1.5 GB |

For refactors, prefer scanning the smallest owned directory first. If token or
cosine mode stays in one phase for several progress intervals, narrow the target
path or raise `--min-lines` / `--min-tokens`.

## Bootstrap Smoke Boundary

The full CLI links the canonical duplicate-check owner in-process; production
evidence must not execute `main.spl` as a raw source worker. After Stage 4,
`scripts/check/check-bootstrap-essential-tools-smoke.shs` runs the exact fresh
binary from a temporary non-repository directory. It requires clean token JSON
to exit 0 with zero groups and an exact clone pair to exit 1 with one group,
two occurrences, and ten duplicated lines. This proves dispatch and a minimal
detector path; it does not replace semantic/cosine or repository-scale checks.
The shared [Stage 4 essential-tools gate](../tooling/pure_simple_tooling.md#stage-4-essential-tools-gate)
also requires the test-runner and lint markers from that same fresh binary.

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

`mode` accepts `semantic`, `semantic-llm`, `token`, or `cosine`;
`output-format` accepts `text` or `json`. The CLI applies explicit flags after
loading this file, then validates the effective values. An invalid value that
is not replaced by a valid CLI override is a configuration error and exits `2`
instead of silently selecting a different analysis or output mode.

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
