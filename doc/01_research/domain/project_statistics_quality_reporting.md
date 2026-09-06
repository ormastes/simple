<!-- codex-research -->
# Domain Research: Project Statistics and Quality Reporting

## Reproducible inventory

Use one machine-readable run record (JSON) and render console/Markdown from
that record. The `scc` project demonstrates multi-language LOC, comments,
blanks, duplicate and complexity rollups, while warning that its complexity is
heuristic and comparable only within a language. This supports labelling any
lexical complexity proxy honestly rather than presenting it as a universal
quality score. [scc documentation](https://github.com/boyter/scc)

## Coverage and modular quality

Coverage must distinguish lines, functions and branches and retain its source,
denominator and exclusions. LLVM's coverage exports contain regions, functions,
branches and summaries, a useful precedent for normalized evidence records.
[llvm-cov](https://www.llvm.org/docs/CommandGuide/llvm-cov.html) and
[Clang source-based coverage](https://clang.llvm.org/docs/SourceBasedCodeCoverage.html).

Coupling is a dependency-graph metric: report fan-in, fan-out, cycles and
cross-project edges. Cohesion needs semantic AST/member-field evidence; if the
analyser does not produce it, report `unavailable`. Microsoft similarly treats
class coupling as unique type/class use and does not prescribe a universal
threshold. [Microsoft code metrics](https://learn.microsoft.com/en-us/visualstudio/code-quality/code-metrics-class-coupling?view=visualstudio).

## Presentation-ready Markdown

Keep an executive conclusion per section, compact tables, provenance and
exclusions. A companion slide-outline Markdown can be converted using Marp or
the repository's Impress/PPTX exporter after theme selection. [Marp](https://marp.app/).

## Recommendation

Adopt a full inventory plus opt-in quality evidence option. This provides the
requested source/test/project counts immediately without making a slow global
clone/coupling scan a hidden default or claiming unavailable cohesion/coverage.
