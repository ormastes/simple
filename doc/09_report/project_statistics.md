# Project Statistics

> Best-effort 2026-08-13 inventory after the self-hosted generator build stalled. Counts follow `StatsInventoryV2`; generated, vendored, and `*_tldr.md` files are excluded. Native PPTX generation remains blocked and is listed below.

## Executive Summary

| Metric | Value |
|---|---:|
| Owned source/test files | 41,544 |
| Owned source/test SLOC | 7,307,459 |
| Source SLOC | 4,767,640 |
| Project test SLOC | 2,539,819 |
| All language/doc files | 59,511 |
| All language/doc SLOC | 11,020,829 |
| Markdown files (non-TLDR) | 17,897 |

## Project Totals

| Project | Total files | Total SLOC |
|---|---:|---:|
| compiler | 7,350 | 1,316,555 |
| app | 5,881 | 2,482,941 |
| lib/std/core | 12,075 | 1,382,111 |
| OS | 3,625 | 539,594 |
| runtime | 259 | 66,245 |
| hardware | 537 | 72,182 |
| verification | 9,273 | 1,060,797 |
| tooling | 1,094 | 208,397 |
| examples | 1,066 | 172,275 |
| remaining source | 384 | 6,362 |

## Source and Test Split

| Project | Source SLOC | Test SLOC |
|---|---:|---:|
| compiler | 939,191 | 377,364 |
| app | 2,160,947 | 321,994 |
| lib/std/core | 879,228 | 502,883 |
| OS | 310,909 | 228,685 |
| runtime | 57,486 | 8,759 |
| hardware | 40,115 | 32,067 |
| verification | 0 | 1,060,797 |
| tooling | 207,620 | 777 |
| examples | 165,782 | 6,493 |
| remaining source | 6,362 | 0 |

## Focus Areas (non-additive)

| Focus | Files | SLOC | Source SLOC | Test SLOC |
|---|---:|---:|---:|---:|
| firmware | 933 | 144,505 | 124,042 | 20,463 |
| RISC-V | 1,290 | 138,412 | 83,826 | 54,586 |
| DB server | 20 | 2,892 | 1,151 | 1,741 |
| Web server | 27 | 2,078 | 728 | 1,350 |
| UI/rendering | 1,784 | 293,796 | 178,431 | 115,365 |
| Office | 288 | 50,930 | 32,399 | 18,531 |
| CRM | 1 | 84 | 84 | 0 |
| Agent Caret | 1,057 | 91,525 | 72,538 | 18,987 |
| Agents Manager | 42 | 2,148 | 2,068 | 80 |
| SPipe | 334 | 49,383 | 13,612 | 35,771 |

## Languages

| Language | Files | SLOC |
|---|---:|---:|
| Simple | 37,642 | 4,534,742 |
| Rust | 1,735 | 562,725 |
| C/C++/headers/assembly | 577 | 167,252 |
| Scripts | 1,660 | 2,050,242 |
| Markdown | 17,897 | 3,705,868 |

## Test Inventory

| Test surface | Files | Runnable SLOC |
|---|---:|---:|
| SSpec total | 22,037 | 2,425,868 |
| Unit | 13,479 | 1,523,586 |
| Integration | 1,557 | 140,868 |
| System | 5,539 | 631,087 |
| Other | 1,462 | 130,327 |
| Markdown fenced tests | 10,124 | 761,179 |
| Comment SDoctests | 63 | 549 |
| Total runnable surfaces | 32,224 | 3,187,596 |

## Quality Evidence

| Metric | Status | Evidence |
|---|---|---|
| Coverage | unavailable | retained table has schema only, no measured rows |
| Duplication | unavailable | retained table has schema only, no measured rows |
| Coupling | unavailable | no current coupling JSON artifact |
| Cohesion | unavailable | no current LCOM evidence artifact |

## Generation Limitations

- The feature system spec passes after repairing the shared multi-line boolean parser hazard.
- The strict full-CLI build was stopped after making no object-cache progress; log: `build/mini_builds/project-stats-native-build.log`.
- The stale self-hosted candidate cannot parse current `process_ops.spl` and is not accepted provenance.
- `project_statistics.pptx` was not fabricated; native conversion requires a current admitted pure-Simple CLI.
