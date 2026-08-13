# Statistics Module

Provides the `simple stats` command to display project metrics.

## Current Implementation

**Active:** `dynamic.spl` - Dynamically computes statistics using shell commands

## Usage

```bash
# Show statistics
simple stats

# Brief output (no docs section)
simple stats --brief

# Verbose output (with directory details)
simple stats --verbose

# Write the default doc/09_report/project_statistics.md report
simple stats

# Select or disable the Markdown report
simple stats --report=build/project-statistics.md
simple stats --no-report

# Include retained or freshly generated quality evidence
simple stats --quality=summary
simple stats --quality=full

# Presentation artifacts (defaults shown)
simple stats --tldr=doc/09_report/project_statistics_tldr.md \
  --slides=doc/09_report/project_statistics_slides.md \
  --pptx=doc/09_report/project_statistics.pptx
```

## Statistics Displayed

- **Files**: Source file counts by category (app/lib/std)
- **Lines of Code**: Total LOC in source files
- **Tests**: Test counts and pass rates from test_result.md
- **Features**: Feature counts by status from feature_db.sdn
- **Documentation**: Links to detailed reports
- **Projects**: Disjoint source/test files and SLOC by compiler, app, library,
  OS, runtime, hardware, verification, tooling and examples
- **Focus areas**: Non-additive firmware, RISC-V, DB/web server,
  UI/rendering, Office, CRM, Agent Caret, Agents Manager, and SPipe views
- **Quality evidence**: Coverage, duplication, coupling and cohesion with
  measured/stale/unavailable status

## Implementation Notes

### Dynamic Approach (Current)

Uses `process_run` to execute shell commands for counting:
- `find` for file counts
- `grep -c` for pattern matching in databases
- `wc -l` for line counting

Owned-code counts exclude vendored and third-party runtime source:
`*/vendor/*`, `*/third_party/*`, `*/external/*`, `miniaudio.h`,
`stb_image.h`, and `stb_truetype.h`.

File-count buckets are disjoint: `app` counts `src/app`, `lib` counts
`src/lib`, `std` counts `src/std` plus `src/i18n`, `core` counts `src/core`,
and `compiler` is the remaining owned `.spl` source under `src`.

### Future Modules (Prepared)

- `types.spl` - Data structures for statistics
- `file_scanner.spl` - Directory walking logic
- `line_counter.spl` - LOC analysis
- `db_aggregator.spl` - Database parsing
- `formatter.spl` - Output formatting
- `main.spl` - Full implementation (blocked by runtime issues)

## Performance

Typical execution time: 2-3 seconds for full project scan

## See Also

- Test results: `doc/08_tracking/test/test_result.md`
- Feature tracking: `doc/08_tracking/feature/feature.md`
- Build status: `doc/08_tracking/build/recent_build.md`
# Project Statistics

`simple stats` summarizes owned project files, source lines, executable test
surfaces, tracked features, and available coverage evidence. A normal run also
writes `doc/09_report/project_statistics.md`.

Use `--report=<path>` (or `--report <path>`) to choose another Markdown output
and `--no-report` for read-only console/JSON use. `--quick` skips expensive LOC
analysis; its report retains zero for metrics that were deliberately skipped.

The report excludes vendored/third-party source and excludes `*_tldr.md` from
Markdown file/test counts. Runnable test LOC is reported separately for SSpec
files, fenced Markdown examples, and `>>>` source-comment SDoctests so these
tests are visible without inflating production Simple SLOC.
