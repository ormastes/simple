# Bug Database

The bug database is stored in `doc/08_tracking/bug/bug_db.sdn`, an SDN file with CRC32 integrity checking.

## Tables

### bugs_active and bugs
Core bug tracking tables with the same schema:
- **id**: Unique bug identifier (e.g., `native_parser_nested_quotes_2026_10_19`)
- **severity**: P0-P4 priority level
- **status**: open, investigating, fix-implemented-verification-pending, closed, fixed, invalid, resolved-*
- **title**: Short description of the bug
- **file**: Primary source file where the bug manifests
- **line**: Line number in that file
- **reproducible_by**: Model/person who can reproduce it
- **created_at**: YYYY-MM-DD creation date
- **updated_at**: YYYY-MM-DD last update date
- **valid**: Boolean; true if row was formally verified, false if pending review

### bug_descriptions
Extended descriptions for bugs (one or more rows per bug_id):
- **bug_id**: References a bug from bugs_active or bugs
- **line_num**: Sequential line number (0, 1, 2, ...)
- **content**: Full description text, often with reproduction steps and evidence

### bug_difficulty (NEW)
Difficulty assessment and history for bugs. Multiple rows per bug_id allowed (newest assessed_at wins):
- **bug_id**: References a bug from bugs_active or bugs
- **difficulty**: 1-5 scale:
  - 1 = trivial (one-line spec fix, doc typo)
  - 2 = easy (single-site obvious fix)
  - 3 = medium (contained code fix in one module with known cause)
  - 4 = hard (cross-module, compiler/codegen/ABI, unclear root cause, or needs repro)
  - 5 = very-hard (miscompile/concurrency/memory corruption, needs bisect, or blocks bootstrap)
- **basis**: Quoted reason drawn from the bug title/description (e.g., "one-line spec fix")
- **assessed_at**: YYYY-MM-DD assessment date
- **assessed_by**: Model/lane that performed assessment (e.g., haiku-difficulty, sonnet-triage-p1)

### bug_investigation_logs
Investigation notes and findings (one or more rows per bug_id):
- **bug_id**: References a bug from bugs_active or bugs
- **line_num**: Sequential line number
- **content**: Investigation details, workarounds, related issues

### bug_fix_strategies
Proposed and implemented fix strategies (one or more rows per bug_id):
- **bug_id**: References a bug from bugs_active or bugs
- **line_num**: Sequential line number
- **content**: Fix approach, design notes, implementation plan

### strings
Shared string table for efficient storage:
- **id**: Unique string identifier
- **value**: The string content

## Coverage Requirements

All non-closed bugs (status != closed/fixed/invalid/resolved-*) must have at least one row in bug_difficulty.

This is enforced by the coverage check in `scripts/check/check-bug-difficulty-coverage.shs`, which is integrated into the CI gates.

## Integrity

The file begins with a CRC32 checksum header:
```
#sdn-crc32:NNNNNNNNNN
```

After hand-editing, reseal with:
```bash
sh scripts/check/reseal-sdn-crc32.shs doc/08_tracking/bug/bug_db.sdn
```

The checksum is fail-CLOSED: a mismatch makes the entire database load as nil.

## Filing New Bugs

When creating a new bug, include:
1. A title (required)
2. One or more rows in bug_descriptions with details (required)
3. Initial severity (P0-P4)
4. Status (usually "open")
5. A bug_difficulty row (required for non-closed status)

Use a date-based ID when appropriate: `problem_description_YYYY_MM_DD`
