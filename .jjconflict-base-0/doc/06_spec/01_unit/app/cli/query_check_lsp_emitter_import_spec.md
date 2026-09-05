# `std.report.emitter.lsp` was imported by three CLI modules and never existed

> Three shipped modules —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `std.report.emitter.lsp` was imported by three CLI modules and never existed

Three shipped modules —

## At a Glance

| Field | Value |
|-------|-------|
| Category | App / CLI query — phantom module import (reproducer) |
| Status | Active |
| Source | `test/01_unit/app/cli/query_check_lsp_emitter_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Three shipped modules —

    src/app/cli/query_check.spl:16       use std.report.emitter.lsp.{LspEmitter}
    src/app/cli/query_navigation.spl:12  use std.report.emitter.lsp.{LspEmitter}
    src/app/cli/query_commands.spl:22    use std.report.emitter.lsp.{LspEmitter, LspDiagnostic, LspTextEdit}

— imported a module that has never existed. `find src/lib -type d -name report`
returned nothing. Every `--format json` path in those modules called
`emitter.encode_string(...)`, so all three died at module resolution.

Measured before the fix, on a seed built fresh this session:

    error: semantic: Cannot resolve module: std.report.emitter.lsp    rc=1

Measured after:

    OK "a\"b\nc"                                                     rc=0

The bug doc named only `query_check.spl`; the other two were found while
fixing it and are covered by the same module.

## Why this MUST run in a SUBPROCESS

Module resolution happens when a program is loaded. This spec file is already
loaded by the time any example runs, so an unresolvable import written here
would kill the whole spec file rather than produce an assertion. The import is
therefore exercised by writing a program to disk and running it through
`SIMPLE_BIN`, with the exit status read from an `echo RC=$?` inside the shell
command — never through a pipe, whose status belongs to the last stage.

## What the fix was

`src/lib/common/report/emitter/lsp.spl` now implements `LspEmitter` over the
real, shipped `json_escape_string` from `std.common.json`. Only
`default_emitter()` and `encode_string()` are implemented, because only those
are ever called; `LspDiagnostic`/`LspTextEdit` were named in one import list and
referenced nowhere, so they were removed from that list rather than invented.

`encode_string` returns a COMPLETE JSON string literal, quotes included — every
call site uses it in value position, e.g. `,"code":{emitter.encode_string(code)}`.

## Scenarios

### the CLI query modules' LSP emitter import resolves to a real module

#### loads `std.report.emitter.lsp` and escapes every JSON-significant byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads `std.report.emitter.lsp` and escapes every JSON-significant byte
- Run a program whose only import is the formerly-phantom module
- Refuse to pass on a run that never started
   - Expected: out does not contain `Cannot resolve module`
   - Expected: res.1 equals `0`
- A quoted, complete JSON string literal — quotes are part of the result
- Every escape the LSP wire format requires


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("loads `std.report.emitter.lsp` and escapes every JSON-significant byte")
step("Run a program whose only import is the formerly-phantom module")
val res = run_source("emitter", EMITTER_SOURCE)
val out = res.0

step("Refuse to pass on a run that never started")
# Without this, an empty or error output would satisfy the `not
# contains` assertion below and the example would be vacuously green.
expect(out).to_contain("PLAIN")
expect(out.contains("Cannot resolve module")).to_equal(false)
expect(res.1).to_equal(0)

step("A quoted, complete JSON string literal — quotes are part of the result")
expect(out).to_contain("PLAIN \"abc\"")

step("Every escape the LSP wire format requires")
expect(out).to_contain("QUOTE \"a\\\"b\"")
expect(out).to_contain("NEWLN \"a\\nb\"")
expect(out).to_contain("BSLSH \"a\\\\b\"")
expect(out).to_contain("TAB \"a\\tb\"")
```

</details>

#### leaves no `use std.report` line anywhere that resolves to nothing

- leaves no `use std.report` line anywhere that resolves to nothing
- The three importers must all resolve against a file that exists
- And no importer may name a symbol the module does not define
   - Expected: names.0.trim() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves no `use std.report` line anywhere that resolves to nothing")
step("The three importers must all resolve against a file that exists")
val res = process_run("sh", ["-c",
    "test -f src/lib/common/report/emitter/lsp.spl && echo MODULE-PRESENT " +
    "|| echo MODULE-MISSING"])
expect(res.0).to_contain("MODULE-PRESENT")

step("And no importer may name a symbol the module does not define")
# `LspDiagnostic`/`LspTextEdit` were imported but never referenced;
# re-adding them to an import list without implementing them would
# recreate the defect in a subtler form.
val names = process_run("sh", ["-c",
    "grep -h 'use std.report.emitter.lsp' src/app/cli/*.spl " +
    "| grep -c 'LspDiagnostic\\|LspTextEdit' || true"])
expect(names.0.trim()).to_equal("0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c6fc5522b8da1841a9e117dd0b5df84a994e039f1cb8d1a5b13f3070641c28d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6fc5522b8da1841a9e117dd0b5df84a994e039f1cb8d1a5b13f3070641c28d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6fc5522b8da1841a9e117dd0b5df84a994e039f1cb8d1a5b13f3070641c28d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/query_check_lsp_emitter_import_spec.spl
mirror: doc/06_spec/01_unit/app/cli/query_check_lsp_emitter_import_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/query_check_lsp_emitter_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/query_check_lsp_emitter_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/query_check_lsp_emitter_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/query_check_lsp_emitter_import_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads `std.report.emitter.lsp` and escapes every JSON-significant byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/query_check_lsp_emitter_import_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves no `use std.report` line anywhere that resolves to nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
