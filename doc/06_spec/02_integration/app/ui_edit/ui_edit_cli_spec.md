# Create an HTML/CSS pair

> ui_edit CLI Integration Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Create an HTML/CSS pair

ui_edit CLI Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | html_ui_toolchain AC-1, AC-2, AC-8 |
| Category | Tooling |
| Status | In Progress |
| Requirements | doc/02_requirements/feature/html_ui_toolchain.md |
| Design | doc/05_design/ui/html_ui/html_ui_toolchain.md |
| Source | `test/02_integration/app/ui_edit/ui_edit_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

ui_edit CLI Integration Specification

Overview
--------
Integration tests for `bin/simple run src/app/ui_edit/main.spl` CLI.
Each `it` block runs in a fresh /tmp directory. Commands are invoked via
`rt_process_run("/bin/sh", ["-c", ...])` from the repo root.

Exit codes are unreliable in interpreter mode — assertions target stdout,
stderr, and file contents rather than exit codes.

Examples
--------
  bin/simple run src/app/ui_edit/main.spl -- new /tmp/dir/page

  bin/simple run src/app/ui_edit/main.spl -- add-css /tmp/dir/page.html /tmp/dir/extra.css

  bin/simple run src/app/ui_edit/main.spl -- add-element /tmp/dir/page.html button --id=ok

  bin/simple run src/app/ui_edit/main.spl -- set-css /tmp/dir/page.html /tmp/dir/page.css button color red

  bin/simple run src/app/ui_edit/main.spl -- list /tmp/dir/page.html

  bin/simple run src/app/ui_edit/main.spl -- add-element /tmp/dir/page.html foowidget

## Scenarios

### ui_edit CLI

#### new creates html and css files with a stylesheet link

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new creates html and css files with a stylesheet link


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("new creates html and css files with a stylesheet link")
val dir = "/tmp/ui_edit_spec_new_" + rt_env_get("$") ?? "0"
rt_process_run("/bin/sh", ["-c", "mkdir -p " + dir])
run_ui_edit(["new", dir + "/page"])
assert_true(file_exists(dir + "/page.html"))
assert_true(file_exists(dir + "/page.css"))
val html = file_read(dir + "/page.html")
assert_true(html.contains("link"))
assert_true(html.contains("page.css"))
rt_process_run("/bin/sh", ["-c", "rm -rf " + dir])
```

</details>

#### add-css injects a second link tag into the HTML

- add-css injects a second link tag into the HTML
   - Expected: count_occurrences(html, "<link") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("add-css injects a second link tag into the HTML")
val dir = "/tmp/ui_edit_spec_css_" + rt_env_get("$") ?? "1"
rt_process_run("/bin/sh", ["-c", "mkdir -p " + dir])
run_ui_edit(["new", dir + "/page"])
run_ui_edit(["add-css", dir + "/page.html", dir + "/extra.css"])
val html = file_read(dir + "/page.html")
expect(count_occurrences(html, "<link")).to_equal(2)
assert_true(html.contains("extra.css"))
rt_process_run("/bin/sh", ["-c", "rm -rf " + dir])
```

</details>

#### add-element roundtrip preserves an unrelated marker line byte-identically

- add-element roundtrip preserves an unrelated marker line byte-identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("add-element roundtrip preserves an unrelated marker line byte-identically")
val dir = "/tmp/ui_edit_spec_elem_" + rt_env_get("$") ?? "2"
rt_process_run("/bin/sh", ["-c", "mkdir -p " + dir])
run_ui_edit(["new", dir + "/page"])
# Inject a marker comment into the HTML body
val marker = "<!-- MARKER: sentinel-do-not-remove -->"
val html0 = file_read(dir + "/page.html")
val injected = html0.replace("</body>", marker + "\n</body>")
rt_process_run("/bin/sh", ["-c", "printf '%s' " + "'" + injected + "'" + " > " + dir + "/page.html"])
run_ui_edit(["add-element", dir + "/page.html", "button", "--id=ok"])
val html1 = file_read(dir + "/page.html")
assert_true(html1.contains(marker))
assert_true(html1.contains("button"))
rt_process_run("/bin/sh", ["-c", "rm -rf " + dir])
```

</details>

#### set-css updates a property and does not duplicate the rule on repeat

- set-css updates a property and does not duplicate the rule on repeat
   - Expected: count_occurrences(css, "color") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("set-css updates a property and does not duplicate the rule on repeat")
val dir = "/tmp/ui_edit_spec_setcss_" + rt_env_get("$") ?? "3"
rt_process_run("/bin/sh", ["-c", "mkdir -p " + dir])
run_ui_edit(["new", dir + "/page"])
run_ui_edit(["set-css", dir + "/page.html", dir + "/page.css", "button", "color", "red"])
run_ui_edit(["set-css", dir + "/page.html", dir + "/page.css", "button", "color", "blue"])
val css = file_read(dir + "/page.css")
expect(count_occurrences(css, "color")).to_equal(1)
assert_true(css.contains("blue"))
rt_process_run("/bin/sh", ["-c", "rm -rf " + dir])
```

</details>

#### list prints one line per element in the HTML file

- list prints one line per element in the HTML file


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("list prints one line per element in the HTML file")
val dir = "/tmp/ui_edit_spec_list_" + rt_env_get("$") ?? "4"
rt_process_run("/bin/sh", ["-c", "mkdir -p " + dir])
run_ui_edit(["new", dir + "/page"])
run_ui_edit(["add-element", dir + "/page.html", "button", "--id=ok"])
val (out, _err, _code) = run_ui_edit(["list", dir + "/page.html"])
assert_true(out.contains("button"))
assert_true(out.contains("html"))
rt_process_run("/bin/sh", ["-c", "rm -rf " + dir])
```

</details>

#### add-element with unknown tag prints an error message

- add-element with unknown tag prints an error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("add-element with unknown tag prints an error message")
val dir = "/tmp/ui_edit_spec_unk_" + rt_env_get("$") ?? "5"
rt_process_run("/bin/sh", ["-c", "mkdir -p " + dir])
run_ui_edit(["new", dir + "/page"])
val (out, err, _code) = run_ui_edit(["add-element", dir + "/page.html", "foowidget"])
val combined = out + err
assert_true(combined.contains("unknown") or combined.contains("foowidget"))
rt_process_run("/bin/sh", ["-c", "rm -rf " + dir])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/html_ui_toolchain.md`
- **Design:** `doc/05_design/ui/html_ui/html_ui_toolchain.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `514e2ad7dfae4e4af097028d9c780920c70b14fb7972319c01a25aedd4651a92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `514e2ad7dfae4e4af097028d9c780920c70b14fb7972319c01a25aedd4651a92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `514e2ad7dfae4e4af097028d9c780920c70b14fb7972319c01a25aedd4651a92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/ui_edit/ui_edit_cli_spec.spl
mirror: doc/06_spec/02_integration/app/ui_edit/ui_edit_cli_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/ui_edit/ui_edit_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/ui_edit/ui_edit_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/ui_edit/ui_edit_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/ui_edit/ui_edit_cli_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new creates html and css files with a stylesheet link' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ui_edit/ui_edit_cli_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add-css injects a second link tag into the HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ui_edit/ui_edit_cli_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add-element roundtrip preserves an unrelated marker line byte-identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
