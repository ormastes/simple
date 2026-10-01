# Browser GPU-Runnable Script Load and Animation

> Loads scripts into the browser script-render lane, executes them against the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser GPU-Runnable Script Load and Animation

Loads scripts into the browser script-render lane, executes them against the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Loads scripts into the browser script-render lane, executes them against the
rendered document, and drives animation ticks by re-rendering successive frames.
Verifies per-frame render evidence: pixel buffer size, frame-to-frame pixel
deltas for the animated element, and byte-identical output for static content.

## Scenarios

### Browser script load into render lane

#### script collection for the render session

#### collects an inline script body with empty type

- collects an inline script body with empty type
   - Expected: result.scripts.len() equals `1`
   - Expected: result.scripts[0] equals `let x = 1`
   - Expected: result.script_types[0] equals ``
   - Expected: result.src_paths.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects an inline script body with empty type")
val html = "<html><head></head><body><script>let x = 1</script></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(1)
expect(result.scripts[0]).to_equal("let x = 1")
expect(result.script_types[0]).to_equal("")
expect(result.src_paths.len()).to_equal(0)
```

</details>

#### collects script type metadata from single-quoted attributes

- collects script type metadata from single-quoted attributes
   - Expected: result.scripts.len() equals `1`
   - Expected: result.script_types[0] equals `text/javascript`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects script type metadata from single-quoted attributes")
val html = "<html><body><script type='text/javascript'>let x = 1</script></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(1)
expect(result.script_types[0]).to_equal("text/javascript")
```

</details>

#### collects external src path and type from double-quoted attributes

- collects external src path and type from double-quoted attributes
   - Expected: result.scripts.len() equals `0`
   - Expected: result.src_paths.len() equals `1`
   - Expected: result.src_paths[0] equals `app.js`
   - Expected: result.src_types[0] equals `module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects external src path and type from double-quoted attributes")
val html = "<html><head><script src=\"app.js\" type=\"module\"></script></head><body></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(0)
expect(result.src_paths.len()).to_equal(1)
expect(result.src_paths[0]).to_equal("app.js")
expect(result.src_types[0]).to_equal("module")
```

</details>

#### collects multiple script bodies in document order

- collects multiple script bodies in document order
   - Expected: result.scripts.len() equals `2`
   - Expected: result.scripts[0] equals `let a = 1`
   - Expected: result.scripts[1] equals `let b = 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects multiple script bodies in document order")
val html = "<html><head><script>let a = 1</script></head><body><script>let b = 2</script></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(2)
expect(result.scripts[0]).to_equal("let a = 1")
expect(result.scripts[1]).to_equal("let b = 2")
```

</details>

#### returns empty collection for script-free HTML

- returns empty collection for script-free HTML
   - Expected: result.scripts.len() equals `0`
   - Expected: result.src_paths.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty collection for script-free HTML")
val html = "<html><head></head><body><div>hello</div></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(0)
expect(result.src_paths.len()).to_equal(0)
```

</details>

#### stops safely on an unterminated script tag

- stops safely on an unterminated script tag
   - Expected: result.scripts.len() equals `0`
   - Expected: result.src_paths.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops safely on an unterminated script tag")
val html = "<html><body><script>let a = 1"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(0)
expect(result.src_paths.len()).to_equal(0)
```

</details>

#### constructs empty parse and render results with allocated evidence buffer

- constructs empty parse and render results with allocated evidence buffer
   - Expected: parse.scripts.len() equals `0`
   - Expected: parse.src_types.len() equals `0`
   - Expected: render.pixels.len() equals `WIDTH * HEIGHT * 4`
   - Expected: render.ok is true
   - Expected: render.scripts_collected equals `0`
   - Expected: render.console_output.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs empty parse and render results with allocated evidence buffer")
val parse = BeScriptParseResult.empty()
expect(parse.scripts.len()).to_equal(0)
expect(parse.src_types.len()).to_equal(0)
val render = BeScriptRenderResult.empty(WIDTH, HEIGHT)
expect(render.pixels.len()).to_equal(WIDTH * HEIGHT * 4)
expect(render.ok).to_equal(true)
expect(render.scripts_collected).to_equal(0)
expect(render.console_output.len()).to_equal(0)
```

</details>

#### hardened script execution

#### executes a double-quoted console.log literal

- executes a double-quoted console.log literal
   - Expected: result.scripts_collected equals `1`
   - Expected: result.scripts_executed equals `1`
   - Expected: result.scripts_denied equals `0`
   - Expected: result.console_output.len() equals `1`
   - Expected: result.console_output[0] equals `hello gpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes a double-quoted console.log literal")
val html = "<html><body><script>console.log(\"hello gpu\")</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_collected).to_equal(1)
expect(result.scripts_executed).to_equal(1)
expect(result.scripts_denied).to_equal(0)
expect(result.console_output.len()).to_equal(1)
expect(result.console_output[0]).to_equal("hello gpu")
```

</details>

#### executes a single-quoted print literal

- executes a single-quoted print literal
   - Expected: result.scripts_executed equals `1`
   - Expected: result.console_output[0] equals `tick`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes a single-quoted print literal")
val html = "<html><body><script>print('tick')</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_executed).to_equal(1)
expect(result.console_output[0]).to_equal("tick")
```

</details>

#### resolves assigned variables through print and console.log

- resolves assigned variables through print and console.log
   - Expected: result.scripts_executed equals `1`
   - Expected: result.console_output.len() equals `2`
   - Expected: result.console_output[0] equals `animated`
   - Expected: result.console_output[1] equals `animated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves assigned variables through print and console.log")
val html = "<html><body><script>const msg = \"animated\"; print(msg); console.log(msg);</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_executed).to_equal(1)
expect(result.console_output.len()).to_equal(2)
expect(result.console_output[0]).to_equal("animated")
expect(result.console_output[1]).to_equal("animated")
```

</details>

#### splits semicolon-joined statements and keeps output order

- splits semicolon-joined statements and keeps output order
   - Expected: result.console_output.len() equals `3`
   - Expected: result.console_output[0] equals `one`
   - Expected: result.console_output[1] equals `two`
   - Expected: result.console_output[2] equals `three`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits semicolon-joined statements and keeps output order")
val html = "<html><body><script>console.log(\"one\");console.log(\"two\");print(\"three\")</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.console_output.len()).to_equal(3)
expect(result.console_output[0]).to_equal("one")
expect(result.console_output[1]).to_equal("two")
expect(result.console_output[2]).to_equal("three")
```

</details>

#### normalizes carriage returns between statements

- normalizes carriage returns between statements
   - Expected: result.console_output.len() equals `2`
   - Expected: result.console_output[0] equals `cr1`
   - Expected: result.console_output[1] equals `cr2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes carriage returns between statements")
val html = "<html><body><script>console.log(\"cr1\")\rconsole.log(\"cr2\")</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.console_output.len()).to_equal(2)
expect(result.console_output[0]).to_equal("cr1")
expect(result.console_output[1]).to_equal("cr2")
```

</details>

#### skips unknown statements and non-literal assignments without denying

- skips unknown statements and non-literal assignments without denying
   - Expected: result.scripts_executed equals `1`
   - Expected: result.scripts_denied equals `0`
   - Expected: result.console_output.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips unknown statements and non-literal assignments without denying")
val html = "<html><body><script>let n = 41; n++; print(n); doSomething()</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_executed).to_equal(1)
expect(result.scripts_denied).to_equal(0)
# non-literal rhs stores empty value, print(n) emits nothing
expect(result.console_output.len()).to_equal(0)
```

</details>

#### denies external src scripts with a diagnostic

- denies external src scripts with a diagnostic
   - Expected: result.scripts_collected equals `1`
   - Expected: result.scripts_denied equals `1`
   - Expected: result.scripts_executed equals `0`
   - Expected: result.diagnostics[0] equals `external script src denied: cdn/app.js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies external src scripts with a diagnostic")
val html = "<html><head><script src='cdn/app.js'></script></head><body></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_collected).to_equal(1)
expect(result.scripts_denied).to_equal(1)
expect(result.scripts_executed).to_equal(0)
expect(result.diagnostics[0]).to_equal("external script src denied: cdn/app.js")
```

</details>

#### denies unsupported script types with a diagnostic

- denies unsupported script types with a diagnostic
   - Expected: result.scripts_denied equals `1`
   - Expected: result.diagnostics[0] equals `unsupported script type denied: text/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies unsupported script types with a diagnostic")
val html = "<html><body><script type='text/simple'>let x = 1</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_denied).to_equal(1)
expect(result.diagnostics[0]).to_equal("unsupported script type denied: text/simple")
```

</details>

#### executes all accepted browser JS type spellings

- executes all accepted browser JS type spellings
   - Expected: result.scripts_collected equals `3`
   - Expected: result.scripts_executed equals `3`
   - Expected: result.console_output.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes all accepted browser JS type spellings")
val html = "<html><body>" +
    "<script type='text/javascript'>console.log(\"a\")</script>" +
    "<script type='application/javascript'>console.log(\"b\")</script>" +
    "<script type='MODULE'>console.log(\"c\")</script>" +
    "</body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_collected).to_equal(3)
expect(result.scripts_executed).to_equal(3)
expect(result.console_output.len()).to_equal(3)
```

</details>

#### denies every host-escape family with the exact diagnostic

- denies every host-escape family with the exact diagnostic
   - Expected: result.scripts_collected equals `6`
   - Expected: result.scripts_denied equals `6`
   - Expected: result.scripts_executed equals `0`
   - Expected: result.diagnostics.len() equals `6`
   - Expected: result.diagnostics[0] equals `host shell access denied`
   - Expected: result.diagnostics[1] equals `child process access denied`
   - Expected: result.diagnostics[2] equals `module loader access denied`
   - Expected: result.diagnostics[3] equals `ambient environment access denied`
   - Expected: result.diagnostics[4] equals `filesystem access denied`
   - Expected: result.diagnostics[5] equals `network access denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies every host-escape family with the exact diagnostic")
val html = "<html><body>" +
    "<script>host.shell(\"ls\")</script>" +
    "<script>spawn(\"sh\")</script>" +
    "<script>require(\"fs\")</script>" +
    "<script>let e = process.env</script>" +
    "<script>fs.readFile(\"/etc/passwd\")</script>" +
    "<script>fetch(\"http://x\")</script>" +
    "</body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_collected).to_equal(6)
expect(result.scripts_denied).to_equal(6)
expect(result.scripts_executed).to_equal(0)
expect(result.diagnostics.len()).to_equal(6)
expect(result.diagnostics[0]).to_equal("host shell access denied")
expect(result.diagnostics[1]).to_equal("child process access denied")
expect(result.diagnostics[2]).to_equal("module loader access denied")
expect(result.diagnostics[3]).to_equal("ambient environment access denied")
expect(result.diagnostics[4]).to_equal("filesystem access denied")
expect(result.diagnostics[5]).to_equal("network access denied")
```

</details>

### Browser script render animation frames

#### render evidence per frame

#### merges render metadata and script execution into one frame result

- merges render metadata and script execution into one frame result
   - Expected: result.ok is true
   - Expected: result.width equals `WIDTH`
   - Expected: result.height equals `HEIGHT`
   - Expected: result.scripts_collected equals `1`
   - Expected: result.scripts_executed equals `1`
   - Expected: result.scripts_denied equals `0`
   - Expected: result.console_output[0] equals `frame 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges render metadata and script execution into one frame result")
val html = _frame_html(0)
val result = render_html_to_pixels_with_scripts(html, WIDTH, HEIGHT)
expect(result.ok).to_equal(true)
expect(result.width).to_equal(WIDTH)
expect(result.height).to_equal(HEIGHT)
expect(result.scripts_collected).to_equal(1)
expect(result.scripts_executed).to_equal(1)
expect(result.scripts_denied).to_equal(0)
expect(result.console_output[0]).to_equal("frame 0")
```

</details>

#### advances animation ticks with monotonically growing painted area

- advances animation ticks with monotonically growing painted area
   - Expected: frame.ok is true
   - Expected: frame.scripts_executed equals `1`
   - Expected: frame.console_output[0] equals `"frame " + tick.to_text()`
   - Expected: pixels.len() equals `WIDTH * HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("advances animation ticks with monotonically growing painted area")
var previous_area: i64 = 0
var tick: i64 = 0
while tick < 4:
    val html = _frame_html(tick)
    val frame = render_html_to_pixels_with_scripts(html, WIDTH, HEIGHT)
    expect(frame.ok).to_equal(true)
    expect(frame.scripts_executed).to_equal(1)
    expect(frame.console_output[0]).to_equal("frame " + tick.to_text())
    val pixels = _frame_pixels(html)
    expect(pixels.len()).to_equal(WIDTH * HEIGHT)
    val area = _painted_area(pixels)
    expect(area).to_be_greater_than(previous_area)
    previous_area = area
    tick = tick + 1
```

</details>

#### produces different pixel evidence between consecutive animation frames

- produces different pixel evidence between consecutive animation frames
   - Expected: _pixels_equal(frame0, frame1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces different pixel evidence between consecutive animation frames")
val frame0 = _frame_pixels(_frame_html(0))
val frame1 = _frame_pixels(_frame_html(1))
expect(_pixels_equal(frame0, frame1)).to_equal(false)
```

</details>

#### keeps static content pixel-identical while script output changes

- keeps static content pixel-identical while script output changes
   - Expected: _pixels_equal(_frame_pixels(html_a), _frame_pixels(html_b)) is true
   - Expected: frame_a.console_output[0] equals `tick a`
   - Expected: frame_b.console_output[0] equals `tick b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps static content pixel-identical while script output changes")
val base = "<html><body style='margin:0; background:#ffffff'>" +
    "<div style='width:8px; height:8px; background-color:#ff0000'></div>"
val html_a = base + "<script>console.log(\"tick a\")</script></body></html>"
val html_b = base + "<script>console.log(\"tick b\")</script></body></html>"
expect(_pixels_equal(_frame_pixels(html_a), _frame_pixels(html_b))).to_equal(true)
val frame_a = render_html_to_pixels_with_scripts(html_a, WIDTH, HEIGHT)
val frame_b = render_html_to_pixels_with_scripts(html_b, WIDTH, HEIGHT)
expect(frame_a.console_output[0]).to_equal("tick a")
expect(frame_b.console_output[0]).to_equal("tick b")
```

</details>

#### is deterministic for repeated renders of the same frame

- is deterministic for repeated renders of the same frame
   - Expected: _pixels_equal(_frame_pixels(html), _frame_pixels(html)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic for repeated renders of the same frame")
val html = _frame_html(2)
expect(_pixels_equal(_frame_pixels(html), _frame_pixels(html))).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dbd44155c6e7b7f395705cd42e906d08fc1ba57ae5176a1a04eea8101612a530`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbd44155c6e7b7f395705cd42e906d08fc1ba57ae5176a1a04eea8101612a530`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbd44155c6e7b7f395705cd42e906d08fc1ba57ae5176a1a04eea8101612a530`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 41 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects an inline script body with empty type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects script type metadata from single-quoted attributes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_script_animation_gpu_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects external src path and type from double-quoted attributes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
