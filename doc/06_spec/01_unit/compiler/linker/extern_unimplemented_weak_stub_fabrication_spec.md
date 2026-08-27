# Unimplemented `extern fn` must fail the build, never fabricate a value

> For anyone declaring an `extern fn`. An `extern fn` is a promise that a symbol

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unimplemented `extern fn` must fail the build, never fabricate a value

For anyone declaring an `extern fn`. An `extern fn` is a promise that a symbol

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Implemented (both the `extern fn` keyword form and the `@extern` |
| Source | `test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

For anyone declaring an `extern fn`. An `extern fn` is a promise that a symbol
exists somewhere outside Simple source. When that promise is false the only
honest outcome is a build failure that names the symbol. Silently linking a
weak stub turns a missing implementation into a plausible-looking wrong answer
that no test, log, or exit code can distinguish from a correct one.

## Scope and Preconditions

Hosted x86_64 Linux, in-process native lane only. The spec drives
`bin/simple native-build` under `SIMPLE_NATIVE_BUILD_RUST=1` deliberately: the
DEFAULT (pure-Simple) native-build lane OOMs on this host — its worker has been
observed killed between 11 GB and 36 GB RSS — so a spec that shelled out to a
plain `native-build` would TIME OUT rather than produce a clean verdict, and a
timeout is not evidence about extern resolution. The in-process Rust lane
completes in ~8s per fixture and is the lane on which the defect was
reproduced.

## Primary Workflow

Two fixtures, both built the same way:

- `test/fixtures/extern_unimplemented_weak_stub/negative/main.spl` declares
  `lane_definitely_absent_probe`, which is defined nowhere in the tree. The
  build MUST fail, MUST name the symbol, MUST NOT emit a binary, and MUST NOT
  yield a program that prints `got 3`.
- `test/fixtures/extern_unimplemented_weak_stub/positive/main.spl` declares
  `rt_string_len`, a real exported runtime symbol. It MUST build and print
  `got 4`.
- `at_negative/` and `at_positive/` are the same pair written with the
  `@extern` ATTRIBUTE spelling instead of the `extern fn` keyword. They are
  separate fixtures because the two spellings took different code paths: the
  attribute form was parsed as a bodyless ordinary function, never reached
  `Linkage::Import`, and was emitted as a strong `ud2` definition, so BOTH its
  cases -- missing symbol AND real runtime symbol -- produced a green build
  whose binary SIGILLed. This positive control is what stops the negative assertions from
  passing vacuously: a compiler that rejected every `extern fn` would satisfy
  the negative case alone, and this spec would still be wrong to go green.

## Observed defect (reproduced 2026-08-18, in-process lane)

The negative fixture builds with exit 0. The build log even prints
`Unresolved symbol preview: __cpu_indicator_init, __cpu_model,
lane_definitely_absent_probe` and then links anyway. `nm` on the product shows
`0000000000402eac W lane_definitely_absent_probe` — a WEAK stub — and running
it prints `got 3` and exits 0. There is no signal at compile, link, or run
time.

## Recovery and Troubleshooting

If this spec is RED, an unimplemented extern still fabricates values; do not
trust any `extern fn` result until it is GREEN. If only the POSITIVE case is
red, the fix over-corrected and now rejects legitimate externs.

## Compatibility and Limitations

Linux/hosted only; the weak-stub emission is a hosted-link behaviour. Baremetal
and cross-target lanes are out of scope here.

## Scenarios

### extern fn with no implementation

#### fails the build instead of linking a fabricating weak stub

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails the build instead of linking a fabricating weak stub
- build the negative fixture on the in-process native lane
- the build must not succeed
   - Expected: out does not contain `BUILD_RC=0`
- the diagnostic must name the missing symbol
   - Expected: out contains `lane_definitely_absent_probe`
- no binary may be produced
   - Expected: out contains `BINARY=no`
- and therefore no fabricated value may ever be printed
   - Expected: out does not contain `RUN_OUT=got 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails the build instead of linking a fabricating weak stub")
step("build the negative fixture on the in-process native lane")
val out = build_and_run("test/fixtures/extern_unimplemented_weak_stub/negative")

step("the build must not succeed")
expect(out.contains("BUILD_RC=0")).to_equal(false)

step("the diagnostic must name the missing symbol")
expect(out.contains("lane_definitely_absent_probe")).to_equal(true)

step("no binary may be produced")
expect(out.contains("BINARY=no")).to_equal(true)

step("and therefore no fabricated value may ever be printed")
expect(out.contains("RUN_OUT=got 3")).to_equal(false)
```

</details>

#### still builds and returns the real value when the extern is implemented

- still builds and returns the real value when the extern is implemented
- build the positive fixture, whose extern is a real runtime symbol
- the build must succeed and emit a binary
   - Expected: out contains `BUILD_RC=0`
   - Expected: out contains `BINARY=yes`
- and the program must return the runtime's real answer, not a stub
   - Expected: out contains `RUN_RC=0`
   - Expected: out contains `RUN_OUT=got 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still builds and returns the real value when the extern is implemented")
step("build the positive fixture, whose extern is a real runtime symbol")
val out = build_and_run("test/fixtures/extern_unimplemented_weak_stub/positive")

step("the build must succeed and emit a binary")
expect(out.contains("BUILD_RC=0")).to_equal(true)
expect(out.contains("BINARY=yes")).to_equal(true)

step("and the program must return the runtime's real answer, not a stub")
expect(out.contains("RUN_RC=0")).to_equal(true)
expect(out.contains("RUN_OUT=got 4")).to_equal(true)
```

</details>

### @extern fn with no implementation

#### fails the build instead of emitting a strong ud2 definition

- fails the build instead of emitting a strong ud2 definition
- build the @extern-form negative fixture on the in-process native lane
- the build must not succeed
   - Expected: out does not contain `BUILD_RC=0`
- the diagnostic must name the missing symbol
   - Expected: out contains `lane_definitely_absent_at_probe`
- no binary may be produced
   - Expected: out contains `BINARY=no`
- and therefore nothing can be left to SIGILL at runtime
   - Expected: out does not contain `RUN_RC=132`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails the build instead of emitting a strong ud2 definition")
step("build the @extern-form negative fixture on the in-process native lane")
val out = build_and_run("test/fixtures/extern_unimplemented_weak_stub/at_negative")

step("the build must not succeed")
expect(out.contains("BUILD_RC=0")).to_equal(false)

step("the diagnostic must name the missing symbol")
expect(out.contains("lane_definitely_absent_at_probe")).to_equal(true)

step("no binary may be produced")
expect(out.contains("BINARY=no")).to_equal(true)

step("and therefore nothing can be left to SIGILL at runtime")
expect(out.contains("RUN_RC=132")).to_equal(false)
```

</details>

#### still builds and returns the real value when the @extern is implemented

- still builds and returns the real value when the @extern is implemented
- build the @extern-form positive fixture against a real runtime symbol
- the build must succeed and emit a binary
   - Expected: out contains `BUILD_RC=0`
   - Expected: out contains `BINARY=yes`
- the program must run to completion, not trap on a fabricated definition
   - Expected: out does not contain `RUN_RC=132`
   - Expected: out contains `RUN_RC=0`
- and it must return the runtime's real answer
   - Expected: out contains `RUN_OUT=got 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still builds and returns the real value when the @extern is implemented")
step("build the @extern-form positive fixture against a real runtime symbol")
val out = build_and_run("test/fixtures/extern_unimplemented_weak_stub/at_positive")

step("the build must succeed and emit a binary")
expect(out.contains("BUILD_RC=0")).to_equal(true)
expect(out.contains("BINARY=yes")).to_equal(true)

step("the program must run to completion, not trap on a fabricated definition")
expect(out.contains("RUN_RC=132")).to_equal(false)
expect(out.contains("RUN_RC=0")).to_equal(true)

step("and it must return the runtime's real answer")
expect(out.contains("RUN_OUT=got 4")).to_equal(true)
```

</details>

### linker output is parsed back to the missing symbols

#### names the symbol an lld undefined-symbol error reports

- names the symbol an lld undefined-symbol error reports
- feed real lld stderr, including its >>> referenced-by continuation lines
   - Expected: names.len() equals `1`
   - Expected: names[0] equals `lane_definitely_absent_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the symbol an lld undefined-symbol error reports")
step("feed real lld stderr, including its >>> referenced-by continuation lines")
val names = driver_native_link_undefined_symbols(
    "ld.lld: error: undefined symbol: lane_definitely_absent_probe\n" +
    ">>> referenced by main.spl\n" +
    ">>>               object.o:(main)\n")
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("lane_definitely_absent_probe")
```

</details>

#### names the symbol a GNU ld undefined-reference error reports

- names the symbol a GNU ld undefined-reference error reports
- GNU ld quotes the symbol in backticks and a trailing quote
   - Expected: names.len() equals `1`
   - Expected: names[0] equals `lane_definitely_absent_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the symbol a GNU ld undefined-reference error reports")
step("GNU ld quotes the symbol in backticks and a trailing quote")
val names = driver_native_link_undefined_symbols(
    "/usr/bin/ld: object.o: in function `main':\n" +
    "main.spl:(.text+0x5): undefined reference to `lane_definitely_absent_probe'\n")
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("lane_definitely_absent_probe")
```

</details>

#### reports each missing symbol once no matter how many call sites reference it

- reports each missing symbol once no matter how many call sites reference it
- the same symbol repeated, plus a second distinct one
   - Expected: names.len() equals `2`
   - Expected: names[0] equals `alpha_probe`
   - Expected: names[1] equals `beta_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports each missing symbol once no matter how many call sites reference it")
step("the same symbol repeated, plus a second distinct one")
val names = driver_native_link_undefined_symbols(
    "ld.lld: error: undefined symbol: alpha_probe\n" +
    "ld.lld: error: undefined symbol: alpha_probe\n" +
    "/usr/bin/ld: main.o:(.text+0x9): undefined reference to `beta_probe'\n")
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("alpha_probe")
expect(names[1]).to_equal("beta_probe")
```

</details>

#### extracts nothing from link failures that are not undefined symbols

- extracts nothing from link failures that are not undefined symbols
- a missing library is a different failure and must pass through untouched
- so is a relocation error, an empty log, and prose that merely discusses the phrase
   - Expected: driver_native_link_undefined_symbols("").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts nothing from link failures that are not undefined symbols")
step("a missing library is a different failure and must pass through untouched")
expect(driver_native_link_undefined_symbols(
    "/usr/bin/ld: cannot find -lfoo: No such file or directory\n" +
    "clang: error: linker command failed with exit code 1\n").len()).to_equal(0)

step("so is a relocation error, an empty log, and prose that merely discusses the phrase")
expect(driver_native_link_undefined_symbols(
    "ld.lld: error: relocation R_X86_64_32S out of range\n").len()).to_equal(0)
expect(driver_native_link_undefined_symbols("").len()).to_equal(0)
```

</details>

### a missing symbol is mapped back to its extern fn declaration

#### matches the declaration whose name is exactly the missing symbol

- matches the declaration whose name is exactly the missing symbol
- the matcher sees the declaration line with `extern fn ` already removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches the declaration whose name is exactly the missing symbol")
step("the matcher sees the declaration line with `extern fn ` already removed")
expect(driver_native_extern_decl_matches("abs(x: i64) -> i64", "abs")).to_be(true)
expect(driver_native_extern_decl_matches("abs", "abs")).to_be(true)
expect(driver_native_extern_decl_matches("abs <T>(x: T)", "abs")).to_be(true)
expect(driver_native_extern_decl_matches("abs<T>(x: T)", "abs")).to_be(true)
expect(driver_native_extern_decl_matches("abs: i64", "abs")).to_be(true)
```

</details>

#### does not blame a longer declaration that merely starts with the same letters

- does not blame a longer declaration that merely starts with the same letters
- this is what stops `abs` reporting the site of `abs_long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not blame a longer declaration that merely starts with the same letters")
step("this is what stops `abs` reporting the site of `abs_long`")
expect(driver_native_extern_decl_matches("abs_long(x: i64)", "abs")).to_be(false)
expect(driver_native_extern_decl_matches("absolute()", "abs")).to_be(false)
expect(driver_native_extern_decl_matches("other(x: i64)", "abs")).to_be(false)
expect(driver_native_extern_decl_matches("", "abs")).to_be(false)
```

</details>

### the assembled link-failure diagnostic

#### names the symbol, its declaration file:line, and keeps the raw linker text

- names the symbol, its declaration file:line, and keeps the raw linker text
- read the real negative fixture and find its declaration line
- run the whole pipeline on real lld stderr against that source
- the missing symbol is named
- the extern declaration file:line appears, and it is the real line
- the line survives stderr truncation because it starts with `error:`
- and the raw linker output is preserved verbatim, not swallowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the symbol, its declaration file:line, and keeps the raw linker text")
step("read the real negative fixture and find its declaration line")
val source = rt_file_read_text(NEGATIVE_FIXTURE_PATH) ?? ""
expect(source.contains("extern fn lane_definitely_absent_probe")).to_be(true)
var decl_line = 0
var n = 0
for line in source.split("\n"):
    n = n + 1
    if line.trim().starts_with("extern fn lane_definitely_absent_probe"):
        decl_line = n
expect(decl_line > 0).to_be(true)

step("run the whole pipeline on real lld stderr against that source")
val raw = "Linking failed: cc linking failed:\n" +
    "ld.lld: error: undefined symbol: lane_definitely_absent_probe\n" +
    ">>> referenced by main.spl\n"
val msg = assembled_message(source, NEGATIVE_FIXTURE_PATH, raw)

step("the missing symbol is named")
expect(msg.contains("lane_definitely_absent_probe")).to_be(true)

step("the extern declaration file:line appears, and it is the real line")
expect(msg.contains(NEGATIVE_FIXTURE_PATH + ":" + decl_line.to_string())).to_be(true)

step("the line survives stderr truncation because it starts with `error:`")
expect(msg.contains(
    "  error: extern fn lane_definitely_absent_probe is declared but not " +
    "implemented anywhere -- declared at " +
    NEGATIVE_FIXTURE_PATH + ":" + decl_line.to_string())).to_be(true)

step("and the raw linker output is preserved verbatim, not swallowed")
expect(msg.contains("raw linker output follows")).to_be(true)
expect(msg.contains(raw)).to_be(true)
expect(msg.ends_with(raw)).to_be(true)
```

</details>

#### passes an unrelated link failure through unrewritten

- passes an unrelated link failure through unrewritten
- a missing library names no undefined symbol at all
   - Expected: msg equals `"LLVM native linking failed: " + raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes an unrelated link failure through unrewritten")
step("a missing library names no undefined symbol at all")
val raw = "/usr/bin/ld: cannot find -lfoo: No such file or directory\n" +
    "clang: error: linker command failed with exit code 1\n"
val msg = assembled_message(rt_file_read_text(NEGATIVE_FIXTURE_PATH) ?? "",
    NEGATIVE_FIXTURE_PATH, raw)
expect(msg.contains("unimplemented extern function(s)")).to_be(false)
expect(msg.contains("declared but not implemented")).to_be(false)
expect(msg).to_equal("LLVM native linking failed: " + raw)
```

</details>

#### does not claim a declaration site for an undefined symbol that is not an extern

- does not claim a declaration site for an undefined symbol that is not an extern
- an undefined internal symbol maps to no `extern fn` in the source
   - Expected: msg equals `"LLVM native linking failed: " + raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not claim a declaration site for an undefined symbol that is not an extern")
step("an undefined internal symbol maps to no `extern fn` in the source")
val raw = "ld.lld: error: undefined symbol: __some_internal_helper\n"
val msg = assembled_message(rt_file_read_text(NEGATIVE_FIXTURE_PATH) ?? "",
    NEGATIVE_FIXTURE_PATH, raw)
expect(msg).to_equal("LLVM native linking failed: " + raw)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LINKER-EXTERN-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5f0139bfc7cb8880eb0dfff20ca4e3b271753af430f46f2304be58f7c7f17b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5f0139bfc7cb8880eb0dfff20ca4e3b271753af430f46f2304be58f7c7f17b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5f0139bfc7cb8880eb0dfff20ca4e3b271753af430f46f2304be58f7c7f17b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails the build instead of linking a fabricating weak stub' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still builds and returns the real value when the extern is implemented' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails the build instead of emitting a strong ud2 definition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
