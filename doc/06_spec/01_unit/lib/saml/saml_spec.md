# Saml Specification

> Tests covering SAML parser — module shell, SAML parser — class fields, SAML parser — enums and attributes, SAML parser — llm fn, SAML parser — comment-embedded cases, SAML parser — test blocks, SAML analysis — prompt variables, SAML analysis — reachable types, SAML analysis — evidence ranking, SAML analysis — external spec coverage, SAML analysis — static warnings, SAML emit — BAML projection, SAML emit — reports and manual.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Saml Specification

## Scenarios

### SAML parser — module shell

#### records the module name and source path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records the module name and source path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records the module name and source path")
val m = fixture_module()
check_msg(m.name == "resume", "module name should be resume")
check(m.source_path == FIXTURE_PATH)
```

</details>

#### collects every top-level declaration kind

- collects every top-level declaration kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects every top-level declaration kind")
val m = fixture_module()
check_msg(m.classes.len() == 2, "expected Education and Resume")
check_msg(m.enums.len() == 1, "expected Seniority")
check_msg(m.structs.len() == 1, "expected ExtractionStats")
check_msg(m.functions.len() == 2, "expected ExtractResume and ScoreResume")
check_msg(m.tests.len() == 1, "expected resume_extraction")
```

</details>

### SAML parser — class fields

#### parses plain, optional, and list field types

- parses plain, optional, and list field types


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses plain, optional, and list field types")
val resume = find_class(fixture_module(), "Resume")
check(resume != nil)
val name = field_named(resume, "name")
check(name.type_name == "text")
check(name.optional == false)
check(name.is_list == false)
val email = field_named(resume, "email")
check_msg(email.optional, "email: text? should be optional")
check(email.is_list == false)
val skills = field_named(resume, "skills")
check_msg(skills.is_list, "skills: [text] should be a list")
check(skills.type_name == "text")
check(skills.optional == false)
```

</details>

#### renders the source spelling back with type_display

- renders the source spelling back with type_display


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders the source spelling back with type_display")
val resume = find_class(fixture_module(), "Resume")
check(type_display("text", true, false) == "text?")
check(type_display("text", false, true) == "[text]")
val skills = field_named(resume, "skills")
check(type_display(skills.type_name, skills.optional, skills.is_list) == "[text]")
```

</details>

#### captures @alias, @description, and @sensitive on fields

- captures @alias, @description, and @sensitive on fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures @alias, @description, and @sensitive on fields")
val resume = find_class(fixture_module(), "Resume")
val name = field_named(resume, "name")
check_msg(name.alias == "candidate_name", "expected @alias body")
check_msg(name.description == "Full legal name as written", "expected @description body")
check(name.sensitive == "")
val email = field_named(resume, "email")
check_msg(email.sensitive == "pii", "expected @sensitive(pii)")
```

</details>

#### keeps a struct separate from a class

- keeps a struct separate from a class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a struct separate from a class")
val m = fixture_module()
check(find_struct(m, "ExtractionStats") != nil)
check(find_class(m, "ExtractionStats") == nil)
```

</details>

### SAML parser — enums and attributes

#### parses enum values and their @alias

- parses enum values and their @alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses enum values and their @alias")
val e = find_enum(fixture_module(), "Seniority")
check(e != nil)
check_msg(e.values.len() == 3, "expected three seniority values")
check(e.values[0].name == "junior")
check(e.values[0].alias == "")
check(e.values[1].name == "staff")
check_msg(e.values[1].alias == "staff_engineer", "expected @alias on staff")
```

</details>

#### splits a trailing attribute run off a declaration head

- splits a trailing attribute run off a declaration head


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits a trailing attribute run off a declaration head")
val parts = split_attributes("name: text @alias(\"a\") @description(\"b, c\")")
check(parts.len() == 3)
check(parts[0] == "name: text")
check(parts[1] == "alias(\"a\")")
check_msg(parts[2] == "description(\"b, c\")", "a comma inside parens must not split")
```

</details>

#### records function attributes and reads their bodies

- records function attributes and reads their bodies


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records function attributes and reads their bodies")
val f = find_function(fixture_module(), "ExtractResume")
check(f != nil)
check_msg(has_attribute(f.attributes, "trace"), "bare @trace should be present")
check_msg(has_attribute(f.attributes, "parse"), "@parse(...) should match by head name")
check(has_attribute(f.attributes, "redact"))
check(has_attribute(f.attributes, "eval_required") == false)
check(attribute_body(f.attributes, "parse") == "strictness: strict")
```

</details>

### SAML parser — llm fn

#### parses params, return type, and client

- parses params, return type, and client


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses params, return type, and client")
val m = fixture_module()
val f = find_function(m, "ExtractResume")
check(f.params.len() == 1)
check(f.params[0].name == "resume_text")
check(f.params[0].type_name == "text")
check_msg(f.return_type == "Resume", "return type should be Resume")
check_msg(f.client == "FastExtract", "client policy should be captured")
val g = find_function(m, "ScoreResume")
check(g.params.len() == 2)
check(g.params[1].name == "rubric")
check(g.return_type == "Seniority")
check(g.client == "CarefulJudge")
```

</details>

#### captures the triple-quoted prompt body

- captures the triple-quoted prompt body


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures the triple-quoted prompt body")
val f = find_function(fixture_module(), "ExtractResume")
check_msg(f.prompt != "", "prompt body must not be empty")
check(f.prompt.contains("Extract the resume below"))
check_msg(f.prompt.contains("saml.output_format"), "prompt must carry the output_format reference")
check_msg(f.prompt.contains("resume_text"), "prompt must carry the param reference")
```

</details>

#### captures the leading doc comment

- captures the leading doc comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures the leading doc comment")
val f = find_function(fixture_module(), "ExtractResume")
check(f.doc.contains("Extract a structured resume"))
```

</details>

#### diagnoses an llm fn with no return arrow as E-SAML-1200

- diagnoses an llm fn with no return arrow as E-SAML-1200


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagnoses an llm fn with no return arrow as E-SAML-1200")
val m = parse_saml("module broken\nllm fn Broken(x: text):\n", "inline")
var found = false
for d in m.diagnostics:
    if d.code == "E-SAML-1200" and d.severity == "error":
        found = true
check_msg(found, "a missing `->` must raise E-SAML-1200 error")
```

</details>

#### leaves a well-formed fixture free of error diagnostics

- leaves a well-formed fixture free of error diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a well-formed fixture free of error diagnostics")
for d in fixture_module().diagnostics:
    check_msg(d.severity != "error", "fixture produced: " + d.code + " " + d.message)
```

</details>

### SAML parser — comment-embedded cases

#### parses an example comment into input and expectation

- parses an example comment into input and expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses an example comment into input and expectation")
val ex = parse_example_comment(" example: ExtractResume(\"x\") => name == \"y\"", 7)
check(ex != nil)
check(ex.kind == "example")
check(ex.input_text == "ExtractResume(\"x\")")
check(ex.expect_text == "name == \"y\"")
check(ex.line == 7)
```

</details>

#### parses a counter-example comment with its distinct kind

- parses a counter-example comment with its distinct kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a counter-example comment with its distinct kind")
val ex = parse_example_comment(" counter-example: ExtractResume(\"\") => error", 9)
check_msg(ex.kind == "counter_example", "counter-example must not be filed as example")
check(ex.expect_text == "error")
```

</details>

#### returns nil for an ordinary comment

- returns nil for an ordinary comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for an ordinary comment")
check(parse_example_comment(" just prose", 1) == nil)
```

</details>

#### attaches both cases to the declaration that follows

- attaches both cases to the declaration that follows


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attaches both cases to the declaration that follows")
val f = find_function(fixture_module(), "ExtractResume")
check_msg(f.example_cases.len() == 2, "expected one example and one counter-example")
var positives = 0
var negatives = 0
for ex in f.example_cases:
    if ex.kind == "counter_example":
        negatives = negatives + 1
    else:
        positives = positives + 1
check(positives == 1)
check(negatives == 1)
val g = find_function(fixture_module(), "ScoreResume")
check_msg(g.example_cases.len() == 0, "cases must not leak onto the next function")
```

</details>

### SAML parser — test blocks

#### parses functions, asserts, and the evidence source

- parses functions, asserts, and the evidence source


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses functions, asserts, and the evidence source")
val t = fixture_module().tests[0]
check(t.name == "resume_extraction")
check(t.functions.len() == 1)
check(t.functions[0] == "ExtractResume")
check(t.asserts.len() == 1)
check(t.asserts[0] == "name == \"Grace Hopper\"")
check_msg(t.evidence_source == "fixture", "evidence source should be fixture")
```

</details>

### SAML analysis — prompt variables

#### extracts the distinct head names a prompt references

- extracts the distinct head names a prompt references


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the distinct head names a prompt references")
val f = find_function(fixture_module(), "ExtractResume")
val vars = prompt_variables(f.prompt)
check_msg(list_has(vars, "resume_text"), "resume_text should be a prompt variable")
check_msg(list_has(vars, "saml.output_format"), "saml.output_format should be a prompt variable")
check_msg(vars.len() == 2, "expected exactly two distinct variables")
```

</details>

#### returns nothing for a prompt with no references

- returns nothing for a prompt with no references


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nothing for a prompt with no references")
check(prompt_variables("plain prose, no placeholders").len() == 0)
```

</details>

### SAML analysis — reachable types

#### walks nested class references transitively

- walks nested class references transitively


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks nested class references transitively")
val m = fixture_module()
val types = reachable_types(m, "Resume")
check_msg(list_has(types, "Resume"), "root must be included")
check_msg(list_has(types, "Education"), "nested class must be reached")
check_msg(list_has(types, "Seniority"), "referenced enum must be reached")
check_msg(types.len() == 3, "expected exactly Resume, Education, Seniority")
```

</details>

#### skips primitives and undeclared names

- skips primitives and undeclared names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips primitives and undeclared names")
val m = fixture_module()
check(reachable_types(m, "text").len() == 0)
check(reachable_types(m, "NotDeclared").len() == 0)
```

</details>

#### includes parameter schema in a function's reachable set

- includes parameter schema in a function's reachable set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes parameter schema in a function's reachable set")
val a = analysis_for(fixture_module(), "ScoreResume")
check_msg(list_has(a.reachable_types, "Seniority"), "return type must be reachable")
check_msg(list_has(a.reachable_types, "Resume"), "param type must be reachable")
check(list_has(a.reachable_types, "Education"))
```

</details>

### SAML analysis — evidence ranking

#### ranks unevidenced, examples_only, tested, and red_proven

- ranks unevidenced, examples_only, tested, and red_proven


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks unevidenced, examples_only, tested, and red_proven")
check(evidence_state(0, 0, 0) == "unevidenced")
check(evidence_state(0, 2, 0) == "examples_only")
check(evidence_state(1, 0, 0) == "tested")
check_msg(evidence_state(1, 1, 1) == "red_proven", "a counter-example plus a test is red_proven")
check_msg(evidence_state(0, 1, 1) == "red_proven", "a counter-example plus an example is red_proven")
```

</details>

#### does not promote a bare counter-example to red_proven

- does not promote a bare counter-example to red_proven


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not promote a bare counter-example to red_proven")
check_msg(evidence_state(0, 0, 1) == "unevidenced", "a counter-example alone backs nothing")
```

</details>

#### ranks the fixture functions from their real evidence

- ranks the fixture functions from their real evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks the fixture functions from their real evidence")
val m = fixture_module()
val extract = analysis_for(m, "ExtractResume")
check_msg(extract.evidence_state == "red_proven", "ExtractResume has a test and a counter-example")
check(extract.example_count == 1)
check(extract.counter_example_count == 1)
check(list_has(extract.covering_tests, "resume_extraction"))
check(list_has(extract.evidence_kinds, "fixture"))
val score = analysis_for(m, "ScoreResume")
check_msg(score.evidence_state == "unevidenced", "ScoreResume has no test and no example")
```

</details>

### SAML analysis — external spec coverage

#### moves a function from unevidenced to tested via external coverage, never to red_proven

- moves a function from unevidenced to tested via external coverage, never to red_proven


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves a function from unevidenced to tested via external coverage, never to red_proven")
val m = fixture_module()
val score_fn = find_function(m, "ScoreResume")
val external: [text] = ["external:test/scratch/score_spec.spl:scores a senior candidate"]
val a = analyze_function_with_external(m, score_fn, external)
check_msg(a.evidence_state == "tested", "external coverage alone should reach tested")
check_msg(a.evidence_state != "red_proven", "external coverage must never reach red_proven")
check_msg(list_has(a.covering_tests, "external:test/scratch/score_spec.spl:scores a senior candidate"), "external entry must appear in covering_tests with its prefix")
```

</details>

#### leaves evidence_state unchanged from before when external coverage is empty

- leaves evidence_state unchanged from before when external coverage is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves evidence_state unchanged from before when external coverage is empty")
val m = fixture_module()
val score_fn = find_function(m, "ScoreResume")
val no_external: [text] = []
val a = analyze_function_with_external(m, score_fn, no_external)
val baseline = analysis_for(m, "ScoreResume")
check(a.evidence_state == baseline.evidence_state)
check(a.evidence_state == "unevidenced")
```

</details>

#### warns E-SAML-1810 when the only evidence is external and there is no counter-example

- warns E-SAML-1810 when the only evidence is external and there is no counter-example


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns E-SAML-1810 when the only evidence is external and there is no counter-example")
val m = fixture_module()
val score_fn = find_function(m, "ScoreResume")
val external: [text] = ["external:test/scratch/score_spec.spl:scores a senior candidate"]
val a = analyze_function_with_external(m, score_fn, external)
check_msg(any_contains(a.warnings, "E-SAML-1810"), "external-only evidence must warn E-SAML-1810")
```

</details>

#### does not warn E-SAML-1810 when a counter-example already exists

- does not warn E-SAML-1810 when a counter-example already exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn E-SAML-1810 when a counter-example already exists")
val m = fixture_module()
val extract_fn = find_function(m, "ExtractResume")
val external: [text] = ["external:test/scratch/extract_spec.spl:extracts a resume"]
val a = analyze_function_with_external(m, extract_fn, external)
check_msg(any_contains(a.warnings, "E-SAML-1810") == false, "a function with an in-file counter-example never needs the external-only warning")
```

</details>

#### analyze_module_with_specs merges discovered coverage per function without touching analyze_module's default

- analyze_module_with_specs merges discovered coverage per function without touching analyze_module's default


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("analyze_module_with_specs merges discovered coverage per function without touching analyze_module's default")
val m = fixture_module()
val spec_paths: [text] = ["test/scratch/score_spec.spl"]
val spec_sources: [text] = ["describe \"scoring\":\n    it \"scores a senior candidate\":\n        ScoreResume(resume, rubric)\n"]
val an = analyze_module_with_specs(m, spec_paths, spec_sources)
var score = nil
for a in an.functions:
    if a.name == "ScoreResume":
        score = a
check_msg(score != nil, "ScoreResume must be present in the analysis")
check_msg(score.evidence_state == "tested", "discovered external coverage should lift ScoreResume to tested")
check_msg(analysis_for(m, "ScoreResume").evidence_state == "unevidenced", "plain analyze_module must stay unaffected")
```

</details>

### SAML analysis — static warnings

#### warns on a prompt variable bound to nothing

- warns on a prompt variable bound to nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on a prompt variable bound to nothing")
val a = analysis_for(fixture_module(), "ScoreResume")
check_msg(list_has(a.unbound_vars, "candidate"), "candidate is not a param and must be unbound")
check_msg(list_has(a.unbound_vars, "rubric") == false, "rubric is a param and must be bound")
check_msg(any_contains(a.warnings, "E-SAML-1300"), "an unbound variable must warn")
check(any_contains(a.warnings, "unbound variable `candidate`"))
```

</details>

#### warns when the prompt never renders saml.output_format

- warns when the prompt never renders saml.output_format


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when the prompt never renders saml.output_format")
val m = fixture_module()
val score = analysis_for(m, "ScoreResume")
check(score.has_output_format == false)
check_msg(any_contains(score.warnings, "output_format"), "missing output_format must warn")
val extract = analysis_for(m, "ExtractResume")
check_msg(extract.has_output_format, "ExtractResume does render saml.output_format")
check_msg(any_contains(extract.warnings, "output_format") == false, "no output_format warning when present")
```

</details>

#### warns when sensitive fields are reached without @redact

- warns when sensitive fields are reached without @redact


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when sensitive fields are reached without @redact")
val m = fixture_module()
val score = analysis_for(m, "ScoreResume")
check_msg(any_contains(score.sensitive_fields, "Resume.email"), "email is @sensitive(pii)")
check_msg(any_contains(score.warnings, "E-SAML-1900"), "sensitive without @redact must warn")
val extract = analysis_for(m, "ExtractResume")
check_msg(any_contains(extract.sensitive_fields, "Resume.email"), "ExtractResume also reaches email")
check_msg(any_contains(extract.warnings, "E-SAML-1900") == false, "@redact suppresses the privacy warning")
```

</details>

#### carries attribute-derived facts onto the analysis record

- carries attribute-derived facts onto the analysis record


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries attribute-derived facts onto the analysis record")
val m = fixture_module()
val extract = analysis_for(m, "ExtractResume")
check(extract.traced)
check_msg(extract.parse_strictness == "strict", "@parse(strictness: strict) must be read")
val score = analysis_for(m, "ScoreResume")
check(score.traced == false)
check_msg(score.parse_strictness == "compatible", "default strictness is compatible")
```

</details>

#### rolls module findings up with a nonzero warning count

- rolls module findings up with a nonzero warning count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rolls module findings up with a nonzero warning count")
val an = analyze_module(fixture_module())
check(an.module_name == "resume")
check(an.functions.len() == 2)
check(an.error_count == 0)
check_msg(an.warning_count > 0, "the fixture is written to trip warnings")
check_msg(an.orphan_classes.len() == 0, "every class is reachable from some llm fn")
```

</details>

### SAML emit — BAML projection

#### emits a class block per declared class

- emits a class block per declared class


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a class block per declared class")
val baml = emit_baml(fixture_module())
check_msg(baml.contains("class Resume {"), "expected a BAML class block for Resume")
check(baml.contains("class Education {"))
check_msg(baml.contains("struct ExtractionStats") == false, "structs are never projected")
```

</details>

#### maps primitive types onto BAML spellings

- maps primitive types onto BAML spellings


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps primitive types onto BAML spellings")
check(baml_type_name("text") == "string")
check(baml_type_name("i64") == "int")
check(baml_type_name("f64") == "float")
check(baml_type_name("bool") == "bool")
check_msg(baml_type_name("Resume") == "Resume", "declared names pass through")
val baml = emit_baml(fixture_module())
check_msg(baml.contains("name string"), "text maps to string")
check_msg(baml.contains("skills string[]"), "[text] maps to string[]")
check_msg(baml.contains("email string?"), "text? maps to string?")
check(baml.contains("education Education[]"))
```

</details>

#### carries @alias through to the BAML field

- carries @alias through to the BAML field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries @alias through to the BAML field")
val baml = emit_baml(fixture_module())
check(baml.contains("@alias(\"candidate_name\")"))
check_msg(baml.contains("@alias(\"staff_engineer\")"), "enum aliases project too")
```

</details>

#### rewrites saml.output_format to ctx.output_format

- rewrites saml.output_format to ctx.output_format


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites saml.output_format to ctx.output_format")
val f = find_function(fixture_module(), "ExtractResume")
val body = baml_prompt_body(f.prompt)
check_msg(body.contains("ctx.output_format"), "saml.output_format must be rewritten")
check_msg(body.contains("saml.output_format") == false, "no saml.* reference may survive")
check_msg(emit_baml(fixture_module()).contains("ctx.output_format"), "the emitted source uses the rewrite")
```

</details>

#### reports every semantic the projection cannot carry

- reports every semantic the projection cannot carry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports every semantic the projection cannot carry")
val losses = baml_projection_losses(fixture_module())
check_msg(any_contains(losses, "struct ExtractionStats"), "native struct is a projection loss")
check_msg(any_contains(losses, "Resume.email"), "@sensitive is a projection loss")
check_msg(any_contains(losses, "redact"), "@redact is a runtime policy loss")
check_msg(any_contains(losses, "parse"), "@parse is a runtime policy loss")
```

</details>

### SAML emit — reports and manual

#### emits an SDN manifest with the module's real counts

- emits an SDN manifest with the module's real counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an SDN manifest with the module's real counts")
val m = fixture_module()
val sdn = emit_sdn_manifest(m, analyze_module(m))
check(sdn.contains("format = \"simple.saml.manifest.v1\""))
check(sdn.contains("module = \"resume\""))
check(sdn.contains("class_count = 2"))
check(sdn.contains("function_count = 2"))
check(sdn.contains("test_count = 1"))
check(sdn.contains("error_count = 0"))
check_msg(sdn.contains("evidence_state = \"red_proven\""), "per-function evidence lands in the manifest")
```

</details>

#### emits an analysis report naming each function and its evidence

- emits an analysis report naming each function and its evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an analysis report naming each function and its evidence")
val report = emit_analysis_report(analyze_module(fixture_module()))
check(report.contains("SAML ANALYSIS " + FIXTURE_PATH))
check(report.contains("ExtractResume(resume_text: text) -> Resume"))
check(report.contains("evidence:   red_proven"))
check(report.contains("E-SAML-1900"))
```

</details>

#### emits a markdown manual with a heading and evidence badge per function

- emits a markdown manual with a heading and evidence badge per function


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a markdown manual with a heading and evidence badge per function")
val m = fixture_module()
val md = emit_markdown_manual(m, analyze_module(m))
check(md.contains("# SAML module `resume`"))
check_msg(md.contains("### `ExtractResume`"), "expected the function heading")
check_msg(md.contains("### `ScoreResume`"), "expected the second function heading")
check_msg(md.contains("**red-proven**"), "expected the red-proven evidence badge")
check_msg(md.contains("**unevidenced**"), "expected the unevidenced badge")
check_msg(md.contains("## BAML projection"), "the manual states its projection losses")
check(md.contains("Do not edit"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/saml/saml_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SAML parser — module shell, SAML parser — class fields, SAML parser — enums and attributes, SAML parser — llm fn, SAML parser — comment-embedded cases, SAML parser — test blocks, SAML analysis — prompt variables, SAML analysis — reachable types, SAML analysis — evidence ranking, SAML analysis — external spec coverage, SAML analysis — static warnings, SAML emit — BAML projection, SAML emit — reports and manual.
- SAML parser — module shell
- SAML parser — class fields
- SAML parser — enums and attributes
- SAML parser — llm fn
- SAML parser — comment-embedded cases
- SAML parser — test blocks
- SAML analysis — prompt variables
- SAML analysis — reachable types
- SAML analysis — evidence ranking
- SAML analysis — external spec coverage
- SAML analysis — static warnings
- SAML emit — BAML projection
- SAML emit — reports and manual

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `16ca5775751b06405ab3174f483d24859452b32b16516762831fa11237d6a95d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16ca5775751b06405ab3174f483d24859452b32b16516762831fa11237d6a95d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16ca5775751b06405ab3174f483d24859452b32b16516762831fa11237d6a95d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/saml/saml_spec.spl
mirror: doc/06_spec/01_unit/lib/saml/saml_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/saml/saml_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/saml/saml_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/saml/saml_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the module name and source path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/saml/saml_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects every top-level declaration kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/saml/saml_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses plain, optional, and list field types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
