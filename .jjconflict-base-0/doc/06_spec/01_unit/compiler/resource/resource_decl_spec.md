# `resource` declaration parsing — WP-A acceptance

> `bin/simple test` re-execs a child **Rust seed** binary, and the seed's parser

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `resource` declaration parsing — WP-A acceptance

`bin/simple test` re-execs a child **Rust seed** binary, and the seed's parser

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-A) |
| Design | doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §1 |
| Source | `test/01_unit/compiler/resource/resource_decl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Why this spec feeds source STRINGS instead of writing `resource` directly

`bin/simple test` re-execs a child **Rust seed** binary, and the seed's parser
is what reads a spec file's own module-level syntax — not the pure-Simple
frontend in `src/compiler/10.frontend/**`. Control probe: `layer ProbeLayer`,
an already-landed pure-Simple soft keyword, fails in a spec file with
"function `layer` not found". So no pure-Simple frontend change can ever alter
how a spec file's own declarations parse, and the plan's WP-A acceptance
criterion (write `resource File` directly in a spec) is unreachable until
stage-3 self-host lands.

The reachable oracle is the one `test/01_unit/compiler/parser/const_spec.spl`
uses: drive `parse_module_body()` over a source string, which runs the edited
pure-Simple parser under the interpreter.

## The load-bearing property

`resource` is a **contextual (soft) keyword**, recognized only at
declaration-start position. 112 identifier uses of `resource` exist in `src/`
today — including inside the compiler's own source (`85.mdsoc/security.spl`,
`85.mdsoc/weaving/join_point_kind.spl`) — so a hard/reserved keyword would
break the compiler's own rebuild.

## Scenarios

### resource declaration: Grammar-A parsing

#### parses `@sffi(prefix: ..., invalid: -1) resource File` into one decl

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses `@sffi(prefix: ..., invalid: -1) resource File` into one decl
   - Expected: decls.len() equals `1`
   - Expected: decl_get_tag(decls[0]) equals `DECL_VAL`
   - Expected: resource_name_of(decls[0]) equals `File`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses `@sffi(prefix: ..., invalid: -1) resource File` into one decl")
val decls = parse_ok("@sffi(prefix: \"rt_io_file\", invalid: -1)\nresource File\n")
expect(decls.len()).to_equal(1)
expect(decl_get_tag(decls[0])).to_equal(DECL_VAL)
expect(resource_name_of(decls[0])).to_equal("File")
```

</details>

#### round-trips the @sffi metadata onto the declaration

- round-trips the @sffi metadata onto the declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips the @sffi metadata onto the declaration")
val decls = parse_ok("@sffi(prefix: \"rt_io_file\", invalid: -1)\nresource File\n")
val meta = resource_meta_of(decls[0])
assert_contains(meta, "prefix=rt_io_file")
# Negative sentinels are TWO tokens (minus + int); dropping the sign
# here would silently record `invalid=1`.
assert_contains(meta, "invalid=-1")
```

</details>

#### accepts the full documented key schema

- accepts the full documented key schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the full documented key schema")
val decls = parse_ok(
    "@sffi(prefix: \"rt_image\", handle: i64, invalid: 0, retain: rt_image_ref, release: rt_image_unref, sharing: foreign, thread_safe: false)\n" +
    "resource Image\n"
)
val meta = resource_meta_of(decls[0])
assert_contains(meta, "retain=rt_image_ref")
assert_contains(meta, "release=rt_image_unref")
assert_contains(meta, "sharing=foreign")
assert_contains(meta, "thread_safe=false")
```

</details>

#### does not leak @sffi metadata onto the next declaration

- does not leak @sffi metadata onto the next declaration
   - Expected: decls.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not leak @sffi metadata onto the next declaration")
val decls = parse_ok(
    "@sffi(prefix: \"rt_cuda_primary_ctx\", sharing: foreign)\nresource CudaPrimaryContext\n" +
    "@sffi(prefix: \"rt_io_file\", invalid: -1)\nresource File2\n"
)
expect(decls.len()).to_equal(2)
assert_contains(resource_meta_of(decls[0]), "sharing=foreign")
# File2 declared no `sharing:` — a leaked pending slot would show it.
assert_false(resource_meta_of(decls[1]).contains("sharing="))
```

</details>

#### does not leak @sffi metadata across an intervening fn declaration

- does not leak @sffi metadata across an intervening fn declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not leak @sffi metadata across an intervening fn declaration")
# The pending slot is cleared per-declaration, not only when a
# `resource` consumes it -- so an `@sffi` that lands on a non-resource
# decl must not survive to the next `resource`.
val decls = parse_ok(
    "@sffi(prefix: \"rt_a\", sharing: foreign)\nfn f() -> i64:\n    1\n" +
    "@sffi(prefix: \"rt_b\")\nresource B\n"
)
var b_meta = ""
for d in decls:
    val m = resource_meta_of(d)
    if m.contains("prefix=rt_b"):
        b_meta = m
assert_false(b_meta.contains("sharing="))
```

</details>

#### does not leak @sffi metadata across an intervening pub fn declaration

- does not leak @sffi metadata across an intervening pub fn declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not leak @sffi metadata across an intervening pub fn declaration")
# `pub fn` goes through parse_module_decl_with_visibility, a separate
# dispatch path with its own reset placement.
val decls = parse_ok(
    "@sffi(prefix: \"rt_a\", sharing: foreign)\npub fn g() -> i64:\n    1\n" +
    "@sffi(prefix: \"rt_c\")\nresource C\n"
)
var c_meta = ""
for d in decls:
    val m = resource_meta_of(d)
    if m.contains("prefix=rt_c"):
        c_meta = m
assert_false(c_meta.contains("sharing="))
```

</details>

### resource declaration: fail-closed validation

#### errors when the required prefix key is missing

- errors when the required prefix key is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when the required prefix key is missing")
assert_true(parse_reports_error("@sffi(invalid: -1)\nresource File\n"))
```

</details>

#### errors on a key outside the documented schema

- errors on a key outside the documented schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors on a key outside the documented schema")
assert_true(parse_reports_error("@sffi(prefix: \"rt_io_file\", bogus: 1)\nresource File\n"))
```

</details>

#### errors when the @sffi attribute is absent entirely

- errors when the @sffi attribute is absent entirely


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when the @sffi attribute is absent entirely")
assert_true(parse_reports_error("resource File\n"))
```

</details>

### resource declaration: soft-keyword recognition boundary

#### does not treat a bare `resource` at end of line as a declaration

- does not treat a bare `resource` at end of line as a declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not treat a bare `resource` at end of line as a declaration")
assert_false(parse_reports_error("val resource = 1\nval x = resource\n"))
```

</details>

#### does not treat `resource(` as a declaration

- does not treat `resource(` as a declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not treat `resource(` as a declaration")
assert_false(parse_reports_error("fn resource(n: i64) -> i64:\n    n\nval y = resource(1)\n"))
```

</details>

#### does not treat `resource.` as a declaration

- does not treat `resource.` as a declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not treat `resource.` as a declaration")
assert_false(parse_reports_error("class Box:\n    resource: text\nfn f(b: Box) -> text:\n    b.resource\n"))
```

</details>

### resource declaration: contextual-keyword regression

#### keeps `var resource = ...` parsing (mirrors 85.mdsoc/security.spl:257)

- keeps `var resource = ...` parsing (mirrors 85.mdsoc/security.spl:257)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps `var resource = ...` parsing (mirrors 85.mdsoc/security.spl:257)")
assert_false(parse_reports_error("var resource = \"x\"\n"))
```

</details>

#### keeps `val resource = ...` parsing

- keeps `val resource = ...` parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps `val resource = ...` parsing")
assert_false(parse_reports_error("val resource = 1\n"))
```

</details>

#### keeps a parameter named `resource` parsing

- keeps a parameter named `resource` parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a parameter named `resource` parsing")
assert_false(parse_reports_error("fn takes(resource: i64) -> i64:\n    resource + 1\n"))
```

</details>

#### keeps a field named `resource` parsing (mirrors join_point_kind.spl:10)

- keeps a field named `resource` parsing (mirrors join_point_kind.spl:10)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a field named `resource` parsing (mirrors join_point_kind.spl:10)")
assert_false(parse_reports_error("class SecurityGate:\n    capability: text\n    resource: text\n"))
```

</details>

#### keeps a function named `resource` parsing

- keeps a function named `resource` parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a function named `resource` parsing")
assert_false(parse_reports_error("fn resource() -> i64:\n    1\n"))
```

</details>

#### keeps `resource` as a bare expression statement parsing

- keeps `resource` as a bare expression statement parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps `resource` as a bare expression statement parsing")
assert_false(parse_reports_error("val resource = 1\nval other = resource\n"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-A)`
- **Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §1`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `32bf8bda0f69b566960e533075363d9599b31419c09ce3a52d0688a7c1c688bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32bf8bda0f69b566960e533075363d9599b31419c09ce3a52d0688a7c1c688bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32bf8bda0f69b566960e533075363d9599b31419c09ce3a52d0688a7c1c688bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/resource/resource_decl_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_decl_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_decl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_decl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_decl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/resource/resource_decl_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses `@sffi(prefix: ..., invalid: -1) resource File` into one decl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_decl_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips the @sffi metadata onto the declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_decl_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the full documented key schema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
