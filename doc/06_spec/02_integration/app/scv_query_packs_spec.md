# scv_query_packs_spec

> Purpose: This spec proves SCV's per-language entity query packs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_query_packs_spec

Purpose: This spec proves SCV's per-language entity query packs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_query_packs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV's per-language entity query packs
(SCV-IMPL-P-06): every pack is versioned (`scv/query-pack/v1`) and declares
declaration kinds, name fields, signature capture, scope-parent policy,
commutative lists, comment/doc nodes and reference rules; extraction runs the
same engine over each pack (indent scopes for Simple/Python, brace scopes for
Rust); the Simple pack reproduces the I-03 symbol-entity rows exactly; packs
project onto the P-05 generic CST (imports as a commutative list, comments as
trivia); and a fallback-parsed .spl file now carries `name:` fields on its
declaration nodes so structural anchors are NAMED (the missing `name:` anchor
fields the plan row calls out).
Audience: Maintainers of the SCV parser / identity layers.

## Scenarios

### scv entity query packs

#### ships a versioned pack per language with every rule category

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-QUERY-PACKS-001
# @req REQ-SSPEC-INTEGRATION
step "the pack format names its version"
assert_equal(scv_query_pack_version(), "scv/query-pack/v1")
step "simple, python and rust each have a pack; an unknown language has none"
val langs = scv_query_pack_languages()
expect(_join(langs)).to_contain("simple\n")
expect(_join(langs)).to_contain("python\n")
expect(_join(langs)).to_contain("rust\n")
assert_equal(scv_query_pack_for_language("cobol"), "")
step "the simple pack declares decl kinds, name fields, signatures, scope, commutative lists, comment/doc and reference rules"
val pack = scv_query_pack_for_language("simple")
expect(pack).to_contain("pack: scv/query-pack/v1")
expect(pack).to_contain("language: simple")
expect(pack).to_contain("scope: indent")
expect(pack).to_contain("comment: #")
expect(pack).to_contain("doc: \"\"\"")
expect(_join(scv_query_pack_rules(pack, "decl"))).to_contain("fn|fn |sig")
expect(_join(scv_query_pack_rules(pack, "decl"))).to_contain("type|struct |scope")
expect(_join(scv_query_pack_rules(pack, "member"))).to_contain("enum|variant|ident")
expect(_join(scv_query_pack_rules(pack, "commutative"))).to_contain("imports|use ")
expect(_join(scv_query_pack_rules(pack, "reference"))).to_contain("import|use ")
step "the rust pack uses brace scopes and // comments"
val rust = scv_query_pack_for_language("rust")
expect(rust).to_contain("scope: brace")
expect(rust).to_contain("comment: //")
```

</details>

#### extracts Simple declarations with signatures and reproduces the symbol-entity rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-QUERY-PACKS-001
step "rows are kind|name|line|container|signature"
val rows = scv_query_pack_extract_decls("simple", _sample())
val joined = _join(rows)
expect(joined).to_contain("const|LIMIT|1||")
expect(joined).to_contain("fn|top|3||(a: i64) -> i64")
expect(joined).to_contain("type|Point|6||")
expect(joined).to_contain("field|x|7|Point|i64")
expect(joined).to_contain("fn|norm|10|Point|() -> i64")
expect(joined).to_contain("enum|Color|13||")
expect(joined).to_contain("variant|Red|14|Color|")
expect(joined).to_contain("trait|Shape|17||")
expect(joined).to_contain("fn|area|18|Shape|() -> i64")
step "a trailing line comment is not part of the signature (string-literal aware)"
val commented = _join(scv_query_pack_extract_decls("simple", "fn g(x: i64) -> i64:  # note\n    x\nfn h(s: text) -> text:  # \"q\"\n    \"a#b\"\n"))
expect(commented).to_contain("fn|g|1||(x: i64) -> i64\n")
expect(commented).to_contain("fn|h|3||(s: text) -> text\n")
step "symbol_entity extraction is the same rows without the signature column"
val sym = _join(scv_symbol_extract_decls(_sample()))
var expected = ""
for r in rows:
    val p = r.split("|")
    expected = expected + "{p[0]}|{p[1]}|{p[2]}|{p[3]}\n"
assert_equal(sym, expected)
```

</details>

#### runs the same engine over python (indent) and rust (brace) packs

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-QUERY-PACKS-001
step "python: class scope via indentation, def signatures"
val py = _join(scv_query_pack_extract_decls("python", "import os\n\nclass Box:\n    def area(self, k):\n        return k\n\ndef main():\n    pass\n"))
expect(py).to_contain("type|Box|3||")
expect(py).to_contain("fn|area|4|Box|(self, k)")
expect(py).to_contain("fn|main|7||()")
step "rust: struct fields and enum variants inside brace scopes, fn outside"
val rs = _join(scv_query_pack_extract_decls("rust", "use std::io;\n\npub struct Pt {\n    x: i64,\n    y: i64,\n}\n\nenum Color { Red, Green }\n\npub fn top(a: i64) -> i64 {\n    a\n}\n"))
expect(rs).to_contain("type|Pt|3||")
expect(rs).to_contain("field|x|4|Pt|i64")
expect(rs).to_contain("field|y|5|Pt|i64")
expect(rs).to_contain("enum|Color|8||")
expect(rs).to_contain("fn|top|10||(a: i64) -> i64")
step "an unknown language extracts nothing rather than guessing"
assert_equal(scv_query_pack_extract_decls("cobol", "fn x():\n").len(), 0)
```

</details>

#### projects a pack onto the generic CST with commutative imports and trivia comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-QUERY-PACKS-001
val src = "use std.a\nuse std.b\n# note\nfn f(x: i64) -> i64:\n    x\n"
val doc = scv_query_pack_cst("simple", "m.spl", src)
step "the projection is a valid scv/cst/v1 document"
assert_equal(scv_cst_document_error(doc), "")
val file = scv_cst_document_node(doc)
assert_equal(scv_cst_kind(file), "file")
var imports = ""
var has_trivia = false
var fn_node = ""
for child in scv_cst_children(file):
    if scv_cst_kind(child) == "list" and scv_cst_label(child) == "imports":
        imports = child
    if scv_cst_kind(child) == "trivia":
        has_trivia = true
    if scv_cst_kind(child) == "named" and scv_cst_label(child) == "fn":
        fn_node = child
step "imports are a commutative list, so reordering them keeps the hash"
assert_equal(scv_cst_ordering(imports), "commutative")
assert_equal(scv_cst_children(imports).len(), 2)
val doc2 = scv_query_pack_cst("simple", "m.spl", "use std.b\nuse std.a\n# note\nfn f(x: i64) -> i64:\n    x\n")
assert_equal(scv_cst_hash(file), scv_cst_hash(scv_cst_document_node(doc2)))
step "comments are trivia and declarations are named nodes carrying name + signature atoms"
assert_true(has_trivia)
assert_false(fn_node == "")
expect(fn_node).to_contain("atom|name||f")
expect(fn_node).to_contain("atom|signature||(x: i64) -> i64")
step "members nest under their container as an ordered members list"
val nested = scv_cst_document_node(scv_query_pack_cst("simple", "p.spl", _sample()))
var point = ""
for child in scv_cst_children(nested):
    if scv_cst_kind(child) == "named" and child.contains("atom|name||Point"):
        point = child
assert_false(point == "")
expect(point).to_contain("list|members|ordered|")
expect(point).to_contain("atom|name||Point.x")
expect(point).to_contain("atom|name||Point.norm")
```

</details>

#### fallback-parsed .spl declaration nodes carry name fields so anchors are named

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-QUERY-PACKS-001
val root = _repo("anchors")
val path = "{root}/m.spl"
file_write(path, _sample())
step "parse through the parser; fallback execution is still reported honestly"
val out = scv_parse_file(root, path)
expect(out).to_contain("execution=fallback-line")
val node = _node_id(out)
assert_false(node == "")
step "structural anchors are NAMED for declarations (fn, type, member) — the missing name: fields"
var keys = ""
for a in scv_extract_anchors(root, node, ""):
    keys = keys + scv_anchor_id(a) + "\n"
expect(keys).to_contain("named:top\n")
expect(keys).to_contain("named:Point\n")
expect(keys).to_contain("named:Point.x\n")
expect(keys).to_contain("named:Color.Red\n")
expect(keys).to_contain("named:Shape.area\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-QUERY-PACKS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `93c412e78adf1c864b772c64ea544a5ed299ee12699be444d84d492a198f2274`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93c412e78adf1c864b772c64ea544a5ed299ee12699be444d84d492a198f2274`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93c412e78adf1c864b772c64ea544a5ed299ee12699be444d84d492a198f2274`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/app/scv_query_packs_spec.spl
mirror: doc/06_spec/02_integration/app/scv_query_packs_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_query_packs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_query_packs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_query_packs_spec.spl:59:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ships a versioned pack per language with every rule category' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_query_packs_spec.spl:87:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'extracts Simple declarations with signatures and reproduces the symbol-entity rows' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_query_packs_spec.spl:113:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'runs the same engine over python (indent) and rust (brace) packs' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_query_packs_spec.spl:130:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'projects a pack onto the generic CST with commutative imports and trivia comments' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
