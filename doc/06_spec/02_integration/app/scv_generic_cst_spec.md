# scv_generic_cst_spec

> Purpose: This spec proves SCV's generic CST IR (SCV-IMPL-P-05): a versioned

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_generic_cst_spec

Purpose: This spec proves SCV's generic CST IR (SCV-IMPL-P-05): a versioned

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_generic_cst_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV's generic CST IR (SCV-IMPL-P-05): a versioned
IR (`scv/cst/v1`) with node kinds File / Named / List(ordered|commutative) /
Atom / Trivia / Error; commutative lists hash order-insensitively while
ordered lists do not; documents validate fail-closed on unknown kinds or
version; and parser roots are stored and loaded keyed by revision+ContentId.
Audience: Maintainers of the SCV parser/CST layer.

## Scenarios

### scv generic CST IR

#### is versioned and exposes every node kind

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-GENERIC-CST-001
# @req REQ-SSPEC-INTEGRATION
step "the IR names its version"
assert_equal(scv_cst_ir_version(), "scv/cst/v1")
step "each kind constructs with the declared kind tag"
val atom = scv_cst_atom("identifier", "foo")
assert_equal(scv_cst_kind(atom), "atom")
assert_equal(scv_cst_label(atom), "identifier")
val trivia = scv_cst_trivia("  # comment")
assert_equal(scv_cst_kind(trivia), "trivia")
val err = scv_cst_error("unbalanced }")
assert_equal(scv_cst_kind(err), "error")
val named = scv_cst_named("fn_decl", [atom, trivia])
assert_equal(scv_cst_kind(named), "named")
assert_equal(scv_cst_children(named).len(), 2)
val lst = scv_cst_list("params", "ordered", [atom])
assert_equal(scv_cst_kind(lst), "list")
val file = scv_cst_file("main.spl", [named, lst, err])
assert_equal(scv_cst_kind(file), "file")
assert_equal(scv_cst_children(file).len(), 3)
```

</details>

#### documents carry the version and validate fail-closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-GENERIC-CST-001
val doc = scv_cst_document(scv_cst_file("a.spl", [scv_cst_atom("id", "x")]))
step "the document header carries scv/cst/v1"
expect(doc).to_contain("cst scv/cst/v1")
assert_equal(scv_cst_document_error(doc), "")
step "round-trip: the document node is the serialized root"
val node = scv_cst_document_node(doc)
assert_equal(scv_cst_kind(node), "file")
step "a wrong version is rejected"
val bad_version = doc.replace("cst scv/cst/v1", "cst scv/cst/v9")
expect(scv_cst_document_error(bad_version)).to_contain("ERROR unsupported cst version")
step "an unknown node kind is rejected"
val bad_kind = doc.replace("atom|", "blob|")
expect(scv_cst_document_error(bad_kind)).to_contain("ERROR")
step "a list ordering outside ordered|commutative is rejected"
val bad_list = scv_cst_document(scv_cst_list("params", "sideways", [scv_cst_atom("id", "x")]))
expect(scv_cst_document_error(bad_list)).to_contain("ERROR bad list ordering")
```

</details>

#### commutative lists hash order-insensitively; ordered lists do not

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-GENERIC-CST-001
val a = scv_cst_atom("id", "alpha")
val b = scv_cst_atom("id", "beta")
step "commutative: reordering children keeps the hash"
val c1 = scv_cst_list("imports", "commutative", [a, b])
val c2 = scv_cst_list("imports", "commutative", [b, a])
assert_equal(scv_cst_hash(c1), scv_cst_hash(c2))
step "ordered: reordering children changes the hash"
val o1 = scv_cst_list("stmts", "ordered", [a, b])
val o2 = scv_cst_list("stmts", "ordered", [b, a])
assert_false(scv_cst_hash(o1) == scv_cst_hash(o2))
step "different content changes a commutative hash too"
val c3 = scv_cst_list("imports", "commutative", [a, a])
assert_false(scv_cst_hash(c1) == scv_cst_hash(c3))
```

</details>

#### stores and loads parser roots keyed by revision plus ContentId

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-GENERIC-CST-001
val root = _repo("roots")
val doc = scv_cst_document(scv_cst_file("m.spl", [scv_cst_atom("id", "x")]))
step "the root key combines revision and ContentId"
val key = scv_cst_root_key("rev-7", "cid-abc")
expect(key).to_contain("rev-7")
expect(key).to_contain("cid-abc")
step "store then load round-trips by the same key"
val stored = scv_cst_root_store(root, "rev-7", "cid-abc", doc)
expect(stored).to_contain("cst-root")
expect(stored).to_contain("hash=")
assert_true(file_exists(scv_cst_root_path(root, "rev-7", "cid-abc")))
assert_equal(scv_cst_root_load(root, "rev-7", "cid-abc"), doc)
step "a different revision of the same content is a distinct root slot"
assert_equal(scv_cst_root_load(root, "rev-8", "cid-abc"), "")
step "an invalid document is refused, never stored"
val bad = doc.replace("cst scv/cst/v1", "cst scv/cst/v9")
val refused = scv_cst_root_store(root, "rev-9", "cid-abc", bad)
expect(refused).to_contain("ERROR")
assert_equal(scv_cst_root_load(root, "rev-9", "cid-abc"), "")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-GENERIC-CST-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `333c87a2837eb065ca8dad3c64cc2cf5d7040634580369d962c21558af83d040`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `333c87a2837eb065ca8dad3c64cc2cf5d7040634580369d962c21558af83d040`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `333c87a2837eb065ca8dad3c64cc2cf5d7040634580369d962c21558af83d040`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/app/scv_generic_cst_spec.spl
mirror: doc/06_spec/02_integration/app/scv_generic_cst_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_generic_cst_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_generic_cst_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_generic_cst_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'is versioned and exposes every node kind' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_generic_cst_spec.spl:56:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'documents carry the version and validate fail-closed' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_generic_cst_spec.spl:75:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'commutative lists hash order-insensitively; ordered lists do not' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_generic_cst_spec.spl:91:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'stores and loads parser roots keyed by revision plus ContentId' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
