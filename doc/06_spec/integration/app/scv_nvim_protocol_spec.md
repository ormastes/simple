# scv_nvim_protocol_spec

> Purpose: This spec proves the SCV Neovim editor protocol `scv/editor/v1`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_nvim_protocol_spec

Purpose: This spec proves the SCV Neovim editor protocol `scv/editor/v1`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_nvim_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV Neovim editor protocol `scv/editor/v1`
(SCV-IMPL-P-07): open_buffer / apply_edit / parser_changed_ranges / save /
rename / refactor_transaction as a pure request→response layer over an
abstract in-process transport, where Neovim-supplied trees/ranges are HINTS
verified against bytes+artifact (reparsed via the parser session) and never
authoritative — a wrong hint is rejected with recomputed ranges, a correct
hint merely verified, and every response states `authority: bytes+artifact`.
Refactor transactions are all-or-nothing. The E-09 UDS transport wiring is a
recorded TODO in the module; nothing here depends on lane A's files.
Audience: Maintainers of the SCV editor integration layer.

## Scenarios

### scv neovim editor protocol (SCV-IMPL-P-07)

#### encodes and decodes requests, and names its protocol version

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
assert_equal(scv_nvim_protocol_version(), "scv/editor/v1")
val req = scv_nvim_request("apply_edit", ["path: /a.spl", "start_byte: 3"], "x\ny")
assert_equal(scv_nvim_req_field(req, "op"), "apply_edit")
assert_equal(scv_nvim_req_field(req, "path"), "/a.spl")
assert_equal(scv_nvim_req_field(req, "start_byte"), "3")
step "new_text payloads keep embedded newlines"
assert_equal(scv_nvim_req_new_text(req), "x\ny")
```

</details>

#### open_buffer parses from bytes and returns the tree root

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
val root = _fresh_root()
val resps = scv_nvim_serve(root, [_open_req("/b.spl", "fn a():\n    1\n")])
assert_equal(resps.len(), 1)
assert_equal(scv_nvim_resp_field(resps[0], "status"), "ok")
assert_not_equal(scv_nvim_resp_field(resps[0], "tree_root"), "")
step "every response states byte authority"
assert_equal(scv_nvim_resp_field(resps[0], "authority"), "bytes+artifact")
```

</details>

#### apply_edit reparses from bytes, records the exact TSInputEdit, and verifies hints

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
val root = _fresh_root()
val src = "fn a():\n    1\n\nfn b():\n    2\n"
var state: Dict<text, text> = {}
val (s1, _r1) = scv_nvim_handle(root, state, _open_req("/c.spl", src))
step "an edit without a hint reports hint_status none"
val edit_req = scv_nvim_request("apply_edit",
    ["path: /c.spl", "start_byte: 12", "old_end_byte: 13"], "9")
val (s2, r2) = scv_nvim_handle(root, s1, edit_req)
assert_equal(scv_nvim_resp_field(r2, "status"), "ok")
expect(scv_nvim_resp_field(r2, "input_edit")).to_contain("start_byte=12")
expect(scv_nvim_resp_field(r2, "input_edit")).to_contain("old_end_byte=13")
assert_equal(scv_nvim_resp_field(r2, "hint_status"), "none")
val computed = scv_nvim_resp_field(r2, "changed_ranges")
step "a hint matching the recomputed ranges is verified, never trusted blind"
val hint_req = scv_nvim_request("parser_changed_ranges",
    ["path: /c.spl", "hint_ranges: {computed}"], "")
val (s3, r3) = scv_nvim_handle(root, s2, hint_req)
assert_equal(scv_nvim_resp_field(r3, "hint_status"), "verified")
step "a wrong Neovim hint is rejected and the byte-derived ranges stand"
val bad_req = scv_nvim_request("parser_changed_ranges",
    ["path: /c.spl", "hint_ranges: 9999..10000"], "")
val (_s4, r4) = scv_nvim_handle(root, s3, bad_req)
expect(scv_nvim_resp_field(r4, "hint_status")).to_contain("rejected")
assert_equal(scv_nvim_resp_field(r4, "changed_ranges"), computed)
```

</details>

#### rejects out-of-bounds edits and unknown buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
val root = _fresh_root()
var state: Dict<text, text> = {}
val (s1, _r) = scv_nvim_handle(root, state, _open_req("/d.spl", "abc"))
val bad = scv_nvim_request("apply_edit",
    ["path: /d.spl", "start_byte: 2", "old_end_byte: 99"], "x")
val (_s2, r2) = scv_nvim_handle(root, s1, bad)
assert_equal(scv_nvim_resp_field(r2, "status"), "error")
val unknown = scv_nvim_request("apply_edit",
    ["path: /nope.spl", "start_byte: 0", "old_end_byte: 0"], "x")
val (_s3, r3) = scv_nvim_handle(root, s1, unknown)
assert_equal(scv_nvim_resp_field(r3, "status"), "error")
```

</details>

#### save writes the buffer bytes and checkpoints; rename moves the session

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
val root = _fresh_root()
val target = "{root}/saved_out.spl"
val reqs = [_open_req("/e.spl", "fn e():\n    5\n"),
    scv_nvim_request("save", ["path: /e.spl", "target: {target}"], ""),
    scv_nvim_request("rename", ["path: /e.spl", "to: /f.spl"], ""),
    scv_nvim_request("parser_changed_ranges", ["path: /f.spl"], ""),
    scv_nvim_request("parser_changed_ranges", ["path: /e.spl"], "")]
val resps = scv_nvim_serve(root, reqs)
assert_equal(scv_nvim_resp_field(resps[1], "status"), "ok")
assert_not_equal(scv_nvim_resp_field(resps[1], "checkpoint"), "")
assert_true(file_exists(target))
assert_equal(file_read(target), "fn e():\n    5\n")
step "after rename the new path answers and the old path is gone"
assert_equal(scv_nvim_resp_field(resps[2], "status"), "ok")
assert_equal(scv_nvim_resp_field(resps[3], "status"), "ok")
assert_equal(scv_nvim_resp_field(resps[4], "status"), "error")
```

</details>

#### refactor_transaction is all-or-nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
val root = _fresh_root()
var state: Dict<text, text> = {}
val (s1, _ra) = scv_nvim_handle(root, state, _open_req("/g.spl", "aaa bbb"))
val (s2, _rb) = scv_nvim_handle(root, s1, _open_req("/h.spl", "ccc ddd"))
step "one out-of-bounds edit rejects the whole transaction, no buffer changes"
val bad_txn = scv_nvim_request("refactor_transaction",
    ["edit: /g.spl|0|3|AAA", "edit: /h.spl|0|999|X"], "")
val (s3, r3) = scv_nvim_handle(root, s2, bad_txn)
assert_equal(scv_nvim_resp_field(r3, "status"), "error")
val probe = scv_nvim_request("save", ["path: /g.spl", "target: {root}/g_probe"], "")
val (_s4, _r4) = scv_nvim_handle(root, s3, probe)
assert_equal(file_read("{root}/g_probe"), "aaa bbb")
step "a valid multi-buffer transaction applies every edit"
val good_txn = scv_nvim_request("refactor_transaction",
    ["edit: /g.spl|0|3|AAA", "edit: /h.spl|4|7|DDD"], "")
val (s5, r5) = scv_nvim_handle(root, s3, good_txn)
assert_equal(scv_nvim_resp_field(r5, "status"), "ok")
assert_equal(scv_nvim_resp_field(r5, "applied"), "2")
val (s6, _r6) = scv_nvim_handle(root, s5,
    scv_nvim_request("save", ["path: /g.spl", "target: {root}/g_after"], ""))
val (_s7, _r7) = scv_nvim_handle(root, s6,
    scv_nvim_request("save", ["path: /h.spl", "target: {root}/h_after"], ""))
assert_equal(file_read("{root}/g_after"), "AAA bbb")
assert_equal(file_read("{root}/h_after"), "ccc DDD")
```

</details>

#### hint comparison is order- and duplicate-insensitive but content-strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-NVIM-PROTOCOL-001
assert_equal(scv_nvim_hint_status("", "0..5\n"), "none")
assert_equal(scv_nvim_hint_status("7..9,0..5,0..5", "0..5\n7..9\n"), "verified")
expect(scv_nvim_hint_status("0..6", "0..5\n")).to_contain("rejected")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-NVIM-PROTOCOL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c21137948f13e37bf995883f0d8363e7a971cde345a75738e353296c7839b0bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c21137948f13e37bf995883f0d8363e7a971cde345a75738e353296c7839b0bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c21137948f13e37bf995883f0d8363e7a971cde345a75738e353296c7839b0bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_nvim_protocol_spec.spl
mirror: doc/06_spec/integration/app/scv_nvim_protocol_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/integration/app/scv_nvim_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_nvim_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_nvim_protocol_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_nvim_protocol_spec.spl:42:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'encodes and decodes requests, and names its protocol version' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_nvim_protocol_spec.spl:52:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'open_buffer parses from bytes and returns the tree root' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_nvim_protocol_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'apply_edit reparses from bytes, records the exact TSInputEdit, and verifies hints' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_nvim_protocol_spec.spl:89:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects out-of-bounds edits and unknown buffers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
