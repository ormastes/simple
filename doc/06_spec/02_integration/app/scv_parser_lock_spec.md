# scv_parser_lock_spec

> Purpose: This spec proves SCV parser trust/lock hardening (SCV-IMPL-P-04):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_parser_lock_spec

Purpose: This spec proves SCV parser trust/lock hardening (SCV-IMPL-P-04):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_lock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV parser trust/lock hardening (SCV-IMPL-P-04):
the v2 registry pins grammar id, source, artifact sha256, TS ABI, protocol,
runtime kind, and signature per entry; a missing local artifact or an
unlocked parser is an ERROR that literally states "no implicit downloads"
(nothing is ever fetched); and upgrades (version or artifact change) open a
NEW parser-index generation while an identical reinstall does not.
Audience: Maintainers of the SCV parser trust layer.

## Scenarios

### scv parser trust/lock hardening (v2 registry)

#### pins grammar id, source, sha256, TS ABI, protocol, runtime kind and signature on install

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PARSER-LOCK-001
# @req REQ-SSPEC-INTEGRATION
step "install a locally present wasm grammar"
val root = _repo("pin")
val wasm = "{root}/grammar.wasm"
_write_wasm(wasm)
val out = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "https://example.invalid/foo", "1.0.0", "wasm", "abi14", "scv/parser/v1", wasm, "sig-aaaa")
expect(out).to_contain("parser-lock2 foo tree-sitter-foo 1.0.0")
expect(out).to_contain("runtime=wasm")
expect(out).to_contain("abi=abi14")
expect(out).to_contain("protocol=scv/parser/v1")
expect(out).to_contain("signature=sig-aaaa")
step "the lock entry carries every pinned field"
val lock = file_read(scv_parser_lock2_path(root))
expect(lock).to_contain("parser2|foo|tree-sitter-foo|https://example.invalid/foo|1.0.0|wasm|abi14|scv/parser/v1|")
expect(lock).to_contain("sig-aaaa")
step "verify checks every entry and reports the generation"
val verify = scv_parser_lock2_verify(root)
expect(verify).to_contain("parser-lock2-verify checked=1")
expect(verify).to_contain("generation=1")
```

</details>

#### never downloads: missing local artifact and unlocked parser are explicit no-implicit-downloads errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PARSER-LOCK-001
val root = _repo("nodl")
step "install with a missing local artifact fails, naming the policy"
val out = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "https://example.invalid/foo", "1.0.0", "wasm", "abi14", "scv/parser/v1", "{root}/absent.wasm", "sig-a")
expect(out).to_contain("ERROR")
expect(out).to_contain("no implicit downloads")
step "resolving a parser that was never locked fails, naming the policy"
val miss = scv_parser_lock2_resolve(root, "foo", "tree-sitter-foo")
expect(miss).to_contain("ERROR")
expect(miss).to_contain("no implicit downloads")
```

</details>

#### rejects unsafe metadata and a missing signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PARSER-LOCK-001
val root = _repo("unsafe")
val wasm = "{root}/grammar.wasm"
_write_wasm(wasm)
val bad = scv_parser_lock2_install(root, "foo", "tree|sitter", "src", "1.0.0", "wasm", "abi14", "scv/parser/v1", wasm, "sig-a")
expect(bad).to_contain("ERROR unsafe parser lock metadata")
val nosig = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "src", "1.0.0", "wasm", "abi14", "scv/parser/v1", wasm, "")
expect(nosig).to_contain("ERROR missing parser signature")
```

</details>

#### upgrades open a new index generation; identical reinstall does not

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PARSER-LOCK-001
val root = _repo("gen")
val wasm1 = "{root}/g1.wasm"
_write_wasm(wasm1)
step "first install lands in generation 1"
val first = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "src", "1.0.0", "wasm", "abi14", "scv/parser/v1", wasm1, "sig-a")
expect(first).to_contain("generation=1")
val gen1 = scv_parser_index_generation(root)
assert_equal(gen1, 1)
val path1 = scv_parser_index_gen_path(root)
expect(path1).to_contain("parser_index.gen1")
step "identical reinstall keeps the generation"
val again = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "src", "1.0.0", "wasm", "abi14", "scv/parser/v1", wasm1, "sig-a")
expect(again).to_contain("generation=1")
assert_equal(scv_parser_index_generation(root), 1)
step "upgrading the version opens generation 2 with a distinct index path"
val (_o, _e, code) = process_run("/bin/sh", ["-c", "printf '\\000asm\\001\\000\\000\\000\\001' > '{root}/g2.wasm'"])
assert_equal(code, 0)
val upgraded = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "src", "1.1.0", "wasm", "abi14", "scv/parser/v1", "{root}/g2.wasm", "sig-b")
expect(upgraded).to_contain("generation=2")
assert_equal(scv_parser_index_generation(root), 2)
val path2 = scv_parser_index_gen_path(root)
expect(path2).to_contain("parser_index.gen2")
assert_false(path1 == path2)
step "resolve returns the upgraded pinned entry"
val entry = scv_parser_lock2_resolve(root, "foo", "tree-sitter-foo")
expect(entry).to_contain("|1.1.0|")
expect(entry).to_contain("sig-b")
```

</details>

#### verify fails closed on artifact tamper (sha256 mismatch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-PARSER-LOCK-001
val root = _repo("tamper")
val wasm = "{root}/g.wasm"
_write_wasm(wasm)
val out = scv_parser_lock2_install(root, "foo", "tree-sitter-foo", "src", "1.0.0", "wasm", "abi14", "scv/parser/v1", wasm, "sig-a")
expect(out).to_contain("parser-lock2")
step "tamper with the stored artifact"
val lock = file_read(scv_parser_lock2_path(root))
val hash = lock.trim().split("|")[8]
val (_o, _e, code) = process_run("/bin/sh", ["-c", "printf '\\000asm\\001\\000\\000\\000\\377' > '{root}/.scv/parsers/{hash}.wasm'"])
assert_equal(code, 0)
val verify = scv_parser_lock2_verify(root)
expect(verify).to_contain("ERROR parser artifact hash mismatch")
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
- `REQ-SCV-PARSER-LOCK-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48d60fa2a3deb9c62ef6741a1179b7d03fe94e7df6d98c12a8de42683aa59db8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48d60fa2a3deb9c62ef6741a1179b7d03fe94e7df6d98c12a8de42683aa59db8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48d60fa2a3deb9c62ef6741a1179b7d03fe94e7df6d98c12a8de42683aa59db8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/app/scv_parser_lock_spec.spl
mirror: doc/06_spec/02_integration/app/scv_parser_lock_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_parser_lock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_parser_lock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_parser_lock_spec.spl:40:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'pins grammar id, source, sha256, TS ABI, protocol, runtime kind and signature on install' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_parser_lock_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'never downloads: missing local artifact and unlocked parser are explicit no-implicit-downloads errors' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_parser_lock_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects unsafe metadata and a missing signature' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_parser_lock_spec.spl:84:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'upgrades open a new index generation; identical reinstall does not' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
