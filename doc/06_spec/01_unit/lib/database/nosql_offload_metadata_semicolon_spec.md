# NoSQL document metadata encode/decode round-trip

> `nosql_document_encode_metadata` / `nosql_document_decode_metadata` serialize

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NoSQL document metadata encode/decode round-trip

`nosql_document_encode_metadata` / `nosql_document_decode_metadata` serialize

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-NOSQL-001 |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`nosql_document_encode_metadata` / `nosql_document_decode_metadata` serialize
a `Dict<text, text>` into a single `;`-joined `key=value` line for storage in
`NoSqlDocumentRecord` lines. Before this fix, `;` and `=` inside a metadata
value were not escaped, so a value containing `;` (e.g. "a;b") was split into
extra bogus pairs on decode, silently corrupting or dropping metadata instead
of round-tripping it.

## Scenarios

### nosql_document metadata round-trip

#### round-trips a value containing a semicolon

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a value containing a semicolon
   - Expected: decoded.get("desc") equals `Some("a;b")`
   - Expected: decoded.keys().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips a value containing a semicolon")
val original: Dict<text, text> = {"desc": "a;b"}
val encoded = nosql_document_encode_metadata(original)
val decoded = nosql_document_decode_metadata(encoded)
expect(decoded.get("desc")).to_equal(Some("a;b"))
expect(decoded.keys().len()).to_equal(1)
```

</details>

#### round-trips multiple keys where one value contains a semicolon

- round-trips multiple keys where one value contains a semicolon
   - Expected: decoded.get("a") equals `Some("1")`
   - Expected: decoded.get("b") equals `Some("x;y")`
   - Expected: decoded.get("c") equals `Some("3")`
   - Expected: decoded.keys().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips multiple keys where one value contains a semicolon")
val original: Dict<text, text> = {"a": "1", "b": "x;y", "c": "3"}
val encoded = nosql_document_encode_metadata(original)
val decoded = nosql_document_decode_metadata(encoded)
expect(decoded.get("a")).to_equal(Some("1"))
expect(decoded.get("b")).to_equal(Some("x;y"))
expect(decoded.get("c")).to_equal(Some("3"))
expect(decoded.keys().len()).to_equal(3)
```

</details>

#### still round-trips a plain value with no special characters

- still round-trips a plain value with no special characters
   - Expected: encoded equals `key=value`
   - Expected: decoded.get("key") equals `Some("value")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still round-trips a plain value with no special characters")
val original: Dict<text, text> = {"key": "value"}
val encoded = nosql_document_encode_metadata(original)
expect(encoded).to_equal("key=value")
val decoded = nosql_document_decode_metadata(encoded)
expect(decoded.get("key")).to_equal(Some("value"))
```

</details>

#### round-trips a value containing a backslash

- round-trips a value containing a backslash
   - Expected: decoded.get("path") equals `Some("a\\b")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips a value containing a backslash")
val original: Dict<text, text> = {"path": "a\\b"}
val encoded = nosql_document_encode_metadata(original)
val decoded = nosql_document_decode_metadata(encoded)
expect(decoded.get("path")).to_equal(Some("a\\b"))
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dcbe068684ff11f6e1ac0545058a9a31ec22e9a521fcbf5b36f3ad7342b28030`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dcbe068684ff11f6e1ac0545058a9a31ec22e9a521fcbf5b36f3ad7342b28030`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dcbe068684ff11f6e1ac0545058a9a31ec22e9a521fcbf5b36f3ad7342b28030`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.spl
mirror: doc/06_spec/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a value containing a semicolon' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips multiple keys where one value contains a semicolon' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/nosql_offload_metadata_semicolon_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still round-trips a plain value with no special characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
