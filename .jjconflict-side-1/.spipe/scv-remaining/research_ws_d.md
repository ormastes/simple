# SCV Completion Gate Audit — Workstream D

Date: 2026-05-15
Auditor: Research Agent (Sonnet 4.6)

---

## Criterion 1: Every MVP item is either implemented and tested or explicitly deferred

**Verdict: PASS**

MVP Order items (scv.md lines 27–35) mapped to implementation:

| # | MVP Step | Evidence |
|---|----------|----------|
| 1 | Raw byte VCS: content-addressed chunks, trees, commits, op-log, auto-snapshot, watch | scv_mvp_spec.spl (11 ex), scv_storage_spec.spl (6 ex), scv_refs_safety_spec.spl (5 ex) |
| 2 | Line and binary fallback parser: balanced line tree, chunk tree for binary | scv_parser_binary_spec.spl (1 ex), scv_parser_artifacts_spec.spl (9 ex) |
| 3 | Tree-sitter integration | scv_parser_wasm_spec.spl (12 ex), scv_wasm_executor_spec.spl (6 ex) |
| 4 | Structural diff view: `--raw`, `--syntax`, `--ignore-formatting` | scv_diff_spec.spl (3 ex), scv_structural_match_spec.spl (8 ex) |
| 5 | Commit gates: private savepoints, parse/compile/test gate | scv_gates_spec.spl (8 ex) + doc/06_spec gates (3 ex) |
| 6 | Node-level merge | scv_merge_spec.spl (5 ex) + doc/06_spec merge (3 ex) |
| 7 | Pack storage and GC | scv_pack_import_spec.spl (7 ex), scv_pack_verify_safety_spec.spl (6 ex), scv_delta_pack_spec.spl (8 ex) |
| 8 | Git import/export | scv_git_interop_spec.spl (19 ex), scv_git_full_interop_spec.spl (21 ex) |

All 8 MVP steps implemented and tested. Production network transport and delta
chains were deferred in Workstream G scope note (scv.md line 158–159) and are
now implemented (PROD-005, PROD-006). No open deferral gaps remain.

---

## Criterion 2: Same-size byte edits change content IDs

**Verdict: PARTIAL**

Evidence found:

- `test/integration/app/scv_mvp_spec.spl:8` — test title: "snapshots, detects
  same-size edits, and restores exact bytes". Script writes `a\nb\nc\n` then
  `A\nb\nc\n` (identical byte count, different content). Assertions:
  - `expect(out).to_contain("M a.txt")` — status correctly detects the modified file
  - `expect(out).to_contain("restored=A|b|c|")` — restore retrieves the new content

Gap: The test verifies that `status` detects the change and that `restore-op`
materializes distinct bytes (implying distinct stored content). However, no test
explicitly captures and compares two chunk/sha256 object IDs to assert they are
different string values. The behavior is implicitly tested (restore would be
a no-op or wrong if IDs were the same), but the completion gate criterion asks
that "byte identity tests prove same-size edits change content IDs" — an explicit
hash-comparison assertion is absent.

Architecture documentation (`doc/04_architecture/scv.md`) states: "Same-size
edits must still be detected through byte hashing."

**Recommended action:** Add a test in `scv_storage_spec.spl` that snapshots two
same-byte-count edits, extracts the chunk sha256 IDs from both commit tree rows,
and asserts `CHUNK1 != CHUNK2`. One `it` block, ~15 lines.

---

## Criterion 3: Unsupported text and binary files snapshot and restore byte-exactly

**Verdict: PARTIAL**

Evidence found:

- `test/integration/app/scv_parser_binary_spec.spl:8` — "writes fallback binary
  syntax nodes as chunk trees". Snapshots a 64-byte `/dev/zero` binary blob,
  verifies `byte_len: 64`, `kind: binary`, `kind: chunk`, `parser: fallback-binary`,
  and `blob.bin|fallback|sha256_` (sha256 prefix only, not pinned value). (lines 8–19)
- `test/integration/app/scv_delta_pack_spec.spl:32` — "delta decoding reconstructs
  original bytes exactly". Writes a text file, snapshots, pack-write-v2,
  pack-read-object, diffs against original: `expect(out).to_contain("roundtrip=same")`
  (line 35). This exercises a text file via the pack path, not `restore-op`.
- `test/integration/app/scv_mvp_spec.spl:8` — text file restore-op asserts
  `restored=A|b|c|`. (line 51) Text only.

Gap: No test does the end-to-end binary path: binary file → `snapshot` →
`restore-op` → `diff` original vs restored bytes. The parser_binary_spec verifies
the parse-index metadata structure (chunk tree, byte_len) but does not restore the
blob and compare bytes. The delta_pack roundtrip test is text-only and uses
`pack-read-object` rather than `restore-op`. The completion gate criterion requires
that *both* unsupported text and binary files can "snapshot and restore byte-exactly"
— the binary restore-op path has no direct test.

**Recommended action:** Add a test in `test/integration/app/scv_parser_binary_spec.spl`
(or `scv_storage_spec.spl`) that writes an arbitrary binary blob, snapshots, deletes
the file, runs `restore-op`, then diffs the restored file against the original with
`cmp` or `diff`. One `it` block, ~15 lines.

---

## Criterion 4: Parser failures still produce private savepoints

**Verdict: PASS**

Evidence:

- `test/integration/app/scv_wasm_executor_spec.spl:37` — "AC-1d: parser failures
  allow private snapshot to proceed". Script installs a bad WASM grammar (`bad.wasm`),
  runs `snapshot`, then asserts `test -n "$SNAP"` (snapshot commit appears in log).
  (lines 37–46)
- `test/integration/app/scv_gates_spec.spl:19` — "exposes parsed_error and rejects
  unknown commit states". Marks state as `parsed_error`, asserts `state=parsed_error`
  in log (line 22), confirming parsed_error is a valid private state.
- Architecture principle (scv.md line 21): "Private savepoints always succeed when
  bytes can be read."

Both the parser-failure path and the resulting snapshot visibility are exercised.

---

## Criterion 5: Public-ready states require configured gates

**Verdict: PASS**

Evidence:

- `test/integration/app/scv_network_remote_spec.spl` — describe "scv network remote
  public_ready gate enforcement":
  - "blocks network push when public_ready is absent even after snapshot and
    test-gate" — asserts `ERROR public_ready gate not set`, `bad_code=1` (verified
    in batch search output)
  - "allows network push after all gates pass including public_ready" — positive path
- `test/integration/app/scv_gates_spec.spl:37` — "exports public artifacts only
  after public_ready". Asserts `ERROR public-export marker state is not public_ready`
  when attempting export without the gate. (line 57)
- `test/integration/app/scv_gates_spec.spl:94` — "pushes public artifacts to a
  filesystem remote only after public_ready"
- `test/integration/app/scv_public_remote_spec.spl` — 7 examples covering public
  push/pull with gate enforcement.

Gate requirement is enforced on both filesystem and network push paths.

---

## Criterion 6: x86-64 and ARM64 documented as primary supported targets

**Verdict: PASS**

Evidence:

- `doc/03_plan/agent_tasks/scv.md:14` — "Primary developer targets are x86-64 and
  ARM64. Compatibility targets are x86, ARM32, RISC-V 64, and RISC-V 32 where the
  Simple runtime supports them."
- `doc/04_architecture/scv.md:149` — "Primary targets are x86-64 and ARM64. x86,
  ARM32, RISC-V 64, and RISC-V 32 are compatibility targets as runtime support
  allows. No design decision should assume RISC-V-only execution."

Both plan and architecture docs carry the required platform statement.

---

## Summary of Gaps

| # | Criterion | Verdict | Gap |
|---|-----------|---------|-----|
| 1 | MVP items all accounted for | PASS | None |
| 2 | Same-size edits change content IDs | PARTIAL | No explicit hash-comparison assertion |
| 3 | Binary snapshot/restore byte-exact | PARTIAL | No binary restore-op byte-comparison test |
| 4 | Parser failures produce private savepoints | PASS | None |
| 5 | Public-ready requires configured gates | PASS | None |
| 6 | x86-64/ARM64 documented as primary | PASS | None |

**Two gaps found**: Criteria 2 and 3 are PARTIAL. Both gaps are test-coverage
gaps only — no implementation changes required. Both can be closed with one new
`it` block each (~15–20 lines per spec).

---

## Recommended Actions

**Action 1 (closes Criterion 2 gap):**
Add to `test/integration/app/scv_storage_spec.spl`:

```
it "same-size byte edits produce different chunk content IDs":
    # Write file v1, snapshot, capture chunk sha256 ID
    # Write file v2 (same size, different bytes), snapshot, capture chunk sha256 ID
    # assert CHUNK_ID_1 != CHUNK_ID_2
    expect(out).to_not_contain("CHUNK_IDS_EQUAL")
    # or: capture both sha256_ prefixed IDs and assert not_equal
```

The script should use `grep` on the tree object row to extract the `sha256_...`
chunk reference for each commit, print both, and assert they differ.

Estimated size: ~20 lines in the spec, no implementation changes required.

**Action 2 (closes Criterion 3 gap):**
Add to `test/integration/app/scv_parser_binary_spec.spl`:

```
it "binary file restores byte-exactly after snapshot":
    # Write N bytes of arbitrary binary content (e.g. head -c 128 /dev/urandom)
    # snapshot → rm blob.bin → restore-op <OP>
    # cmp original.bin blob.bin && echo match || echo mismatch
    expect(out).to_contain("match")
    expect(out).to_contain("exit=0")
```

The script captures the HEAD_OP after snapshot, removes the file, runs
`restore-op`, and uses `cmp` to verify bit-exact restoration.

Estimated size: ~15 lines in the spec, no implementation changes required.
