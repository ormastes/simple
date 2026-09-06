# NVMe Spec → SSpec Conversion Plan, and the SSpec Infra It Requires

Status: PLAN (2026-09-01). Umbrella: `nvme_complete_fw_mdsoc_offload_master_plan.md`
(§11.3 G6 gap). Research basis: `simpleemu_unified_emulator_nvme_riscv_test_infra_plan.md`
§11 (SVAP — "Markdown is a projection, not the canonical test product").

Every claim below is marked **MEASURED** (with `file:line`) or **PROPOSAL**.
The honesty boundary from EMU invariant 8 governs the whole document:
**functional vectors may project to ATE content; SSpec does NOT replace ATPG**,
and no wording here or in any generated artifact may claim Simple generates
manufacturing test patterns.

---

## 1. Measured baseline — what SSpec offers today

### 1.1 DSL surface (MEASURED)

- `describe` / `it` / `step(...)` / `expect(...).to_equal/.to_contain/...` are
  the working surface; defined via `src/lib/nogc_sync_mut/spec.spl` and used
  as `use std.spec.step` in every modern spec (e.g.
  `test/feature/usage/bitfield_runtime_compat_spec.spl`).
- Skip/ignore condition decorators: `src/lib/gc_async_mut/spec/condition.spl`,
  `decorators.spl` (files actually read); `src/lib/nogc_sync_mut/spec/` holds
  same-named siblings incl. `skip_governance.spl` (measured by `ls` only).
- Feature metadata + registry + doc generation:
  `src/lib/gc_async_mut/spec/feature_doc.spl` (register/get by category).
- Scenario evidence vocabulary and helpers:
  `src/lib/common/spec/scenario_evidence.spl`, `scenario_helpers.spl`
  (step results, contains/status/file/JSON-field checkers).
- Dual-run oracle helper: `src/lib/common/spec/dual_run.spl` —
  `dual_check_f64` / `dual_check_text` with explicit NaN and -0.0 policy;
  explicitly test-scope only, not a live shadow.
- Environment/evidence admission: `src/lib/common/spec/environment_profile.spl`
  — pure, never turns configured capability into proof of execution.

### 1.2 Typed-evidence pipeline (MEASURED — corrects a prior claim)

Workstream F reported that `EvidenceRequest`, an `EvidenceProvider` trait, and
a spec-layer `EvidenceManifest` "exist only in comments." **That claim is
one-third right:**

- `EvidenceRequest` — **comment-only, confirmed.** Its only occurrence is the
  pipeline diagram comment at `src/lib/common/spec/evidence/model.spl:7`
  (`EvidenceRequest -> provider -> RawArtifact -> format adapter -> ...`).
  No record definition exists anywhere under `src/lib/` or `src/app/`.
- `EvidenceProvider` trait — **comment-only as a trait, confirmed**, but the
  *provider machinery is real code*: `CounterpartEvidenceProvider` is named
  only in a comment
  (`src/lib/nogc_sync_mut/spec/evidence/counterpart/provider_runner.spl:7`,
  "design §13"), yet that file is a working runner with `ProviderKind`
  dispatch (`native_in_process`, `process_bridge`; the qemu/remote/isolated
  kinds return `unavailable` with a named diagnostic, never a silent pass),
  a provider registry, and the fail-closed rule that a non-runnable source
  still yields a `SourceResult` rather than shrinking the comparison matrix.
- `EvidenceManifest` — **the prior claim is WRONG.** It is real code:
  `pub struct EvidenceManifest` at
  `src/lib/common/spec/evidence/model.spl:499`, with
  `evidence_manifest_lines` (`:540`), `evidence_manifest_is_complete`
  (`:570`), schema constant `EVIDENCE_MANIFEST_SCHEMA =
  "simple.sspec.evidence.v1"`, consumed by `regeneration_gate.spl:48/63/90`
  and `manual_render.spl:221` (provenance appendix). The byte-identical
  regeneration gate hashes rendered manuals and distinguishes expected drift
  (`run_id`/`environment`) from stale claims (`spec_sha256`/`artifact_sha256`).
- Confirmed real, as reported: typed selectors
  (`EvidenceSelectorKind` at `model.spl:29` — `canonical_node`,
  `protocol_field`, `json_pointer`, `terminal_region`, `pixel_region`,
  `binary_field`, `byte_range`, `bit_range`), the fail-closed comparator
  (`evidence_comparator.spl` — unresolved selector fails, all-ignore oracle
  fails, tolerance over non-numbers fails), **12 format adapters**
  (`src/lib/common/spec/evidence/format/` — 12 `.spl` files incl.
  `binary_layout.spl`, `text_protocol.spl`, `json_document.spl`), the
  Markdown renderer (`manual_render.spl`, sole renderer, pipe-escaping so
  untrusted cell content cannot forge columns), legacy/untyped adapters
  (`legacy_facade.spl`, `untyped_capture.spl`), and the SPipe extension
  namespace `simple.sspec.evidence.ext.v1` (`spipe_extension.spl`).

**Consequence:** the SVAP gap is narrower than workstream F reported. The
canonical-record spine (selectors, canonical evidence, manifest, comparator,
regeneration gate) exists. What is genuinely missing is the FRONT of the
pipeline (`EvidenceRequest` as a typed record, a declared provider trait) and
the *emission* of SVAP records from a scenario.

### 1.3 Bitfield/table testing (MEASURED)

- `bitfield` declarations parse and run: `bitfield CompatFlags(u8): ready: 1 /
  mode: 3 / _: 4` (`test/feature/usage/bitfield_runtime_compat_spec.spl`),
  including adjacent-field-preservation checks. `@packed` struct bitfield
  syntax is **parser diagnostic only**
  (`test/feature/usage/packed_struct_bitfield_syntax_spec.spl` documents the
  boundary; fallback is `bitfield`).
- **No first-class table-driven form exists.** No `it_each` /
  parameterized-case construct anywhere under `src/lib/` or `test/`
  (searched `it_each|for_each_case|parameterized|table_test`; hits were
  coincidental — simd/database files, not a test form). Loops that generate N
  checks DO work today — `bitfield_spec.spl` iterates `val PARSER_PHASE =
  [...]` lists; the firmware's own checker accumulates
  `fail = fail + expect_eq(...)` (`nvme_admin.spl:445-519`). The measured
  gap is **row identity**: a failing check inside a loop does not name its
  row in the verdict or the generated manual. That, not "loops are missing,"
  is what makes thousands of NVMe field rows infeasible today.

### 1.4 Existing NVMe specs (MEASURED)

`test/03_system/app/nvme_firmware/` holds 20 files. The house idiom
(`nvme_base_spec_commands_spec.spl`): run a firmware demo/checker via
`process_run`, assert named `NVME-... PASS` verdict lines with
`to_contain`, guard against `FAIL` markers, and state a **Claim Boundary**
section ("does not prove a freshly linked RV32 ELF, QEMU boot, ... PCIe
interoperability, or power-loss durability"). `nvme_emu_media_slice_b_spec.spl`
follows the same shape for media/retention slices.

### 1.5 Firmware conformance floor (MEASURED — bounds what is testable)

- Host command payload is one word: `data: i64  # simulated single-byte
  payload stand-in` (`examples/09_embedded/simpleos_nvme_fw/fw/nvme_types.spl`,
  `NvmeCmd`). No PRP/SGL, no real data buffers.
- 13 admin opcodes (`fw/nvme_admin_types.spl:14-26`: Delete/Create SQ+CQ,
  Get Log, Identify, Abort, Set/Get Features, Async Event, FW Commit/Download,
  Format NVM) + 5 I/O opcodes; `IdentifyData` is a flat struct
  (`fw/nvme_admin.spl:107-110`), not a byte-accurate 4096-byte Identify page.
- **No doorbell / phase-tag / MMIO host transport exists at all.** CC, CSTS,
  AQA, ASQ/ACQ, doorbell stride — none of the NVMe controller register file
  is modeled anywhere in-tree.

Anything transport-shaped is therefore **untestable today** and must not be
claimed.

---

## 2. Deliverable A — SSpec infra improvements (each grounded in a measured gap)

Ordered; each item states exists / missing / minimal change / verification.
All records are **SDN**, never JSON/YAML. No inheritance; generics `<>`.

### A1. Row-identified table cases (`spec_table`)

- **Exists:** loops generating N `expect` calls (§1.3); nothing names the row.
- **Missing:** a case form where each row carries an id that appears in the
  verdict line and the generated manual on failure.
- **Minimal change:** a pure library helper in `src/lib/common/spec/`
  (PROPOSAL: `table_case.spl`): `pub struct TableRow` (id: text, plus the
  row's typed payload via a caller-supplied closure) and
  `pub fn check_rows<T>(rows: [T], id_of: fn(T) -> text, check: fn(T) ->
  RowVerdict) -> TableVerdict` that accumulates named failures and renders
  one `ManualBlock` table (reusing `manual_render.spl` — do NOT add a second
  renderer). A failing table fails the enclosing `it` with the offending row
  ids in the message. No DSL/parser change; this is a library, matching the
  house accumulate-and-report idiom already in `nvme_admin.spl`.
- **Verified by:** a spec whose fixture table contains one deliberately bad
  row must fail naming exactly that row id (mutation-red per the SSpec dual
  check rule), and pass when the row is corrected.

### A2. Register/bitfield field-table form

- **Exists:** `EvidenceSelectorKind.binary_field` / `bit_range` /
  `byte_range` (`model.spl:29-158`) already express "byte 7 bit 63";
  `format/binary_layout.spl` adapts binary captures; the fail-closed
  comparator rejects unresolved selectors.
- **Missing:** a declarative register table record and the four derived rule
  families (RO write-ignored, RW round-trip, RW1C clear-on-one,
  RSVD reads-zero/write-ignored; reset value on init).
- **Minimal change:** PROPOSAL `src/lib/common/spec/register_table.spl`:
  `pub struct RegField` (name, offset_bits, width_bits, access enum
  {ro, rw, rw1c, rsvd}, reset: i64, clause: text) and
  `pub fn field_cases(f: RegField) -> [TableRow]` that EXPANDS one field row
  into its positive/negative/reset/reserved cases mechanically, checked via
  A1 against a caller-supplied read/write closure pair. Selectors are emitted
  as existing `bit_range` selectors — **no new selector namespace.** Tables
  themselves live as SDN data files next to the spec so the same table feeds
  both the test run and SVAP emission (A4).
- **Verified by:** a fixture register model with one deliberately writable
  reserved bit must fail the RSVD rule naming field + rule; a correct model
  passes all four families.

### A3. First-class negative / reset / persistence case kinds

- **Exists:** negative checks are ad hoc (`SC_INVALID_OPCODE` expectations,
  `_expect_no_fail_marker`); reset/persistence appear only as prose in slice
  specs.
- **Missing:** a case-kind tag so coverage accounting can prove "this field
  has positive AND negative AND reset AND fault AND persistence evidence" —
  required verbatim by the master plan's advertise-nothing-unproven rule.
- **Minimal change:** an enum `CaseKind {positive, negative, reset, fault,
  persistence}` on `TableRow` (A1) and a counting function
  `coverage_of(rows_run) -> per-field CaseKind set`, emitted into the
  `EvidenceManifest` flow (real code, §1.2) as manifest lines. No runner
  change.
- **Verified by:** the capability-gate spec (B4) refuses to mark a bit
  provable while any kind is absent.

### A4. SVAP emission path (the G6 requirement)

- **Exists:** the back half — CanonicalEvidence → comparator →
  ComparisonResult → ManualBlock → manifest → regeneration gate (§1.2), plus
  the SPipe extension namespace for carrying payloads.
- **Missing:** the front half: `EvidenceRequest` as a real record, and
  emission of the research's SVAP core records (TestIntent, ExecutionPlan,
  Stimulus, Oracle, Schedule, Coverage — research §11.3) from a scenario.
- **Minimal change (staged):**
  1. Promote the `model.spl:7` comment to code: `pub struct EvidenceRequest`
     (scenario_id, step_id, selector list, provider kind, case ids) in
     `model.spl`, schema-versioned under the existing
     `simple.sspec.evidence.v1` discipline.
  2. PROPOSAL `src/lib/common/spec/svap/` emitting **SDN** records:
     `TestIntent` (clause id + CaseKind matrix from A3), `Stimulus` (the A2
     table rows as command/register transactions — for NVMe today these are
     the in-tree command structs, not pin vectors), `Oracle` (the comparator
     OracleSpec already in use), `ResultManifest` (= the existing
     `EvidenceManifest`, reused not duplicated).
  3. Projection 1 (`bin/simple test`) is the existing runner — the spec runs
     the rows directly. Projection 2 (ATE-functional content) is a docgen-side
     exporter reading the same SDN pack. **Honesty boundary:** projection 2
     carries functional vectors and schedules only; ATPG patterns come from
     external tools which SVAP may only package/schedule/trace (research
     §11.10). Pin-level vector emission is BLOCKED on PinIR (master plan
     workstream G) and is out of scope here; until then projection 2 emits
     transaction-level content and says so in the manifest.
- **Verified by:** one NVMe scenario emits its SDN pack; the pack re-renders
  byte-identically under `regeneration_gate`; the ordinary test run and the
  pack's case list are checked equal (same case ids, same verdicts) —
  a divergence fails.

**Deliberately NOT proposed:** a new DSL keyword, a second Markdown renderer,
a JSON interchange format, or a generic "test framework rewrite." Everything
above is additive library code on the measured spine.

---

## 3. Deliverable B — NVMe spec → SSpec conversion method

### B1. Unit of conversion: the clause record

One NVMe base-spec clause (e.g. "5.17 Identify command", "3.1.5 CC —
Controller Configuration") becomes one **SDN clause record** (hand-authored;
the NVMe PDF is not in-tree and no automated extraction is claimed; shape sketch below, not literal SDN syntax):

```
clause:
  id: "NVME-2.0c-5.17"        # spec edition pinned in the id
  title: "Identify command"
  kind: command | register | log_page | behavior
  fields: [RegField...]        # A2 rows, when kind is register/log_page
  conformance: mandatory | optional | not_applicable
  status: proven | partial | untestable   # see B4
  scenario: test/03_system/app/nvme_firmware/<spec>.spl#<describe>
```

Records live under `test/03_system/app/nvme_firmware/clauses/` as SDN
(PROPOSAL). `status: untestable` requires a stated blocker (e.g. "no MMIO
transport" — measured §1.5), so the ledger is honest by construction.

### B2. Traceability chain

clause id → scenario (`@req` + clause id in the `it` docstring, already the
house idiom) → assertion (row id from A1 embeds the clause id:
`NVME-2.0c-5.17/CNS-01h/reset`) → result (`EvidenceManifest` lines carry the
row ids; the regeneration gate pins the rendered manual). Each link is
checkable: a clause record naming a scenario that does not exist, or a
scenario whose rows reference no clause, fails a lint-style ledger check
(PROPOSAL: `scripts/check/check-nvme-clause-ledger.shs`, same
verdict-line/exit conventions as existing guards; never gate on `bin/simple
run` exit codes — verdict lines are the evidence).

### B3. Evidence grade

Reuse the Claim Boundary idiom as a graded field rather than prose-only:
`grade: model` (host-model Simple run — everything today), `grade: rv32`
(scalar firmware checker), `grade: qemu`, `grade: board`. Grades are
declared per scenario and copied into the manifest;
`environment_profile.spl`'s rule applies — configured capability is never
proof, so a grade above `model` requires the corresponding execution receipt.

### B4. Untestable-until-proven capability gating (master plan rule)

A capability bit (Identify field, log page, feature id) starts
`status: untestable`. It may move to `proven` only when its clause record
shows a complete CaseKind matrix (A3): positive + negative + reset + fault +
persistence, all green in the ordinary run. The firmware's advertised
Identify content is then derived from the ledger, not hand-set — a bit whose
matrix is incomplete must read as unsupported/zero. Verification: a spec that
flips one matrix entry red must flip the advertised bit off (dual check:
pass, and mutation-red).

### B5. Honest scoping — P0

**In P0 (testable today, `grade: model`):** exactly the measured floor —
Admin: Identify (controller + namespace, flat-struct fields only), Create/
Delete SQ/CQ + binding rules, Set/Get Features (queue count), Abort, Get Log
(as implemented), plus reserved-field guards; NVM: Read, Write, Write Zeroes,
DSM/TRIM, Flush. These are what `nvme_base_spec_commands_spec.spl` already
exercises. P0's job is to RESTATE that coverage as clause records + A1/A2
tables with full CaseKind matrices — a representation upgrade, not a
coverage claim.

**Explicitly NOT P0, with the measured reason:**
- Controller register file (CC, CSTS, AQA, ASQ/ACQ, doorbells, phase tags):
  no MMIO transport exists (§1.5). P1, gated on the transport landing.
- Byte-accurate Identify / log pages (4096-byte layouts, PRP/SGL): payload is
  one `i64` word (§1.5). P1.
- Firmware download/commit content, Format NVM data paths, Sanitize,
  reservations, multiple namespaces, ZNS/KV command sets, fabrics: not
  implemented; claiming them would be false. P2+/out of scope.
- Power-loss/persistence at real-media fidelity: slice specs model it; grade
  stays `model` until the emulator lane (workstream E) provides better.

A conversion "covering the NVMe spec" is not claimed at any stage; the ledger
IS the claim, and every record carries its status.

### B6. Staging

1. **Stage 0** — land A1 (table rows) + A3 (CaseKind); convert ONE clause
   (Identify Controller) end-to-end as the template, incl. the ledger check.
2. **Stage 1** — A2 register-table form against the flat `IdentifyData`
   fields and feature words (real in-tree layouts); complete P0 clause
   records; capability gating B4 wired to the ledger.
3. **Stage 2** — A4 SVAP emission for the converted clauses; regeneration +
   projection-equality gates green.
4. **Stage 3+** — unlocked by firmware work, not by this plan: MMIO/doorbell
   transport → CC/CSTS clauses; real payloads → byte-accurate Identify.

---

## 4. Deliverable C

`doc/06_spec/hardware/nvme/nvme_base_command_set_example.md` — a
**hand-authored illustration of the target projected shape** (stated inside
the file). `doc/06_spec/` is generated-from-sspec territory mirroring
`test/` paths (structure.md: DO NOT refactor); this file becomes a real
generated artifact only when Stage 2's docgen path produces it, at which
point the hand-authored version is replaced, not edited.

## 5. What was not verified

- The exact definition site/shape of `describe`/`it`/`expect` matchers
  (located to `src/lib/nogc_sync_mut/spec.spl` by filename search only).
- `provider_runner.spl` "9 providers" count from workstream F — the runner
  and registry are real; the specific count was not re-counted.
- The research doc's SVAP record field lists (§11.3) were read as section
  titles + summaries, not full field-by-field text.
- No NVMe specification PDF is in-tree; all NVMe layout facts above come from
  the firmware sources cited, and anything beyond them is marked ILLUSTRATIVE
  in the example file.
