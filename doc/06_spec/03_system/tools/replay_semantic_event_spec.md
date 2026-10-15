# Replay semantic event type contracts

Status: **13 PASS / 0 FAIL — non-admitting historical-seed diagnostic**. The coordinator executed this frozen canonical spec once: 822 ms, exit 0, peak RSS 223912 KiB, enforced limit 5859375 KiB, quiescent=1. Log, resource and exit receipts are under `build/phase-one-storage-gui-diagnostic/replay_semantic_event_spec/cycle-one.*`; source/producer inputs are bound by `semantic-event-cycle-one-inputs.sdn`. No passing case was rerun, and no production source or shared guide changed.

The exact retained seed SHA-256 is `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. Independent review verified all seven retained generation bindings, recorded in `/tmp/retained-phase1-seed-provenance-review-20261011.md` and the coordinator's `retained-generation-integrity-20261011.sdn`. The mutable marker `/tmp/beta-qual-4159b0b6/src/compiler_rust/target/bootstrap.current.env` and preflight `/tmp/beta-qual-4159b0b6/.simple/storage/build/bootstrap/bootstrap-preflight.env` are absent. Retained artifact identity supports this historical diagnostic provenance; it does not establish current Phase1 admission or fresh preflight. Resource containment receipts are not compiler-admission receipts. No marker/preflight was recreated.

This result is **not currently admitted Phase1, normal self-hosted/fullCLI, native, whole-suite or release qualification**. The diagnostic passed and is complete; it must not be rerun merely to obtain another green receipt.

## Actual behavior and dependencies

The ten original cases remain intact. New cases check all twelve explicit event IDs/names in both directions, the existing FunctionEnter fallback for values outside 0–11, and every constructor-initialized field. The mapping oracle supplies explicit IDs and names; a roundtrip alone cannot hide mutually incorrect conversions. The legacy size-constant assertion is preserved but does not establish actual wire layout.

Production owner: `src/lib/nogc_sync_mut/replay/semantic/trace_events.spl` (SHA-256 `e1ea7343ff5b95ce2da195d8167df7386b2f23b531227c18a9a3349d26fd4412`). `trace_events.spl` has no imports and exports the event type, kind and size constant. The only additional spec dependency is the shared `std.spec` harness. These are direct production dependencies; the coordinator's frozen execution manifest must also bind the actual shared harness and producer closure.

No binary codec, buffer offsets, serialized record size, live instrumentation, process replay or native tracing is exercised. The invalid-ID fallback documents current conversion behavior; it is not strict record validation. No production defect was established by this bounded static intake. A baseline failure must be recorded and scoped before authorizing a source fix.

## Evidence and admission limits

Requirement trace: `REQ-SSPEC-SYSTEM`. Coverage 80% is an admission target, not measured coverage. The canonical source has real assertions and visible steps; this manual is synchronized directly to it, while SPipe docgen remains pending. No normal self-hosted/native, full-Phase1 or release qualification is claimed. The historical seed provenance and missing current-authority pointers are explicitly recorded above.

The original canonical and legacy `test/system/replay_semantic_event_spec.spl` were fully byte-identical, SHA-256 `c569727b710466d36f8e48b5c1e018b85cfa5837e68214766c27ba49a6865225`. The duplicate was removed after preserving every original case; neither original header carried an additional requirement or tag. Bounded searches found no explicit legacy-path references in scripts, app source or system-test plans. Other lanes were not modified.

Canonical SHA-256: `b4df035ff39c8d357620e2238112edcbf2197a5f2c5e404539cf0125d655705d`. Preparation metadata: `build/phase-one-storage-gui-diagnostic/replay-type-contracts-prepared.sdn`. The first and only baseline executed this complete canonical file once. All cases passed; no further runtime execution is planned.

## Scenarios and visible steps

Every scenario contains a visible `step(...)` describing its operation. Detailed assertions appear in the exact executable source below.

| Case | Scenario | Evidence |
|---|---|---|
| 1 | FunctionEnter to_i32 returns 0 | Diagnostic PASS |
| 2 | FunctionExit to_i32 returns 1 | Diagnostic PASS |
| 3 | ObjectAlloc to_i32 returns 3 | Diagnostic PASS |
| 4 | AsyncSpawn to_i32 returns 8 | Diagnostic PASS |
| 5 | from_i32(0) gives FunctionEnter | Diagnostic PASS |
| 6 | from_i32(11) gives AsyncComplete | Diagnostic PASS |
| 7 | create sets kind field correctly | Diagnostic PASS |
| 8 | create initialises seq to 0 | Diagnostic PASS |
| 9 | event_kind() roundtrips back to BorrowStart | Diagnostic PASS |
| 10 | SEMANTIC_EVENT_SIZE is 68 | Diagnostic PASS |
| 11 | preserves every event identifier and public name in both directions | Diagnostic PASS |
| 12 | uses the existing FunctionEnter fallback for out-of-range identifiers | Diagnostic PASS |
| 13 | initializes every unused record field to zero without losing the kind | Diagnostic PASS |

<details>
<summary>Exact executable SSpec source</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/nogc_sync_mut/replay/semantic/trace_events.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# @tag:system
# Pure event model contracts; wire codec and live/native tracing are separate obligations.

use std.spec.{describe, it, expect, step}
use std.nogc_sync_mut.replay.semantic.trace_events.{SemanticEvent, SemanticEventKind, SEMANTIC_EVENT_SIZE}

fn expect_semantic_kind(kind: SemanticEventKind, code: i32, label: text):
    expect(kind.to_i32()).to_equal(code)
    expect(kind.to_text()).to_equal(label)
    val recovered = SemanticEventKind.from_i32(code)
    expect(recovered.to_i32()).to_equal(code)
    expect(recovered.to_text()).to_equal(label)

describe "SemanticEventKind to_i32":
    it "FunctionEnter to_i32 returns 0":
        step("FunctionEnter to_i32 returns 0")
        val k = SemanticEventKind.FunctionEnter
        expect(k.to_i32()).to_equal(0)

    it "FunctionExit to_i32 returns 1":
        step("FunctionExit to_i32 returns 1")
        val k = SemanticEventKind.FunctionExit
        expect(k.to_i32()).to_equal(1)

    it "ObjectAlloc to_i32 returns 3":
        step("ObjectAlloc to_i32 returns 3")
        val k = SemanticEventKind.ObjectAlloc
        expect(k.to_i32()).to_equal(3)

    it "AsyncSpawn to_i32 returns 8":
        step("AsyncSpawn to_i32 returns 8")
        val k = SemanticEventKind.AsyncSpawn
        expect(k.to_i32()).to_equal(8)

describe "SemanticEventKind from_i32 roundtrip":
    it "from_i32(0) gives FunctionEnter":
        step("from_i32(0) gives FunctionEnter")
        val k = SemanticEventKind.from_i32(0)
        expect(k.to_i32()).to_equal(0)

    it "from_i32(11) gives AsyncComplete":
        step("from_i32(11) gives AsyncComplete")
        val k = SemanticEventKind.from_i32(11)
        expect(k.to_i32()).to_equal(11)

describe "SemanticEvent create":
    it "create sets kind field correctly":
        step("create sets kind field correctly")
        val ev = SemanticEvent.create(SemanticEventKind.VariableWrite)
        expect(ev.kind).to_equal(SemanticEventKind.VariableWrite.to_i32())

    it "create initialises seq to 0":
        step("create initialises seq to 0")
        val ev = SemanticEvent.create(SemanticEventKind.ObjectDrop)
        expect(ev.seq).to_equal(0)

    it "event_kind() roundtrips back to BorrowStart":
        step("event_kind() roundtrips back to BorrowStart")
        val ev = SemanticEvent.create(SemanticEventKind.BorrowStart)
        val k = ev.event_kind()
        expect(k.to_i32()).to_equal(6)

    it "SEMANTIC_EVENT_SIZE is 68":
        step("SEMANTIC_EVENT_SIZE is 68")
        expect(SEMANTIC_EVENT_SIZE).to_equal(68)

describe "Complete semantic event model contracts":
    it "preserves every event identifier and public name in both directions":
        step("Inspect all twelve production event kinds against their explicit identities")
        expect_semantic_kind(SemanticEventKind.FunctionEnter, 0, "FunctionEnter")
        expect_semantic_kind(SemanticEventKind.FunctionExit, 1, "FunctionExit")
        expect_semantic_kind(SemanticEventKind.VariableWrite, 2, "VariableWrite")
        expect_semantic_kind(SemanticEventKind.ObjectAlloc, 3, "ObjectAlloc")
        expect_semantic_kind(SemanticEventKind.ObjectDrop, 4, "ObjectDrop")
        expect_semantic_kind(SemanticEventKind.OwnershipTransfer, 5, "OwnershipTransfer")
        expect_semantic_kind(SemanticEventKind.BorrowStart, 6, "BorrowStart")
        expect_semantic_kind(SemanticEventKind.BorrowEnd, 7, "BorrowEnd")
        expect_semantic_kind(SemanticEventKind.AsyncSpawn, 8, "AsyncSpawn")
        expect_semantic_kind(SemanticEventKind.AsyncYield, 9, "AsyncYield")
        expect_semantic_kind(SemanticEventKind.AsyncResume, 10, "AsyncResume")
        expect_semantic_kind(SemanticEventKind.AsyncComplete, 11, "AsyncComplete")

    it "uses the existing FunctionEnter fallback for out-of-range identifiers":
        step("Decode identifiers below and above the defined event range")
        val negative = SemanticEventKind.from_i32(-1)
        val past_last = SemanticEventKind.from_i32(12)
        expect(negative.to_i32()).to_equal(0)
        expect(negative.to_text()).to_equal("FunctionEnter")
        expect(past_last.to_i32()).to_equal(0)
        expect(past_last.to_text()).to_equal("FunctionEnter")

    it "initializes every unused record field to zero without losing the kind":
        step("Create an async-resume event through the production constructor")
        val ev = SemanticEvent.create(SemanticEventKind.AsyncResume)
        expect(ev.kind).to_equal(10)
        expect(ev.event_kind().to_text()).to_equal("AsyncResume")

        step("Inspect sequence, location, identity and payload defaults")
        expect(ev.seq).to_equal(0)
        expect(ev.thread_id).to_equal(0)
        expect(ev.timestamp_ns).to_equal(0)
        expect(ev.source_file_id).to_equal(0)
        expect(ev.source_line).to_equal(0)
        expect(ev.source_column).to_equal(0)
        expect(ev.name_id).to_equal(0)
        expect(ev.object_id).to_equal(0)
        expect(ev.payload_a).to_equal(0)
        expect(ev.payload_b).to_equal(0)
```

</details>
