# WM browser event-routing proof validator

> **Runtime status: BLOCKED.** This manual mirrors the executable contract, but
> no current focused SSpec receipt was produced for this documentation update.
> The fixture assertions below are not live Electron/Chromium evidence.

Source: `test/03_system/check/wm_browser_event_routing_validator_spec.spl`.

Run: `SIMPLE_LIB=src bin/simple test test/03_system/check/wm_browser_event_routing_validator_spec.spl --mode=interpreter --clean --fail-fast`.

## Operator contract

The validator accepts only a regular, single-link proof JSON tied to the live
Electron Chromium event-routing surface and the regular producer
`tools/web-render-backend/wm_event_check.js`. It normalizes source-artifact,
runtime, event-sequence, count, timing, animation, payload, UI, and font-frame
rows. Any missing, forged, stale, aliased, malformed, fractional, unsafe, or
out-of-budget value fails closed; `pass=true` alone never passes.

Required live proof includes the canonical host-pointer/focus/move/title/maximize/
text/pointer-down/pointer-up sequence, matching aggregate counts, positive
`performance.now()` and input-to-paint measurements, animation evidence, real
JSON booleans and numbers, DOM payload/UI readback, Electron/Chrome identity,
and a correlated Simple font-composition receipt at the configured path.

## Primary changed flow

1. `step("Create a valid alternate receipt beside the configured receipt")`
   creates a second byte-valid receipt without changing the configured path.
2. `step("Reject the proof when its receipt path differs from the configured path")`
   requires validator exit 1 and the normalized composition-artifact-invalid
   reason.

<details>
<summary>Executable SSpec focus</summary>

```simple
it "rejects a valid alternate receipt outside the configured proof path":
    step("Create a valid alternate receipt beside the configured receipt")
    val root = "build/test-wm-browser-event-validator-receipt-path"
    val mutation = "const alt=path.join(dir,\"alternate.env\");fs.copyFileSync(srp,alt);p.simple_composition_receipt_path=alt"
    val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
        _fixture_command(root + "/proof.json", mutation) +
        " && SIMPLE_WEB_FONT_COMPOSITION_RECEIPT=" + root + "/simple-composition.env" +
        " node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/proof.json > " + root + "/evidence.env"
    val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
    step("Reject the proof when its receipt path differs from the configured path")
    expect(code).to_equal(1)
    val evidence = file_read(root + "/evidence.env")
    expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
    expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-simple-composition-artifact-invalid")
```

</details>

## Scenarios and expected outcome

| Scenario | Expected outcome |
|---|---|
| accepts complete event timing animation payload and UI proof | PASS; emits normalized `wm_browser_event_routing_*` evidence. |
| rejects a composition receipt from a different run | FAIL: composition artifact invalid. |
| rejects a valid alternate receipt outside the configured proof path | FAIL: composition artifact invalid. |
| rejects a font frame receipt that is not correlated with the event stream | FAIL: font-frame correlation missing. |
| rejects pass true proof when required event counts are missing | FAIL: event-routing contract missing. |
| rejects pass true proof without the live event surface identity | FAIL: surface identity missing. |
| rejects pass true proof without the live event-check source marker | FAIL: proof source missing. |
| rejects pass true proof when the live event-check source artifact is missing | FAIL: proof source missing. |
| rejects substituted live event-check source artifacts | FAIL: hardlink, non-regular, or marker-missing producer. |
| rejects pass true proof without live Electron Chromium runtime evidence | FAIL: browser runtime missing. |
| rejects pass true proof when the frame sequence is missing or reordered | FAIL: event-routing contract missing. |
| rejects pass true proof when Chromium timing or animation is malformed | FAIL: event-routing contract missing. |
| rejects pass true proof when Chromium timing does not advance or exceeds budget | FAIL: event-routing contract missing. |
| rejects pass true proof when input-to-paint latency is missing or malformed | FAIL: event-routing contract missing. |
| rejects string booleans for readiness timing and animation proof | FAIL: event-routing contract missing. |
| rejects stringified numeric event timing animation UI and payload proof | FAIL: event-routing contract missing. |
| rejects pass true proof when payload details do not match dispatched DOM events | FAIL: event-routing contract missing. |
| rejects pass true proof when UI readback details are missing | FAIL: event-routing contract missing. |
| rejects pass true proof when event counts or move coordinates are fractional | FAIL: event-routing contract missing. |
| rejects unsafe exponential integer event animation UI and payload proof without crashing | FAIL: event-routing contract missing. |
| rejects symlinked WM event-routing proof JSON before reading event evidence | FAIL: proof symlink rejected. |
| rejects hardlinked WM event-routing proof JSON before reading event evidence | FAIL: proof hardlink rejected. |
| keeps the live shell wrapper wired to the validator result | PASS only when wrapper preserves validator status/reason. |
| keeps wrapper diagnostics on early dependency failures | PASS only when dependency failure retains all diagnostic rows. |

## Evidence and admission

The acceptance scenario retains normalized validator output, including proof
symlink/hardlink checks, producer source status and both source sizes, runtime
identity, counts, timing, animation, event sequence, payload/UI fields, and
font-frame/composition correlation. A live admission is BLOCKED until the
focused SSpec produces that receipt with its passing scenario and all rejection
scenarios observed as expected.
