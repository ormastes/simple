# WM browser event-routing proof validator

> **Runtime status: BLOCKED.** The one bounded focused interpreter run stopped
> after two scenarios because Simple interpreted a shell cleanup expression as
> language interpolation. The cleanup expression was then rewritten without
> named shell-variable expansion and was not rerun under the bounded-test guard.
> Earlier direct validator checks passed for path, hash, metadata, and
> process-version rejection. These fixtures are not live Electron/Chromium
> evidence.

Source: `test/03_system/check/wm_browser_event_routing_validator_spec.spl`.

Run: `SIMPLE_LIB=src bin/simple test test/03_system/check/wm_browser_event_routing_validator_spec.spl --mode=interpreter --clean --fail-fast`.

## Operator contract

The validator accepts only a regular, single-link proof JSON tied to the live
Electron Chromium event-routing surface and the regular producer
`tools/web-render-backend/wm_event_check.js`. It normalizes source-artifact,
runtime, event-sequence, count, timing, animation, payload, UI, and font-frame
rows. Any missing, forged, stale, aliased, malformed, fractional, unsafe, or
out-of-budget value fails closed; `pass=true` alone never passes.
Electron runtime identity is physical evidence, not a producer source marker:
the proof must retain the exact canonical repo-local `node_modules/electron/cli.js`,
platform executable, source manifest and lock, and installed package paths with
their current SHA-256 values. The source manifest dependency, lock root
dependency, nested lock package, installed package, and launched process must
all report exactly Electron `42.5.0`. The launched Electron process separately
derives `fs.realpathSync(process.execPath)` and hashes those executable bytes;
both self-observed values must exactly equal the wrapper-provided canonical
executable identity and the validator's current local executable. This evidence
path supports macOS and Linux only. Windows and other platforms fail closed
because the strict resolver requires the Unix `.bin/electron` symlink contract.

Executable fixtures are created only under each test's isolated build root.
`WM_EVENT_VALIDATOR_ROOT` selects that fixture for standalone validator tests,
and a validated trap removes every fixture root when the scenario shell exits.
The production evidence wrapper rejects this environment variable.

Required live proof includes the canonical host-pointer/focus/move/title/maximize/
text/pointer-down/pointer-up sequence, matching aggregate counts, positive
`performance.now()` and input-to-paint measurements, animation evidence, real
JSON booleans and numbers, DOM payload/UI readback, Electron/Chrome identity,
and a correlated Simple font-composition receipt at the configured path. It
also requires the retained canonical Aetheric production envelope and generated
HTML hash, exact theme snapshot fingerprints, mirrored computed glass witnesses,
and explicit non-synthetic/non-compatibility flags.

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
| rejects swapped Electron paths hashes metadata and process identity | FAIL: exact physical Electron identity mismatch, including self-observed process executable path/hash. |
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
identity with canonical Electron artifact paths, hashes, and exact `42.5.0`
metadata, counts, timing, animation, event sequence, payload/UI fields, and
font-frame/composition correlation. A live admission is BLOCKED until the
focused SSpec completes all scenarios under a runtime that supports its existing
matcher surface.
