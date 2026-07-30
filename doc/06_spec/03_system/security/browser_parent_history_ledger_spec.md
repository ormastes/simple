# Capability-bound parent browser history

> The renderer proposes a complete bounded ledger inside nested `SBRF9`; the
> parent admits it only through the matching random outer `SBR2` capability and
> publishes the candidate with one atomic swap.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Status | Implemented static; execution held |
| Source | `test/03_system/security/browser_parent_history_ledger_spec.spl` |
| Requirements | REQ-WEB-BROWSER-009, 012, 014, 017, 021 |
| Protocol | Outer `SBR2`; nested `SBRHJ1`, `SBN2`, and `SBRF9` only |
| Updated | 2026-07-30 |

`make_history_process_fixture` creates the two-entry parent ledger, current
index, canonical origin, CSP-ready policy, Home URL, and title. The
`expect_history_public_state` checker asserts the parent document/current URL,
Back URL, Forward URL, entry count, and current index.

## Scenario

### should publish only one complete parent-authorized ledger

1. **Stage parent history authority**
   - Use one valid 128-bit-form fixture capability; production commands mint
     their capability with the accepted random SBR2 owner.
   - Encode the complete parent ledger and current index as `SBRHJ1` in `SBN2`.
   - Bind the navigation to outer `SBR2` and prove the joined snapshot carries
     the same capability.

2. **Accept one capability-bound history proposal**
   - Encode a same-origin `pushState` proposal with the complete three-entry
     candidate ledger.
   - Encode the real frame, bind it to outer `SBR2`, assert the nested payload
     is `SBRF9`, then decode and call the parent `_accept_decoded_frame`.
   - Assert the public current URL and Back/Forward projections after the
     parent performs its one atomic candidate swap.

3. **Reject hostile or stale history proposals**
   - Reject a proposal capability different from the admitted outer
     capability, a stale reply, sandbox CSP without scripts, a wrong frame URL,
     and a malformed 65-entry ledger.
   - Each rejection reaches the real SBR2 decode and parent frame-accept path;
     no helper commits a ledger directly.

4. **Preserve chrome across renderer failure**
   - Assert fail-close leaves the established parent ledger, index, current
     URL, Back/Forward projections, Home URL, and document title unchanged.
   - Explicit session close remains the owner of clearing parent state.

<details>
<summary>Executable SSpec flow</summary>

```simple
describe "Capability-bound parent browser history":
    # @manual: show
    # @capture(protocol)
    it "should publish only one complete parent-authorized ledger":
        step("Stage parent history authority")
        # SBRHJ1 snapshot -> SBN2 -> outer SBR2

        step("Accept one capability-bound history proposal")
        # proposal -> frame -> outer SBR2/nested SBRF9 -> decode -> accept

        step("Reject hostile or stale history proposals")
        # capability/reply/CSP/URL/overflow rejection matrix

        step("Preserve chrome across renderer failure")
        # make_history_process_fixture + expect_history_public_state
```

The complete executable helpers and assertions are in
`test/03_system/security/browser_parent_history_ledger_spec.spl`. Execution and
docgen remain held until a source-matched admitted pure-Simple full CLI is
available; no seed or bootstrap result can promote this manual.

</details>
