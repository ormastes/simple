# Browser renderer command capability

> SBR2 renderer authority is created only by the hosted parent, becomes
> admissible only after a complete host-wire write, is echoed unchanged by the
> worker, and is consumed before broker or frame authority.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

## Scope and evidence boundary

The executable scenario is
`test/03_system/security/browser_renderer_command_capability_spec.spl`.
It covers REQ-WEB-BROWSER-014, REQ-WEB-BROWSER-021,
and NFR-WEB-BROWSER-010. It makes no fuzz/corpus claim.

This checked-in manual records SBR2 codec oracles, the real
`HostedBrowserRendererProcess` cancellation/admission methods, and a
deterministic 10,000-cycle counter model. It proves exact issue/consume counters
and zero retained model-token bytes. It does **not** claim runtime latency,
RSS, subprocess execution, Draw IR pixels, fuzz/corpus coverage, or a passing
pure-Simple runner. Those promotion claims remain gated on the admitted current
full pure-Simple CLI.

## Scenario

### should bind one-use SBR2 authority to each complete host wire

1. **Admit the trusted capability owner**
   - `setup_trusted_capability_owner_fixture`
   - `check_trusted_capability_owner_admitted`
   - Accept exactly 32 lowercase nonzero hexadecimal bytes.
   - Reject empty, uppercase, all-zero, legacy SBR1 input, and legacy nested
     network/fetch/frame payload versions; production uses SBRN2/SBRQ5/SBRF9.

2. **Issue one fresh command token**
   - `check_fresh_command_token_issued`
   - Keep a split write inadmissible through byte 31.
   - Admit the tuple only after the final byte completes the SBR2 wire.
   - Bind generation, root command request, immediate wire, and token.

3. **Reject an unissued command token**
   - `check_unissued_command_token_rejected`
   - Reject predicted, wrong-root, wrong-wire, wrong-generation, and replayed
     tuples before granting authority.
   - Accept one conforming echo exactly once.
   - Seed a partially written old command, call real
     `HostedBrowserRendererProcess.begin_stop`, assert `stop_after_write`,
     complete the old write, invoke `_begin_stop_after_write`, and leave the
     new Stop wire partial. Also drive `begin_navigate` replacing a fully
     written command. A queued old reply is classified from its bounded nested
     `reply_to` as stale before capability admission, leaves the new
     staged/issued tuple untouched, keeps the process active, and preserves the
     admitted image. A future reply rejects; only after the new Stop offset
     reaches its full length does the test issue its tuple, and the current
     reply alone consumes authority.

4. **Retire all capability material**
   - `check_all_capability_material_retired`
   - Stop/cancel retirement preserves the last admitted image witness.
   - Terminal retirement clears image state.
   - The 10,000-cycle deterministic model ends with 10,000 issues,
     10,000 consumes, zero failures, and zero staged/issued token bytes.

<details>
<summary>Executable SSpec</summary>

The complete runnable source, including every setup/checker implementation and
all built-in matcher assertions, is retained at
`test/03_system/security/browser_renderer_command_capability_spec.spl`.

```simple
val fixture = setup_trusted_capability_owner_fixture()
step("Admit the trusted capability owner")
check_trusted_capability_owner_admitted(fixture)
step("Issue one fresh command token")
check_fresh_command_token_issued(fixture)
step("Reject an unissued command token")
check_unissued_command_token_rejected(fixture)
step("Retire all capability material")
check_all_capability_material_retired(fixture)
```

</details>
