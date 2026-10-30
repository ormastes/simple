# Configured launch API — independent Astra source review

Baseline: `4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`.
Status: **WARN / NOT_RUN; focused source review CLOSED with no remaining scoped P0/P1/P2.**
No compiler, test, native child, helper or server was executed by this reviewer.

## Production review

No concrete scoped P0/P1/P2 finding. Compared the working API diff directly with
its baseline and read the new explicit-state service query owner plus the
already-reviewed configured launch composition contract.

Six existing queries moved mechanically: sessions, clients, windows, active
window, panes and focused pane. Array order, filtering, first-match behavior,
public signatures and error strings remain unchanged. Active-window lookup
calls the explicit-state window list instead of re-entering the global API.
There are no globals, host calls or publication effects in service_queries.

The new API forwards the existing Sosix PtyLaunchV1 without reconstructing shell
text or dropping argv/cwd/environment. Revision preflight precedes the helper;
closing and exact session/window/pane admission precede PTY open/spawn there.
A failed launch retaining an actual fd sets pane closing intent only when the
returned state commits that fd. The API publishes once, preserving canonical
client reconciliation and native identity revision. An open failure reporting
provider-global quarantine with commit=false does not manufacture a pane cleanup
token. That global cleanup debt is still subject to existing owner-stop gates.

The API remains the only service registry. These changes do not register a full
CoreMux provider, implement a listener, or certify configured-launch capability
from symbol existence. The typed adapter/common validation and selected provider
probe remain separate admission obligations.

## Initial production pins

| Path | SHA256 | Lines |
|---|---|---:|
| src/os/apps/smux/api.spl | c7223400a920e0e98084668edf063a4f3236c1d49c99e59f8f15cda5691e9f78 | 783 |
| src/os/apps/smux/service_queries.spl | 280979f064cb82f2cb1b419c01d8a26966c11ea5dac2ee6950b7f1cb43ed4a3a | 51 |
| doc/05_design/smux_api_owner_extraction_2026-10-25.md | ab1bd8224651749abbec4c9e16236cf40a9ffa6e22ee75b18838643086811446 | 110 |

## Pending review boundary

The new real-child API scenario is still owned by another author and was not
reviewed while moving. Final freeze verification and that precise test/manual
delta will be appended before this report is marked closed. Prior helper-level
native scenarios and source-authored counts are not passing runtime evidence.
## Final focused v3 review, 2026-10-26

Initial production findings above remain unchanged. Root identified a test-only
v2 cleanup gap: accepting a forbidden overwrite could lose the first native fd
from the service registry, leaving session cleanup able to close only the second
child. That finding is closed in the v3 source correction.

The public API scenario retains the first token only after matching the API's
positive returned PID, exact pane/session/window ancestry and nonnegative i32
bounds. A separately returned second PID must satisfy the same checks; duplicate
tokens are not added twice. The retained list contains cleanup authority only,
not a copied service registry. No unbound or foreign observed token is closed.

Both first and distinct second captured tokens are closed after the public API
cleanup, before any assertions. The loop retains failed tokens, has 200 rounds
and 25ms retry delays, and reports unresolved handles plus known PIDs. Original
API cleanup success is asserted independently: later fallback cleanup cannot
mask failure of the API lifecycle contract. PID absence, global pending count,
exact child identity/incarnation and output observations remain separate checks.
Fixture absence/admission failure still reaches owned cleanup and then fails;
there is no passing unavailable-provider branch.

The third case tests actual public create/list/configured-launch, duplicate
refusal, leased attach/detach, capture and checked session kill. Source-observed
PID/handle/incarnation bindings and child-computed output support its intended
oracle; these observations have not been executed. The documented exclusive
provider/no-intervening-open and idempotent selected-provider close conditions
remain qualification prerequisites. Native calls can still require external
wall-time/Job containment; token cleanup does not prove unknown foreign effects
or descendant quiescence. PID reuse remains an observation limit.

Only the new scenario and changed manual/source report were reviewed in this
final pass; unchanged owner/helper/unit/fixture implementations were not rescanned.
All ten manifest pins were independently matched, including the three unchanged
production/design pins already reviewed above. Nine pure and three native cases
remain authored, zero executed; the child fixture is NOT_BUILT. No native admission,
SSpec PASS, full CoreMux capability admission or N2 completion is claimed.

Final freeze: `build/review/smux-configured-launch-source-v3.sdn`
SHA256 `27f30eb04be1a8096e11b2ce28033a26498eeb89d31fa9c99738347051a3e055`.
V2 remains historical at SHA256
`e92a3e0c050e97e8d0815c59ddacc94af646c3ee9797abb7f996a2c9fec5ea50`.

| Final pinned path | SHA256 |
|---|---|
| src/os/apps/smux/pane_configured_launch_service.spl | 74130fe5c96303f5aa84af8f9cfccb24675aba1776f084fc5960c96750a8c067 |
| test/01_unit/os/apps/smux/configured_launch_admission_spec.spl | ac97c67c3408573ddedc9030bf0a5c1efad2b28c5a0de20e35a72f6260d7fb85 |
| test/03_system/tools/smux_configured_launch_spec.spl | 1274a0a86173dd110aaccee5bc4661170fd25dfab4d514efa77f089af89568e5 |
| test/fixtures/coremux/configured_launch_child.spl | c22fd484cab1b235dfaa9454522eef50bf9742786eedd953d5d114e30d0f0f2d |
| doc/06_spec/01_unit/os/apps/smux/configured_launch_admission_spec.md | a292da4902d1a5e6fcf8278be6c639d5232baf23d397e682efb593bd27d8707c |
| doc/06_spec/03_system/tools/smux_configured_launch_spec.md | fe0d70ca3bb1c033de2f0b79da123df2f5b5e14ee2581758ade47e7bcd14c571 |
| doc/09_report/smux_configured_launch_source_2026_10_26.md | 8cce09db098d31011fb76630d2c28943f477674a9ac944d3bfb0e490c652cad8 |
| src/os/apps/smux/api.spl | c7223400a920e0e98084668edf063a4f3236c1d49c99e59f8f15cda5691e9f78 |
| src/os/apps/smux/service_queries.spl | 280979f064cb82f2cb1b419c01d8a26966c11ea5dac2ee6950b7f1cb43ed4a3a |
| doc/05_design/smux_api_owner_extraction_2026-10-25.md | ab1bd8224651749abbec4c9e16236cf40a9ffa6e22ee75b18838643086811446 |
