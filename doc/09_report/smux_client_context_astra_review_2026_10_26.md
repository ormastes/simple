# Smux shared client context: independent source review

Baseline: `1aaec595d0f49a0e255e27a6ebc5a7720f8cfa80`.
Initial v1 status: **WARN / NOT_RUN; correction pending at initial review**.
Seven unit and two persistent-owner API cases are authored; zero were executed.
No compiler, native/helper process, build, test, staging or commit was performed.

## Review scope and evidence

The ten inputs below are the frozen v1 manifest, not a claim that all surrounding
Smux code is reviewed. Reviewed the three appended attachment fields, pure
projection/lookup/ordered replacement, managed/unmanaged attachment transforms,
configuration equality, root-owned `_publish` reconciliation, and matching tests
and manuals. Bounded reads of lease admission/heartbeat, existing exact client
slot helpers, pane visibility and API focus/attachment call sites support this
review. Concurrent RenameWindow correction and configured-launch implementation
are excluded. The API hash also contains the separately owned L2 cleanup-commit
condition; this review does not qualify the full configured-launch dynamic gate.

The revised plan's root decision supersedes its historical private-selection
proposal: one current window per session and active pane per window. The primary
[tmux guide, immutable revision cf5a82fad1144475335e078548b6ed18fc37422c](https://github.com/tmux/tmux/wiki/Getting-Started/cf5a82fad1144475335e078548b6ed18fc37422c)
supports that shared focus model. Per-client viewport and lease generation remain
separate. No private selection controller or new registry is introduced.

## Finding P2-L1-01: successful unmanaged attach returns noncanonical context

In the frozen v1 API, `smux_attach` publishes `update.state` through the new
reconciliation hook, then returns `MuxClientAttachment.create(...)`. The factory
uses default empty current_window/current_pane, so an attached result disagrees
with the stored/listed record whenever the session has shared active focus.
This is a public result inconsistency, even though managed attach returns a token
and the new system scenarios originally checked only stored managed records.

Requested correction: return the actual published attachment by exact client ID,
and assert returned-versus-stored identity, generation, viewport and context
through the real API. Root reported replacing the return with
`_svc.get_client(_svc.find_client_idx(client_id))` without another publication.
That source correction was observed after the initial review; the API no longer
matches its historical v1 pin. The other nine v1 inputs still matched. Closure
requires the author's frozen v2 assertion/manifest; no final source-clear status
is assigned yet.

## Remaining source observations

- Defaults preserve dummy/refused/unmanaged generation zero; direct live managed
  constructors receive actual admitted generation. Existing service add/remove
  and rebuild helpers copy whole attachment records. Managed resize retains
  generation and slot order while heartbeat updates only lease deadline.
- `smux_lease_admit` replaces same client label with a new monotonic generation
  and target session; projection derives that session's canonical focus.
  Unmanaged attach refuses labels present in managed leases. Wrong/stale positive
  generations and zero unmanaged identity refuse pure lookup. Lookup is not
  token authentication and cannot be used alone as an authorized endpoint.
- Reconciliation projects exactly one active window and one focused visible pane;
  ambiguous, hidden, missing, detached and inconsistent zoom context becomes
  empty without changing focus. No arbitrary fallback target is selected.
- `_publish` computes canonical final state before comparison/publication; the
  comparator includes generation/window/pane. Deadline-only renewal and an
  already canonical reconciliation remain no-ops. Ordered replacement is bounded
  by existing four-client/eight-window/eight-pane owner capacities.
- Authenticated focus, expired-token/owner-incarnation checks, closing/quarantine
  permission and interactive private-cursor migration remain explicit owner
  obligations. Pure projections do not confer input authority. The API's
  existing guarded mutation paths remain responsible for checked state changes.

## Test boundary and gaps

The seven unit cases use production helpers and meaningful values; the two
system cases read actual stored API state rather than manually reconciling it.
They cover shared two-client focus, other-session isolation, hide/window-removal
repair, managed reattach and no-op renewal, with owned session cleanup before
assertion. They spawn no child and establish no terminal input, viewport,
wire authentication or native cleanup evidence. Manuals preserve this boundary.
Cross-session managed reattach and unmanaged-downgrade refusal were source-traced
but not explicitly asserted in these seven cases. Real child input, closing
failure/quarantine, crash/expiry capacity recovery, token/owner-incarnation
validation and full N2 remain required in later connected qualification.
Source authoring is not SSpec execution or an application/backend pass.

## Historical v1 pins

Manifest: `build/review/smux-client-context-source-v1.sdn`.
Plan: `build/review/coremux-client-context-plan-v1.md`, SHA256
`be0b3b963ecc8d6f1655d186181c927c98a70e892ddcf0a62a7aac49ff0e168c`.

| Input | v1 SHA256 |
|---|---|
| `src/os/apps/smux/contract.spl` | `9e32e3b35f2d46eb8ede9c8a300c248f3e26f0b9548298a6acc01428739f49d6` |
| `src/os/apps/smux/client_context_service.spl` | `ded09aeb02898c2f5aed0a4cc19775f4aee2400996443c2925ad85697e99c418` |
| `src/os/apps/smux/client_attachment_service.spl` | `bb7b5a4c9fa31b492d45110649559521d24245a6809d10f86d12b7b85e48f8a8` |
| `src/os/apps/smux/service_revision.spl` | `2f49bcb24426b2c9ef84895f15406f529c109629fcf4b5b03e6aa234c858da85` |
| `src/os/apps/smux/api.spl` | `dbed2128a1c2b031b5da8dcd071c8cd578afe2a6329353597720980081f80aaa` |
| `test/01_unit/tools/smux_client_context_spec.spl` | `f4570106584f5a226c3f03485e10fc0631c984e8991050cb13d51f7af15a4e70` |
| `test/03_system/tools/smux_client_context_spec.spl` | `7cf17c88f1d09928519f8818de106d0acc048b0b5246d0c32ca313960e8ead5a` |
| `doc/06_spec/01_unit/tools/smux_client_context_spec.md` | `408edab36ac21be83bcc22b627b1a9fe95cb13892ff2e54681e37959384b9512` |
| `doc/06_spec/03_system/tools/smux_client_context_spec.md` | `84792004a2955c644cd0c0fc2bc9cb212021fbd0cd58de010f278cfb6ee6f7ec` |
| `doc/09_report/smux_client_context_source_2026_10_26.md` | `abb45a3f1d5075ee288f10b67c93abddd12e768abf50123b9b5a574dbabd9d8d` |


## Focused v2 disposition

**WARN / NOT_RUN: P2-L1-01 SOURCE-CLOSED.** No remaining concrete P0/P1/P2
finding in this reviewed correction delta. Eight unit and three persistent-owner
API cases are authored; all eleven remain unexecuted. This supersedes the initial
pending disposition above while preserving the original finding and v1 pins.

The actual `smux_attach` success return now reads the canonical published record
by exact client ID. Publication still occurs once, and the API remains 800 lines.
The new real-API scenario covers initial unmanaged attach and viewport update,
requires expected nonempty window/pane context, checks stored/listed context and
generation, unique listed client identity and unmanaged generation zero, and
cleans its owned session before assertions. It does not call projection to mask
a missing API connection and would reject the original empty-context return.

The extra unit case invokes production managed/unmanaged transforms to move one
client from s1 to s2, checks the new actual generation and destination context,
old-recipient clearing, old-session/token refusal and unmanaged downgrade refusal
in both sessions. This closes the previously noted source-coverage omissions;
it does not establish native authorization or crash/expiry behavior. Both manuals
reflect the new counts and preserve the no-child/no-native-evidence limitation.

All ten v2 hashes matched during focused rereview. No reviewer production edits,
compiler/tests/builds or runtime launches occurred. L2 configured-launch gate,
RenameWindow cycle2, interactive integration, actual child/cleanup/N2 and full
provider admission remain outside this source closure. Existing failures and
NOT_RUN criteria are not converted into passing evidence.

V2 manifest: `build/review/smux-client-context-source-v2.sdn`, SHA256
`276f3545d14e5b02504a4b8f305407468d02f8aa5b8b1149da8a4d9c6e15d757`.

| Input | v2 SHA256 |
|---|---|
| `src/os/apps/smux/contract.spl` | `9e32e3b35f2d46eb8ede9c8a300c248f3e26f0b9548298a6acc01428739f49d6` |
| `src/os/apps/smux/client_context_service.spl` | `ded09aeb02898c2f5aed0a4cc19775f4aee2400996443c2925ad85697e99c418` |
| `src/os/apps/smux/client_attachment_service.spl` | `bb7b5a4c9fa31b492d45110649559521d24245a6809d10f86d12b7b85e48f8a8` |
| `src/os/apps/smux/service_revision.spl` | `2f49bcb24426b2c9ef84895f15406f529c109629fcf4b5b03e6aa234c858da85` |
| `src/os/apps/smux/api.spl` | `1786df13fc5c08a7865f3accda1d6ed37b2760adb35d4d27d7b0d963e8b84107` |
| `test/01_unit/tools/smux_client_context_spec.spl` | `cc096ad9d884b76b257cdcd588253da9e6109f09a35db7af46f88a818ff02696` |
| `test/03_system/tools/smux_client_context_spec.spl` | `ee6c740cd45f80bb82a5ac8951b9461ac1d7a88668862a8baafadb6e218e0ec8` |
| `doc/06_spec/01_unit/tools/smux_client_context_spec.md` | `d47424211a866d95338aa07304257c2119cd9f27323d665ac7a3f82dc9a9ab91` |
| `doc/06_spec/03_system/tools/smux_client_context_spec.md` | `bef1a29a0db8dad37d716f4f5ef7f4015c865f5efc71c7826389bec38d049e25` |
| `doc/09_report/smux_client_context_source_2026_10_26.md` | `75003f4e1cf1efbc0c8cfba9fbb629c551d8c40ce8b37b20322c9b38841db498` |
