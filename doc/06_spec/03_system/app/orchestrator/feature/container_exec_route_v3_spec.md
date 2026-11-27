# Actual common finite exec route

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 exact parent/admission association; HOST-02 canonical owner retention.
Spec: `test/03_system/app/orchestrator/feature/container_exec_route_v3_spec.spl`.

Setup: construct actual neutral exec, original intent, admission and canonical
installed-carrier shapes around existing real scripted Linux/Windows owners.
The deadline is explicitly historical (1000 ms); no future grant is invented.
Actual common negative calls fail before any control probe/exec effect. Pure
neutral diagnostic projection uses raw observed-shaped fields only, not native
success. No Host signature/lease, native connection, WAL or leaf session is mocked.

| Exact step | Procedure / checks |
|---|---|
| refuses unsupported action through the actual common route before effects | Actual begin rejects unsupported destroy action with no session/probe cleanup/birth/inspection/retirement and zero executor calls. |
| refuses scripted begin before actual control probe or exec native creation | Actual create/start routes reject scripted owners before native probe, retaining common scope and zero commands. |
| uses pure binding for expired inspect but still refuses scripted native observation | Actual inspect performs pure binding despite historical expiry, then rejects scripted native observation. No fresh grant or running-parent proof is fabricated. |
| refuses original parent baseline and installation artifact mismatches before effects | Refuse original parent-plan, installed artifact and parent baseline mismatch before effects. |
| explicitly refuses Windows effect and inspect without a platform fallback | Actual Windows owner explicitly refuses both effect and inspect without fallback, preserving owner. |
| projects diagnostic running and exit data without PID removal or completion authority | Project diagnostic running/-1 and exited/23 fields, exact request digest and parent identity. No PID/remove/reap/completion field or authority is exposed. |
| refuses wrong full exec parent identities and impossible exit diagnostic bounds | Refuse short/equal parent exec ID, mismatched parent CID and impossible observed exit bound. |

Actual positive source route (NOT executed): begin validates common cached Linux
platform/baseline, full original parent plan, semantic project, exact parent runtime,
installed artifact and structural admission. It checks actual admission clock,
obtains actual common control probe itself, preserves returned owner/probe cleanup
on every failure, checks distinct control pin and fresh expiry, then calls actual
adapter.exec_begin_v3. Probe budget is min(request control window, remaining launch
window, 30000 ms); original request bytes are not rewritten. Begin includes synchronous
bounded capture and is NOT hard-wall responsive. Inspect uses structural binding
without live expiry/running-parent precondition and calls actual adapter known-birth
inspect with no caller native exec ID. Host still supplies verified installation/
admission/BEGIN; these common shapes do not authenticate the caller.

Session retains immutable context and EXACT returned Linux leaf. All WAL and IO
belong to that leaf. Poll validates 1–25 ms plus small cached backend/scope/baseline,
then calls leaf.step only; it never hashes/projects full multi-MiB request or invokes
fresh CLI per turn. Native waits are bounded, but WAL/fsync/filesystem work may
block: no whole-host nonblocking guarantee. Error/stale-view returns retain the
returned leaf; common never generic-closes an earlier connection copy. Cleanup
ignores parent readiness/scope drift and calls ONLY leaf.cleanup, no sends/kill.
It exposes no birth/inspection. cleanup_complete is copied ONLY from actual leaf
retirement fact (all connection, WAL/lifetime lock and durability owners gone,
requested cleanup and not stale), never inferred from phase or error absence.
Some session may remain for provenance. Retirement can preserve a failed error;
it does not mean exec ended, action succeeded or capacity was released.

Provider interfaces and retirement facts match the reviewed immutable checkpoint
`d41bf8b2ace96ace60a2620925a25b11cebbf153`. No native owner seam is fabricated to
test poll/cleanup states. Actual provider and Host installation/carrier dependencies
are referenced, not copied (carrier `feccc4e7820`).
Root integration, native lifecycle/unknown-create/no-auto-retry and full platform
qualification remain required. Builds/tests/native execution were prohibited.
