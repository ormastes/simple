# wire_codec_v1_spec

STATUS: NOT_RUN. 16 authored cases,0executed,0runtime passes.
Manual authored from current SSpec source; native docgen has not run.

Source: `test/01_unit/lib/common/contracts/mux/wire_codec_v1_spec.spl`.

Production typed codec and strict SDN/parser controls. Value fixtures are not providers, children or authenticated leases.

## Authored cases

1. round trips every command with exact fields and full u64 correlation
2. preserves maximum u64 and rejects signed overflow and noncanonical spelling
3. round trips binary NUL and high bytes and refuses noncanonical hex
4. preserves Unicode and escapes through actual SDN envelope bytes
5. rejects malformed UTF8 unknown variants wrong arity and dictionary bypasses
6. checks length framing without allocating an oversized body
7. preflights aggregate payload and capture hex expansion against frame budgets
8. round trips full connection state capabilities and lease terms without upgrading evidence
9. round trips all six typed query result shapes and rejects mismatched queries
10. round trips mutation disconnect and events with explicit receipts and revisions
11. preserves Partial and Unknown errors and refuses false Unsupported effects
12. rejects foreign owners duplicate IDs invalid geometry and out of order events
13. binds snapshot scope and visibility while permitting required ancestors
14. rejects dangling and inconsistent client context and restoration geometry
15. rejects a byte fitting response above the parser node budget before SDN allocation
16. matches actual strict parser node accounting for an admitted full response

## Visible steps

- Round trip all thirty typed command payloads
- Check exact unsigned decimal wire identity
- Preserve literal binary data without lossy text conversion
- Check UTF8 launch environment after strict decode
- Fail closed on malformed or invented wire shapes
- Reject zero and oversized advertised lengths
- Refuse impossible sizes before frame construction
- Preserve full observations and NotRun descriptors
- Bind each query reply to its declared operation
- Preserve effects and cleanup data without synthetic success
- Keep uncertainty in structured failures
- Validate observation graph and event cursors
- Reject unrelated and filtered objects in a scoped reply
- Check same owner reference membership and ancestry
- Apply identical sender and receiver node ceilings
- Compare preflight node count with production parser observation

## Admission and evidence

Use only an admitted current Phase3 compiler and matching runtime/full modern
SSpec runner with semantic --library-mode nogc-sync-mut and generic library roots.
Do not select a family by --source directory, use a seed, rebuild Phase2 for this
suite, or accept missing framework imports as a passing run. No exact executable
or invocation is admitted by this source checkpoint.

Retain producer/source/runtime hashes, actual argv, stdout/stderr, exit status,
case totals with failures/blocked/unrun, resource peaks and cleanup receipts.
Auth tokens and pane content are excluded from diagnostic errors and public reports.
Private expected fixture text is inspected only by assertions/owned artifacts.
All current cases remain NOT_RUN; source checks are not native test evidence.
