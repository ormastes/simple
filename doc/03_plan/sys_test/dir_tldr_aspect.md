# dir_tldr_aspect: System Test Plan (DRAFT)

Executable skeleton: `test/03_system/app/compiler/feature/dir_tldr_aspect_spec.spl`. Every case
is currently a fail-fast placeholder and turns real during implementation. Requirement IDs
are provisional and map to option groups until the user selects.

| Case | REQ (provisional) | Scenario | Assertion |
|---|---|---|---|
| T1 | A/H1 | compile a dir with no `__init__.tld` | gate builds it before the first member compile; compile admitted |
| T2 | H1 | dir TLDR stale (member added) | gate rejects, rebuilds; the stale artifact is never used |
| T3 | H4 | corrupt dir TLDR bytes | digest mismatch → quarantine + rebuild |
| T4 | C | edit a private body of one file | dir TLDR output digest unchanged → children not re-weaved |
| T5 | D | 3 dirs, 80 jobs | split into chunks; first `.o` ≤10 s |
| T6 | D | 200 dirs | one job per dir; TLDR loaded once per job |
| T7 | E/F | LogAspect pointcut via OOP predicate | woven call present at the expected placement |
| T8 | G | same plugin config in dirs a/ and b/ | one instance; distinct per-dir match results |
| T9 | H2 | two clean builds | identical woven object digests |
| T10 | H3 | concurrent producers for the same dir | single flight: one production, readers pinned |
| T11 | H5 | plugin digest not in allowlist | load refused, compile fails closed with a diagnostic |
| T12 | N7 | change an aspect pointcut | only the affected dir union is re-weaved |

Runner: Haiku lane, `bin/simple test <spec> --mode=interpreter` on the self-hosted binary, with no P3-RUN interference.
