# Stage 2 HIR archive authority handoff failures

Status: FIX LANDED, FULL QUALIFICATION PENDING. No Stage 3/4 continuation,
local deployment, release, or SimpleOS build is authorized by this evidence.

## Terminal evidence

The Linux x86_64 Cranelift full-bootstrap lane used one worker, a 5,859,375 KiB
process-tree cap, and the isolated output
`.simple/storage/build/bootstrap-combined-20261016`. The first admitted Stage 2
compiler reached both full-CLI and test-runner HIR construction and rejected a
valid alias because the schedule compared the alias path with the canonical
surface path. The corrected schedule next identified an empty retained authored
path. Phase 1 now freezes `source_file_authored_path`, whose existing contract
falls back to the canonical path for programmatic and closure-alias sources.

The third and final permitted verification cycle rebuilt 1,346 modules, passed
candidate sanity and admission, and advanced both tool builds beyond schedule
capture. Both then stopped at `HIR journal selected managed authority differs`.
The journal was recomputing a digest by traversing a nested provider aggregate
transported across the complete phase-2 build. Journal creation already
recaptures and fully revalidates the live provider, checks the transported
selection digest and producer header against that recapture, and stores only
the recaptured value. Commit `5e1f8f13c86` removes the redundant traversal;
the fixture proves that nested transport state is ignored while a changed
scalar selection digest is rejected.

Related landed fixes on this branch:

- `9a71503522a`: retry only snapshot-index drift once through cold/warm SCV prime.
- `cd6af8b4dda`: identify the exact frozen schedule owner invariant.
- `3af60658a35`: retain the authored-path fallback in the phase-1 owner.
- `5e1f8f13c86`: recapture journal managed-runtime authority.

The branch is linearly rebased onto `origin/release_phase3` commit
`045087662cc`. The post-rebase SCV prime selftest passes all 25 cases; shell,
Perl syntax, and diff whitespace checks pass. The journal repair has not had a
fourth full-bootstrap run because the repository mandates a three-cycle session
cap. A fresh scoped session must rebuild Stage 2, require PASS for the full CLI,
test runner and all three mandatory suites, then consume the managed receipt for
Stage 3/4. Only a verified Stage 4 deployment may feed the prepared RISC-V, ARM,
and x86 SimpleOS lanes.
