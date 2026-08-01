# Release beta bootstrap and verification postponed

Status: OPEN — implementation may be reviewed, but release qualification is not complete.

## Completed scope

Research, selected B/B requirements, architecture, detail design, executable specifications, release workflow hardening, readiness/evidence collectors, focused shell contracts, and the Stage-3 transient parser ownership repair are implemented in the release-beta lane.

## Postponed gates

- Fresh strict pure-Simple Stage 2 → Stage 3 → Stage 4 bootstrap with `SIMPLE_NO_STUB_FALLBACK=1`.
- Source-matched Stage-4 CLI sanity, SPipe execution, and fresh manual generation.
- Full `/verify` production-readiness audit and required runtime/MCP smoke checks.
- Final GitHub workflow evidence, tag, prerelease creation, and artifact publication.

Stage-2 or Stage-3 CLIs may run bounded diagnostics where supported. Their results are partial evidence only and must never be recorded as `STATUS: PASS`, release qualification, or a substitute for Stage 4.

## Resume conditions

1. No other bootstrap/native-build/Cargo owner is writing shared compiler authority.
2. `git rev-parse --is-bare-repository` remains `false` and source/runtime hashes are stable.
3. Run the one reserved strict bootstrap confirmation and retain timing/RSS logs.
4. If Stage 4 passes, generate the manual and run `/verify` once.
5. Release/tag/push artifacts only after verification reports `STATUS: PASS`.
