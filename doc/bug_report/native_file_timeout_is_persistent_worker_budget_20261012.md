# Native file timeout actually limits the persistent worker

Status: confirmed configuration/documentation mismatch; no timer implementation change.

Bootstrap attempt 12 failed without admission. Its native HIR worker claimed
868 sources and published 867 terminal records before a wait timeout. The
unfinished claim was `src/compiler/70.backend/backend/gpu_backend_metadata.spl`.
This does not establish a defect or hang in that source: the deadline covered
the worker's accumulated work, not that claim's duration.

## Reproduction and ownership

- Producer SHA256: `1d18beed32d7156d9dc0ed2025ed6da77af289778f97632b8f57e07e5a7137b8`.
- Producer source: `0e0287094ba9a7f415513fe26b988e06228a62c5`.
- Attempt 12 input source: `142996e86e334bc3ac437003443f48968771082a`.
- The actual command transcript rows 76–77 contain `--timeout 1800`.
- The native log ends with owner `0/1@0`, status `BLOCKED`, exit `-2`,
  claimed `868`, sealed `-1`, finished `false`.
- The enclosing native RSS receipt records exit 1 and quiescence; its peak
  was 6,498,900 KiB, below the 12,582,912 KiB cap. This was not an RSS refusal.

The following line references are to the producer source above:

1. `scripts/bootstrap/bootstrap-from-scratch.sh:3883–3901` calls
   `SIMPLE_NATIVE_FILE_TIMEOUT` a per-file timeout but forwards it as `--timeout`.
2. `src/app/cli/native_build_main.spl:248–266` converts that value to
   milliseconds. Its help at line 225 correctly calls it a worker timeout;
   the comment at line 250 incorrectly also claims a per-file worker budget.
3. The caller at line 1142 passes it to `run_hir_shards`. Line 835 waits for
   the persistent shard process using that entire budget. It does not reset
   the wait on each claim or completed file.
4. `src/runtime/runtime_process.c:3088–3108` returns `-2` when Windows
   `WaitForSingleObject` times out; the child is still running. The caller
   at `native_build_main.spl:839–842` then kills and reaps it.
5. `src/app/io/_CliCompile/compile_targets.spl:1069–1084` consumes both
   spellings of `--timeout` without assigning a per-file deadline.

`COMPILER_BUILD_TIMEOUT_SECONDS=900` is a separate sanity-probe budget
(`bootstrap-from-scratch.sh:2128–2177`). The enclosing native deadline of
7200 seconds cannot override the shorter 1800-second worker wait.

## Preserved evidence

All paths below are under `C:/dev/simple-bootstrap-storage/rp3l-20261011/`:

| Artifact | SHA256 |
|---|---|
| `stage3/x86_64-pc-windows-msvc/stage2-command.transcript` | `fbcd82313b33b02cd58e1d243ec2697548d12317d2a642b1c84c9d2444356d99` |
| `logs/x86_64-pc-windows-msvc/stage2-native-build.log` | `408dda616ec651b0aea7466eb840fff3f2227cfe07f5dbbfb106a738794e1e14` |
| `logs/x86_64-pc-windows-msvc/stage2-native-build.log.rss.env` | `55ef48033fec7602069153d353078b982bddc9e2be34458ffd03943ddd571325` |
| `whole-bootstrap-control/result.json` | `a3e42bdd00bf47948c7659c517c10c26b7cad57fa51d2a2c25594a1a3420c5ea` |

The external `rel-phase3-generic-qualification-20261011/attempt12-terminal-evidence.json`
indexes seven preserved artifacts. Its original cause field predates this
source audit; the failed run and original receipts remain unchanged.

## Bounded follow-up and acceptance

The proposed next request explicitly treats 6600 seconds as the whole-worker
budget, inside a 7200-second native deadline and 10800-second outer deadline.
That is a reviewed configuration adjustment, not a demonstrated performance
fix or a per-file timeout implementation. It must keep nonzero exits,
unfinished claims, kill/reap failures, and resource refusals blocking admission.
No retry or native check was executed for this report.

A future implementation should distinguish worker and per-unit deadlines,
preserve legacy argument compatibility, and report timeout separately from
crash. A meaningful regression must run a bounded persistent worker through
multiple completed claims and an unfinished claim, checking timeout,
termination/reaping, retained incomplete evidence, and nonzero failure; an
ordinary compiler error must not be relabeled timeout. Existing timeout parse
specs verify numeric conversion only and do not prove this behavior.
