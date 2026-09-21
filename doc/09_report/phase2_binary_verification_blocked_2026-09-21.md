# Phase 2 binary verification: blocked evidence (2026-09-21)

## Verdict

**BLOCKED.** Interpreter, compiler, and loader binary coverage was not run.
There is no admitted, current-source Stage 2 compiler with the required frozen
runtime capsule. No Rust seed, unreceipted release binary, or stale admitted
binary was substituted.

## Authoritative route

The executable gate is
`scripts/bootstrap/bootstrap-phase-verification.shs --phase=stage2`. It:

- requires `phase2-runtime-capsule.env` for Phase 2;
- snapshots the admitted compiler and verifies its SHA-256;
- builds a phase-qualified full CLI and standalone test runner with the frozen
  hosted runtime;
- runs the representative compiler bootstrap suite in interpreter and compile
  modes; and
- with `--strategy=full`, runs the full compiler unit inventory in interpreter
  mode through that exact test runner and full CLI owner.

The loader has no separate binary. Loader coverage is the
`test/01_unit/compiler/99.loader` and `test/01_unit/compiler/loader` portions of
the same Simple compiler/test-runner lane.

## Current-source admission audit

The isolated lane was created from `origin/main` at
`20245f731dbe12f3eb93943e2dc3c2f4fc22d76c`.

The only discovered admitted Windows Stage 2 candidate was:

- candidate SHA-256:
  `d0eb922e8d49d27718a07cfd6646048043564a2f361c34e0a99d4d712ba50607`;
- admission path:
  `D:/wk-p2/.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env`;
- admission receipt SHA-256:
  `b53c7a430af66f7edef76d750770b40a99c506a40259a1f55676f14020d5147a`;
- producer worktree HEAD:
  `63fdcd9ea57eccea39350ab7e3136d5b8144d00c`;
- producer dirty fingerprint:
  `93d91935adaf6fa5b43893b73649147b0c4a2793953bcc55f8325f5e9cd899f6`;
- admitted source snapshot SHA-256:
  `8e8f14a2c7b6aff73a790fe5e6846c76f9a15a619441edfa88ee566e82b5560f`;
- current canonical source snapshot SHA-256:
  `64fc779d832b56892ac1c3c1f98d16a160f94e414de8f407aed17accba9b226c`;
- canonical snapshot comparison: `source_snapshot_match=no`; and
- required `phase2-runtime-capsule.env`: absent.

The current snapshot hash and comparison are console evidence. The snapshot was
created in a temporary directory and deleted by its cleanup trap; no durable
snapshot receipt is claimed. The admitted snapshot and `git-state-before.env`
remain beside the discovered candidate.

The candidate is stale by both Git lineage and canonical source content, and it
lacks the Phase 2 runtime capsule. The runner already rejects the missing
capsule with `Phase2 verification requires a SHA-qualified runtime capsule`.
No additional runner change is justified by this audit.

## Historical failure inventories

No authoritative artifact naming **43 known failures** was found. The search
covered the current documentation and tests, all Git history for the relevant
phrase/count patterns, Phase 2/loader branches and pull requests, and retained
local Phase 2 scratch reports. This report does not manufacture a 43-item list.

The exact search forms were:

```text
rg -n -i -g '*.md' -g '*.txt' -g '*.env' -g '*.json' \
  '43 (known )?fail|known failures|failures.{0,40}43|43.{0,40}failures' \
  doc .simple D:/wk-*
git log --all --oneline \
  -G'43 (known )?fail|known failures|failures.*43|43.*failures' \
  -- doc scripts test
git branch -a --list '*phase2*' '*loader*' '*binary*' '*failure*'
gh pr view 1169 --json title,body,headRefName,commits,files,url
Select-String over retained Phase 2 scratch files for:
  '43 known|known failures|43 fail|failures: 43|failed=43|43 failed'
```

The retained scratch files are under
`C:/Users/ormas/AppData/Local/Temp/claude/C--Users-ormas-dev-simple/47c70af7-c756-42a6-9364-b9901cb9c916/scratchpad/`:
`loader_results.txt`, `fail_details.txt`, and `fail_summary.txt`.

The historical data that was found is non-admissible for the current lane:

| Source | Scope | Recorded result | Why it cannot be reused |
|---|---|---:|---|
| PR #1169 | 30 representative interpreter/compiler/loader/lib specs | interpreter 8/8; loader 5/8; compiler 7/10; lib 1/3 fully green | Built and tested a fresh Rust seed; no current self-hosted admission |
| retained `loader_results.txt` | 15 loader specs | 10 passing specs, 5 failing specs; 13 failed examples | Ran with an unreceipted `bin/simple.exe` |
| retained `fail_details.txt` | compiler sample | 12 specs with visible failures; 11 terminal verdicts total 21 failures, while the truncated `access_policy_spec` section shows at least 8 more | Ran with an unreceipted `bin/simple.exe` |
| retained `fail_summary.txt` | broader sample | 24 failing specs, 59 failed examples | Ran with an unreceipted `bin/simple.exe` |

These counts are historical triage inputs only. They are not Phase 2 PASS/FAIL
evidence and are not a baseline for closing bugs.

## Exact unblock condition

Produce a fresh Stage 2 admission from the current source snapshot, publish its
SHA-qualified immutable runtime capsule, then run the authoritative verifier
once with `--strategy=full`. Retain `summary.env`, the full inventory TSV/JSON
logs, compiler and runtime hashes, and command-owner receipts. Classify
interpreter, compiler, and loader rows from that evidence only.

The next run must continue to use the Windows C toolchain policy (`clang-cl` /
MSVC C); it must not introduce GCC, G++, or C++ compilation.
