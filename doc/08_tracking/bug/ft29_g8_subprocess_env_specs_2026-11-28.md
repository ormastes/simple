# FT-29 G8: specs failing on subprocess / tool environment (Windows)

Status: verification-pending

Measured 2026-11-28 with `bin/simple.exe` (Rust bootstrap seed) on Windows.

| Spec | Before | Cause | Class | Action |
|---|---|---|---|---|
| cli/duplicate_check_contract | rc 127 (stale) | none now: 3/3 pass | n/a | no change |
| pkg/feature/requires_range | 2 fail | `bin/simple` is the seed; no `lock`/`update` | tool absent | `precondition:` -> BLOCKED |
| gen_lean/feature/source_model_command | 3 fail (rc 124) | seed has no `gen-lean source-model` | tool absent | `precondition:` -> BLOCKED |
| compiler/feature/driver_synthetic_registration_live | 2 fail rc -1 | `simple_cmd()` only probed `bin/simple`; on Windows the file is `bin/simple.exe`, fell back to nonexistent debug binary | launcher bug | probe `bin/simple.exe` |
| build/feature/dist_build_staged_two_node | 0 examples | seed parser rejects the multi-line `val x = if c:\n a else:\n b` at `two_node_staged_qualification.spl:514`; module load error | source/parser | aligned `else:` form (see Parser note) |
| mail_cli/feature/mail_pop3_credentials | no verdict | no hang in code: each `tools/mail-cli/bin/mail` call takes tens of seconds under MSYS (thousands of forks), the probe runs 6 parallel sub-groups, and `protocol_1` alone exceeded 300 s on a loaded host, so the runner budget expires first | performance | OPEN, see below |

## Repro and prevention
- Repro: the specs above themselves (seed-only host => BLOCKED outcome instead of failure; `driver_synthetic` now launches `bin/simple.exe`).
- Prevention: the same `precondition:` helper pattern in both seed-gated specs;
  generalization: any spec spawning `bin/simple` must probe `.exe` on Windows.

## Open
- Pop3 fixture cost on Windows: per-call fork cost of the bash client (`tools/mail-cli/lib/*.bash` sourcing chain). Needs a reduced-fork client path or a larger per-spec budget; not fixed here.
- dist_build_staged_two_node re-run after the fix: 2 of 2 pass (was 0 examples, module load error).

## Parser note (not a parser bug)
Original: `val r = if c:
    "a" else:
    "b: " + x` (the `else:` trailing the then-value on the same line, with the else body on following lines). Minimal repro fails: `expected Indent, found FString`. The same shape with `else:` on its own line aligned with `if` parses and runs, and the fully inline `if c: a else: b` also works. A trailing `else:` after an indented-block value has no defined grammar (the then-branch is an inline expression, the else-branch a block), so this is invalid syntax, not a parser gap; no workaround tag needed. The fix uses the aligned form and keeps `val`.

## Follow-up request
- Diagnostics: the seed reports `expected Indent, found FString` for a trailing `else:` after an inline then-value. A message naming the construct ("else-block after inline then-value is not allowed; put `else:` on its own line aligned with `if`") would make this self-explanatory. Feature request, not a parser bug.
- Verified empirically (not just by diff): with the seed on this Windows host the two seed-gated specs reported `outcome=BLOCKED` (2 and 3 blocked), so `bin/simple` / `./bin/simple` resolve through the launcher here.
