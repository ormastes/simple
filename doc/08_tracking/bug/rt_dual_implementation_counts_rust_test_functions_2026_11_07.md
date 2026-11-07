# Runtime dual-lane ratchet counts Rust test entrypoints as primitives

- Severity: P2; status: open pending reviewed PR landing.
- Owner: `scripts/check/check-rt-dual-implementation-ratchet.shs`.
- Session: `01a1afac/rt-dual-tests`; target: `release/1.0.0`.

## Failure and root cause

The [PR #7346 server failure](https://github.com/ormastes/simple/actions/runs/42276624483/job/128094475091)
classified six private `#[test] fn rt_path_components_*` items as new Rust-only
runtime primitives. The six analogous `rt_path_normalize_*` tests in PR #7343
have the same attribute/function shape. At release base
`bfcab1cde567ad9efa4ced3bb2c67299587dde14`, lines 195–203 use a raw line-oriented
`fn rt_*` grep, despite the policy comment saying test helpers are not runtime
primitives. A test entrypoint is not a production primitive.

## Narrow repair

Retain the legacy Rust candidate regex behavior and file selection, including
the existing tests.rs exclusion. Tokenize only to associate an outer `#[test]`
with its own function occurrence, then suppress that occurrence by source
offset. Never subtract names globally: an actual private primitive remains
counted when another module contains a same-named test. Visibility, symbol
prefix, arbitrary file names and cfg/module graphs do not decide exclusion.

Comments, strings, raw strings and nested comments cannot leak a test attribute
onto an adjacent real item. Existing legacy candidates inside comments/strings
remain counted, and the old multiline-declaration blind spot is preserved;
this repair does not silently broaden lexical extraction. C extraction,
allowlists, baseline contents, single-lane comparison, stale enforcement and
committed-source authority are unchanged.

The original twelve selftest fixtures are unchanged. Three new fixtures use the
production extractor and comparison for mixed outer attributes and adjacent
private primitives, attribute leaks plus legacy lexical behavior, and a real
primitive sharing a test name in another module. Real unpaired primitives still
produce new Rust-only debt. Existing new/stale/delta and allowlist negatives
remain active.

## Finite execution ledger

1. **FAIL**, preserved: shell syntax passed, then the first production selftest
   failed lane separation because the new token pass left Perl's shared source
   cursor at EOF. The following candidate `/g` loop found no Rust functions.
   Exit 2; no target scan ran. Log SHA256:
   `6dd7daa79ef52d69b4ab0e41a7b5d999d1f082e384d5a0fc2fd1e4e8052b1fcc`.
2. **PASS**, after the one-line cursor reset: normal full production replay
   `bash scripts/check/check-rt-dual-implementation-ratchet.shs --rev a72e7fa953fc1bf88fffc9ebe6d637ad60173254 --baseline-rev bfcab1cde567ad9efa4ced3bb2c67299587dde14`.
   Actual result: **15 fixtures passed; 2,610 symbols checked against 2,621
   single-lane base entries; zero new**. Frozen-baseline drift remains visible:
   **233 new, 109 stale, informational** in delta mode. Exit 0, elapsed 81.173s.
   Separate raw C/Rust population counts are not printed and are not claimed.
   Log SHA256:
   `49d262ab27da0cf28aeefb8fd9feadfc016b1634f56fd5028b6a1028338ff21e`.

No parent selftest-child/allowlist bypass environment was set. The production
replay automatically ran all fifteen selftests; no separate passing selftest,
second normalize replay or unchanged syntax check was rerun. Attempt count:
**2/6**, including the failed cycle. Source SHA256 was pinned before and after
the successful replay:
`a7fa53267ed625e2c23088a713b513c93142ec6aaab320c46c8c2935a1f7c633`.
Tested Git blob: `d84feeb64c9c68d3a775f6d063d934496c4f71b1`.

Root reviewed the actual source, cursor correction, meaningful fixtures and
terminal replay evidence. Qualification is **PASS for this checker repair
only**. This does not qualify runtime implementations or complete the broader
MIR/codegen campaign. Mandatory push/server checks apply to the final PR head.
The canonical root bug claim remains held until reviewed landing.

Local immutable evidence is retained under
`C:/dev/simple/.git/worktrees/rt-dual-tests-d88f/evidence/`:
`cycle1-command.sdn`, `cycle1-syntax.log`, `cycle1-replay.log`,
`cycle1-result.sdn`, `cycle2-command.sdn`, `cycle2-replay.log` and
`cycle2-result.sdn`. Final metadata-guard and publication receipts are retained
alongside them. Provider input/output/cache-read/cache-create token counts,
comparable cohort average and ratio are unavailable; no estimated or zero-filled
usage is claimed.
