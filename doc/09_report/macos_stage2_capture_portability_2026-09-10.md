# macOS Stage-2 capture portability — 2026-09-10

Status: **WARN — capture regressions pass; Stage-2 remains rejected.**

This is the Astra escalation after two fresh Stage-2 attempts. The third and
final attempt preserved the existing cache, compiled the candidate, and reached
the first frontend fixture. It failed on a separate hash-tool portability bug,
subsequently fixed and verified only through focused shell regressions.
No fourth bootstrap attempt, compiler admission, Chrome build, or performance
comparison was performed or claimed.

## Changes

- `candidate_frontend_capture_setup` now selects an explicit Darwin adapter.
  macOS cannot resolve directory children through Linux `/proc/<pid>/fd` paths.
  The output directory and Perl collector remain held on inherited descriptors.
- The existing Perl collector uses `fchdir` to anchor Darwin output operations
  to the held directory. The candidate child restores the original working
  directory before execution. Exclusive hard-link publication refuses existing
  log/receipt files and symlinks; Linux retains its `renameat2` path.
- Every Darwin probe rewinds the held helper before execution. `/dev/fd`
  duplicates its shared file offset: without the rewind, a second execution
  can read EOF and exit zero without running the collector.
- The collector contract now runs with host-correct descriptor and executable
  paths. A separate regression exercises macOS capture setup, two sequential
  probes, hash-bound receipts, and refusal to replace prior evidence.
- The frontend hash helper prefers `sha256sum` when available and falls back
  to `shasum -a 256`. It propagates command failures and rejects missing tools
  or malformed digests instead of accepting a successful trailing pipeline.

Sol's preceding staging-permission fix in `bootstrap-stage3/authority.shs` and
its seed tuple projection regression were preserved unchanged.

## Verification

Executed in `/Users/ormastes/simple_worktrees/stage2-chrome-20260910`:

| Check | Result |
| --- | --- |
| Perl collector syntax | PASS |
| Frontend admission shell syntax | PASS |
| `candidate_frontend_darwin_capture_test.shs` | PASS |
| `process_group_bounded_log_contract_test.shs` | PASS on macOS |
| `candidate_frontend_hash_portability_test.shs` | PASS with exact admission PATH, isolated shasum fallback, and error controls |
| Darwin capture integration with exact admission PATH | PASS after portable hash fix |
| Diff whitespace | PASS |
| Final Stage-2 candidate build | 2 compiled, 859 cached, 0 failed; 17.0 seconds |
| First frontend fixture collector | `reason=child-exit`, `raw_status=0`, 637 captured bytes |
| Stage-2 admission | FAIL: frontend wrapper status 126 |
| Linux runtime regression | Not executed on this macOS host |

The collector contract covers combined streams, overflow, timeout and descendant
cleanup, supervisor/child signals, execution errors, publication signal ordering,
directory replacement, existing/symlink/temporary/receipt collisions, held-helper
replacement, command working directory, and rapid-exit readiness handshakes.

## Preserved evidence

Paths below are relative to that worktree:

- `build/native_probe/stage2-chrome/third-attempt-console.log`
- `build/native_probe/stage2-chrome/logs/aarch64-apple-darwin/stage2-native-build.log`
- `build/native_probe/stage2-chrome/stage3/aarch64-apple-darwin/stage2-command.transcript`
- `build/native_probe/stage2-chrome/stage3/aarch64-apple-darwin/stage2-sanity.env`
- `build/native_probe/stage2-chrome/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log`
- `build/native_probe/stage2-chrome/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-bootstrap-0.log.bounded.env`
- `build/native_probe/stage2-chrome/darwin-capture-test.log`
- `build/native_probe/stage2-chrome/bounded-log-darwin-test-final.log`
- `build/native_probe/stage2-chrome/portable-hash-sanitized-path-test.log`
- `build/native_probe/stage2-chrome/darwin-capture-sanitized-path-test.log`
- `build/native_probe/stage2-chrome/stage2/aarch64-apple-darwin/simple.rejected`

The previous complete output tree was cloned before the retry to
`build/native_probe/stage2-chrome-attempt2-preserved`. Its rejected binary and
failed sanity receipt were byte-compared before archiving the canonical failed
sanity receipt as `stage2-sanity.env.prior-to-attempt3`. The existing native cache
kept its original path and was reused. Both rejected candidates have SHA-256:

`dbe62ce0bca9d3832e2d06063c48222292bab605f854f2228508685adf260238`

## Final attempt failure and focused follow-up

During the final attempt, `candidate_frontend_hash_file` called `sha256sum`
unconditionally. The admission
environment has a restricted macOS PATH where that command is absent. The
candidate successfully builds `p2_add`, and the collector publishes its correct
receipt, but the shell hash comparison rejects it and prevents the remaining
frontend and receiver checks from executing.

The portable hash fix now follows the `sha256sum`/`shasum` preference in
`bootstrap_stage3_hash_file`. Its focused regression checks a known 64-character
SHA-256 digest, a path containing spaces, GNU-tool preference, an isolated
shasum-only fallback, absent tools, absent input, command failure, and malformed
output. Both that test and the real Darwin capture/collector integration passed
with the exact recorded admission PATH:

`/opt/homebrew/Cellar/llvm@18/18.1.8/bin:/Users/ormastes/simple_worktrees/stage2-chrome-20260910/build/native_probe/rustup-isolated-copy/.cargo/bin:/opt/homebrew/bin:/usr/bin:/bin`

No fourth full bootstrap attempt or Chrome invocation followed this fix. The
existing failure receipt remains unchanged; the candidate remains rejected.
The remaining frontend probes, receiver capability, and full admission are
unverified with the corrected helper.

Even after Stage-2 admission, the canonical Chrome oracle builder currently
requires Stage-3 provenance, authority-map, compiler, and sanity artifacts.
Those prerequisites remain unproven and must not be bypassed.
