# Lane handoff — rt + bitstream sspec (2026-08-18/19)

Status: session ended. All work below is **landed at origin/main** unless marked
otherwise. Parent programme: `doc/03_plan/infra/binary_runtime_hardening/plan.md`.

This is a handoff, not a summary of intentions. Failures, unknowns, and
unverified claims are marked as such.

---

## 1. What landed (verified present at origin by symbol-grep, 2026-08-19)

| area | change | evidence |
|---|---|---|
| base64url | `base64url_decode_strict` + `Base64UrlError` (RFC 4648 §3.3 rejection); byte-taking `base64url_encode_bytes` | `10/10`, `9/9` specs |
| JWT/token | `auth_middleware.spl`, `password_reset.spl` decode via strict; 3 duplicate local decoders/encoders deleted | `9/9` at the time (see §4 caveat) |
| session/CSRF | `compute_signature`, `csrf_token_for_session` made executable | `11 total, 8 passed, 3 failed` — 3 RED **on purpose**, see §3 |
| rt gate | no longer rewrites its baseline on a passing run (`--update-baseline` added); `extern fn rt_*` declarations counted separately | selftest 3 → 8 fixtures |
| rt classification | 2 of 13 candidates allowlisted (`vulkan_sffi`, `metal_sffi`) | `doc/08_tracking/rt_boundary/provider_classification_2026-08-18.md` |
| bitfield | `bitfield_mir_spec.spl` 19 vacuous → 14 real, in **both** twin trees | `14/14` each |
| dead code | `src/compiler/50.mir/custom_primitive_bitfield.spl` deleted (285 lines) | confirmed absent at origin |
| seed | lane's Rust seed made to compile (3 files restored to origin's versions) | `Finished release profile ... 0 errors` |

Verified at origin: `base64url_decode_strict`, `_webfw_digest_to_hex`,
`extern_declarations`, `would_straddle_word` all present;
`custom_primitive_bitfield.spl` absent.

---

## 2. Verified vs merely believed

**Verified by running, this session:**
- every `Results:` line quoted above (each re-run by the parent, not taken from a subagent report);
- the rt gate no longer dirties its baseline (`git status` empty before *and* after a run);
- the seed compiles (`cargo check --release --bin simple`, 0 errors);
- deletion-safe: `custom_primitive_sffi_spec.spl` 20/20 and `bitfield_mir_spec.spl` 14/14 after removing the dead module;
- all six mandatory pre-push guards PASS at the pushed tip.

**NOT verified — do not cite as done:**
- **No bootstrap.** `bin/simple build bootstrap` was never run. The 285-line
  deletion is proven safe for *module loading* and AC-5/AC-6 behaviour only,
  **not** for a from-scratch self-hosted rebuild. This gap is still open.
- **The vacuous-spec sweep is structural only.** 423 files / 1,537 examples are
  *structurally* incapable of failing. Failability was never proven — that needs
  mutation testing (delete the subject, observe red), which was not run.
- **The "no spec reachability" count is unstable.** It moved 245 → 281 → 348
  across three revisions because the scan never terminated. **≥348 is a lower
  bound, not a measurement.** Re-run to completion before quoting any number.
- **CSRF finding #2** (`csrf_integration.spl:43`) rests on the declared
  signature pair alone; its confirming run never terminated. Dispositive on
  types, but never observed failing.

---

## 3. Known-RED tests deliberately left red

`test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl` —
**3 of 11 examples fail on shared main.** This is intentional and documented in
`doc/08_tracking/bug/webfw_signing_wrong_digest_and_csrf_not_session_bound_2026-08-18.md`.

They encode two real security defects:
1. the digest does not match the openssl HMAC-SHA256 oracle (shape
   `00000019000000b5…` — 8 values where SHA-256 has 32);
2. `csrf_token_for_session` returns the **same token for different session
   ids** — tokens are transplantable between sessions.

**Do not "fix" these by replacing the expected values with the observed ones,
or by relaxing them to self-consistency.** The expected values are openssl's.
Deleting them restores a green suite while leaving forgeable CSRF tokens.

If the next session decides the red is too disruptive for other lanes, the
acceptable move is to *quarantine with a tracking id*, never to weaken.

---

## 4. The unexplained thing — read this before trusting any measurement here

Two independent measurement hazards were hit, and both can silently invalidate
a green result:

**(a) The shared seed binary changes under you.** A spec measured `9 passed,
0 failed` and later `5 passed, 4 failed` on *byte-identical source*. The cause
was a rebuild of the shared `bin/simple` at 10:12:23, which broke instance-method
dispatch repo-wide (a 14-line hello-world class fails:
`method 'greet' not found on type 'object'`). Filed as
`seed_rebuild_10_12_breaks_instance_method_dispatch_object_receiver_2026-08-18.md`.
**CLAUDE.md already says to record binary identity with timings; this shows it
is required for pass/fail too.**

**(b) Code on disk did not match code executed.** In `session.spl`, three
different function bodies produced **byte-identical wrong output**, with the
final edit verified present at the file. Unresolved, and it undermines every
measurement in this file's vicinity. Two real ambiguity hazards were found but
**neither was confirmed as the cause**: `hmac_sha256(key: text, data: text) -> text`
has 3 same-signature definitions, and `bytes_to_hex` has 10 under `src/lib`
(one untyped). The pure-Simple crypto stack itself was verified CORRECT against
openssl, so the defect is in dispatch/reachability, not HMAC.

---

## 5. Infrastructure defects found (all filed)

- **The pre-push hook sabotages its own guards.** `git push` triggers a hook
  whose git invocations write `core.bare = true` into the *shared*
  `simple-main/.git/config`; the next guard then cannot see a work tree and
  fail-closes to `ERROR — nothing was checked`. Every push attempt this session
  was blocked this way — always status 2 (ERROR), never status 1 (FAIL). The
  repo already ships `scripts/check/check-core-bare-sanity.shs` documenting the
  relative-`GIT_DIR` mechanism.
  **CORRECTION:** `shared_git_config_core_bare_flipped_true_breaks_all_worktrees_2026-08-18.md`
  speculates a subagent did it. That is **wrong** — it is the push path itself.
  That doc should be amended; this note is the correction of record.
- `land.shs` runs only the rules.sdl **quick** group; the mandatory guards are in
  group **full**, so they do not run on that path. Run them manually.
- `check-no-direct-rt.shs` counted `extern fn rt_*` declarations as call sites
  (74 of 111 matches in `vulkan_sffi.spl`) — fixed, but note the baseline moved
  18788 → 12012 → 12020 for *definition* reasons, not migration progress.

---

## 6. What the next session should pick up, in order

1. **The seed dispatch regression.** Nothing else can be verified end-to-end
   until it is fixed; a 14-line reproducer is in its bug doc. It also
   invalidated a green result already committed to main.
2. **The code-on-disk vs code-executed discrepancy (§4b).** Higher leverage
   than any individual fix, because it silently falsifies measurements.
3. **The two live security defects** — wrong digest and non-session-bound CSRF
   tokens — which are what the 3 red examples pin.
4. Then: bootstrap to close the deletion gap; re-run the coverage scan to
   completion; consolidate the 4th `base64url_encode_bytes`
   (`src/lib/common/jwt/encode.spl:144`).

## 7. Lane hygiene notes

- This worktree is **not** a jj repo (`jj` reports "no jj repo in .") — the
  documented `sj raw jj` flow does not apply here; plain git was used.
- Another session's uncommitted work appeared in this worktree twice and was
  **dropped, not pushed** (a commit titled `base` carrying 16 files belonging to
  screenshot-SFFI / test-runner / GUI lanes). Check `git log origin/main..HEAD`
  before pushing from here.
