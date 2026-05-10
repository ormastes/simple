# M-B retry — `crypto-pure-simple-port` Curve25519 backend cleanup (done)

Wave 4. Date: 2026-04-25. Author: M-B-retry (Sonnet sub-agent).

## Why a retry

Original M-B (`m_b_curve25519_done.md`, 2026-04-25 wave 2) had landed the
deletion of three obsolete Curve25519 backends. The 2026-04-26 destructive
restore wave brought them back. This task re-deletes them, in a detached
worktree, behind branch `worktree-mb-curve-delete` (the parallel-jj-safe push
path), per `feedback_push_via_worktree.md`.

## Caller sweep (re-verified 0 callers)

In `src/` the wider sweep returned only the in-scope files themselves
(self-references inside the to-be-deleted set):

| Module | grep `os.crypto.MODULE` (src/) | External callers |
|---|---|---|
| `os.crypto.curve25519_bigint` | `src/os/crypto/curve25519.spl` (line 14, dead import) and `src/os/crypto/curve25519_bigint_wrapper.spl` (re-export) | **0** (both are in-scope to be deleted/edited) |
| `os.crypto.curve25519_bigint_wrapper` | none | **0** |
| `os.crypto.curve25519_smalllimb` | none | **0** |

Evidence: `grep -RIln --include='*.spl' '<MODULE>' src/` per the runbook.
Final post-edit sweep returned `NONE` for all three patterns.

## Files deleted (at `e81431e4dc`)

- `src/os/crypto/curve25519_bigint.spl` (517 LOC; B2 `[u8]` quadratic workaround — bug closed `e4b572b7c4`)
- `src/os/crypto/curve25519_bigint_wrapper.spl` (26 LOC; re-export shim only)
- `src/os/crypto/curve25519_smalllimb.spl` (531 LOC; Cranelift `>>` workaround — bug closed FR-DRIVER-0002b 2026-04-18)

Total purged: 1074 LOC of obsolete-by-evidence backend code (per
`field_design.md` §1, both root causes are now fixed).

## Files modified

`src/os/crypto/curve25519.spl` — survivor, 1291 → 1277 LOC.
md5 final: `a9bf6a714fe8d888769fe5761783e4f3`. Changes:

1. Removed line-14 dead import `use os.crypto.curve25519_bigint.{x25519_safe,
   x25519_base_safe, bigint_roundtrip_probe, bigint_mask_probe,
   bigint_cswap_probe, bigint_ladder_probe}` and replaced with a 3-line
   removal-marker comment pointing at FR-DRIVER-0002b + B2 + R-C field design §1.
2. Removed 6 dead re-export shims (former lines 643–659):
   `x25519_bigint_probe`, `x25519_base_bigint_probe`,
   `x25519_bigint_roundtrip_probe`, `x25519_bigint_mask_probe`,
   `x25519_bigint_cswap_probe`, `x25519_bigint_ladder_probe`. They forwarded
   into the now-deleted backend; keeping them would have been a compile error.
3. Replaced the shim block with a 1-line removal-marker comment.

Residual `bigint*` reference count in survivor after edit: **0**.

## Tests run

| Spec | Cases | Pass | Fail | Notes |
|---|---|---|---|---|
| `test/system/os_crypto_ref_primitives_spec.spl` | 31 | **31** | 0 | Includes 3/3 X25519 RFC 7748 (`x25519_base` / shared secret / iterative `x25519(9,9)`). 1303 ms. |

Direct-invocation sanity: same spec re-run a second time post-restore — same
31/31 result.

## Deliberate-fail probe (per `feedback_compile_mode_false_greens.md`)

Edited `test/system/os_crypto_ref_primitives_spec.spl` line 244 (Poly1305 RFC
7539 §2.5.2 byte[0] assertion):

```
-        expect(mac[0]).to_equal(0xa8)
+        expect(mac[0]).to_equal(0xff)
```

Run output (RED): `Passed: 30  Failed: 1  Duration: 1203ms` — exactly the
expected failure on the corrupted Poly1305 byte[0] case. Runner is live; the
prior 31/31 was real.

Edit reverted to `0xa8`; final run re-confirmed **31/31 GREEN** (1304 ms).

## Worktree branch

```
worktree path : /tmp/mb-curve-delete  (detached HEAD off d43e8c5c50)
branch        : worktree-mb-curve-delete (pinned via git update-ref)
HEAD          : e81431e4dcce32b82ebafdf6449511f5115d857d
subject       : chore(crypto): delete 3 obsolete curve25519 backends (M-B retry; obsolete-by-evidence per R-C)
diff stat     : 4 files changed, 4 insertions(+), 1092 deletions(-)
```

Push path (deferred to caller per `feedback_push_via_worktree.md`):
```
cd /tmp/mb-curve-delete && git push origin worktree-mb-curve-delete:main
# or fast-forward main onto e81431e4dc via the main project's jj.
```

## advisor() outcome

Called once before substantive work. Advisor confirmed: 0-caller evidence is
unambiguous, the 2 self-references are exactly the in-scope files, no extra
sweep needed. Reminded me about the deliberate-fail probe and the
`git update-ref` branch pin — both completed.

## Acceptance gates (all green)

- [x] 0 external callers verified (3 sweeps + final post-edit sweep).
- [x] 3 obsolete files removed via `git rm`.
- [x] Survivor `curve25519.spl` cleaned: dead import + 6 shims removed; 0 residual `bigint*` references.
- [x] `os_crypto_ref_primitives_spec.spl` 31/31 (incl. 3/3 X25519 RFC 7748).
- [x] Deliberate-fail probe RED → restored → re-run GREEN.
- [x] Branch `worktree-mb-curve-delete` pinned at `e81431e4dc`.
- [x] No edits outside disjoint scope (only `src/os/crypto/curve25519*.spl`).
- [x] No new externs.

## Wave-3 follow-ups (still NOT done — same as original M-B note)

- Port `x25519`, `x25519_base`, `_clamp_scalar`, `_mask_u_coord`, `_cswap_pair`,
  `_ladder_step`, and the in-file `x25519_smalllimb`/`_x25519_fe_*` scaffold
  to `src/lib/common/math/curve/{montgomery,curve25519}.spl` per R-C
  `field_design.md` §2/§5.
- Repoint the 8 callers, then delete `src/os/crypto/curve25519.spl` itself.
- Retire the `x25519_fe_probe` / `x25519_base_fe_probe` scaffolding and the
  orphan first `_clamp_scalar` near line 621.
