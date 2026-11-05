# Linux Phase 2 backend-bound fixture drift

Status: FIXED by focused fixture correction; full native bootstrap remains unqualified. CI38162989607 at51b15dc failed four of16 contract scenarios. Actual diagnostic reproduction proves missing mandatory --backend rejects before verifier and memory validation. Fake verifier also omitted verification_backend in summary and command-owner receipt.

Fix only the test fixture: exercise all14 existing scenarios on both LLVM and Cranelift, enforce backend forwarding, emit backend-bound receipts, and reject missing/invalid backends before verifier work. Production runner unchanged.

Qualification: corrected32 runner scenarios PASS once; shell syntax PASS. No compiler or full bootstrap executed.

## Evidence: re-verification 2026-11-05 (work/libbug-linux-phase2fix-20261105)

Re-checked on `origin/release/1.0.0` @ adfeae3765c. The correction is already
present via commits 114ff44787b (runner-side backend/receipt enforcement) and
d80aaaa574f (fixture binding, "test(bootstrap): bind Linux Phase2 fixtures to
explicit backend"); both are ancestors of release/1.0.0. No fixture or test
change was required.

- RED (pre-fix reproduction, d80aaaa574f^): `16 runner scenarios; 4 failures` —
  `good`/`binding` rejected by `--backend=llvm|cranelift is required` and both
  memory-cap guards unreachable, matching the CI38162989607 signature.
- GREEN (current test): `32 runner scenarios; 0 failures`, exit 0 (14 scenarios
  x llvm/cranelift + malformed/zero memory-cap guards + missing/invalid backend
  rejection before verifier work). `sh -n` syntax PASS.
- Non-vacuity: three deliberate fixture corruptions are each caught —
  (a) summary omits `verification_backend`: 4 failures (runner rejects, status 2);
  (b) command-owner receipt omits `verification_backend`: 4 failures;
  (c) fake verifier stops forwarding `--backend` (accepts only cranelift):
  2 failures (llvm good/binding only). Corruptions were applied to throwaway
  copies under /tmp, never committed.

## Premise triage 2026-11-05 (mirp2-F, origin/release/1.0.0 @ 27e65c24371-era)
CLOSE: fix commits 114ff44787b + d80aaaa574f are ancestors of release/1.0.0; the
2026-11-05 re-verification above (32 scenarios, 0 failures, 3 non-vacuity
corruptions caught) is the evidence. bug_db status should be `fixed`.
