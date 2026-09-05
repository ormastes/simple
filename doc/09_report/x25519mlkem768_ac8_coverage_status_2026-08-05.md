# AC-8 branch-coverage status for X25519MLKEM768 after the manifest existence gate

**Date:** 2026-08-05
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple`
**Scope:** `src/app/test/x25519mlkem768_{coverage_contract,critical_inventory}.spl`
and the campaign specs under `test/01_unit/app/test/`.

AC-8: *"Owned X25519MLKEM768 implementation code reaches at least 98% measured
branch coverage, with 100% coverage of security-critical validation,
implicit-rejection, backend-selection, fallback, and fail-closed branches; any
mechanically unreachable branch is justified in the coverage report rather than
excluded silently."*

## 1. The defect that was fixed

Both campaign manifests listed file paths that do not exist, and neither checked
existence. The missing three were identical in both:

- `src/lib/gc_async_mut/crypto_accel/cuda_session.spl`
- `src/lib/gc_async_mut/crypto_accel/metal_session.spl`
- `src/lib/gc_async_mut/crypto_accel/vulkan_session.spl`

Background: `doc/08_tracking/bug/crypto_accel_session_modules_do_not_exist_2026-08-05.md`.

### The gate

`x25519_mlkem768_coverage_absent_in(paths)` reports every listed path that is not
on disk and is not **declared blocked**. Declared-blocked paths are named in the
verdict line, never dropped. `x25519_mlkem768_coverage_stale_blocked_paths()`
turns the gate RED in the other direction too: once a blocked module lands, the
block must be retired, otherwise the owner would sit outside the denominator
forever — the silent exclusion AC-8 forbids.

The critical inventory's owner list was a verbatim copy of the contract's. Two
hand-maintained copies of a coverage manifest can drift, so `_critical_owner_paths()`
now delegates to `x25519_mlkem768_coverage_owner_paths()`. One source of truth,
one gate. `main()` in the calibrator runs the gate as a preflight and fails with
`reason=manifest-path-absent`, naming the offending paths, instead of the generic
`owner-source-not-regular` it produced before.

Runnable check: `test/01_unit/app/test/x25519mlkem768_manifest_existence_gate_spec.spl`.

**GREEN** (tree as it stands):

```
coverage-contract manifest-existence-gate: PASS declared=37 present=37 blocked=0 absent=0 stale_blocked=0
critical-inventory manifest-existence-gate: absent=0
Results: 8 total, 8 passed, 0 failed
```

**RED** (one phantom path temporarily added to `x25519_mlkem768_coverage_spec_paths()`,
then reverted; the contract file's md5 was captured before and after each run and
is identical between the two green runs):

```
coverage-contract manifest-existence-gate: FAIL declared=38 present=34 blocked=3 absent=1 stale_blocked=0 absent_paths=test/01_unit/os/crypto/PHANTOM_RED_PROOF_spec.spl
Results: 8 total, 6 passed, 2 failed
```

The spec also carries a standing self-test (`should prove the checker can go RED
on a path that is not on disk`) so the gate cannot silently become fail-open.

## 2. Handling of the phantom entries: declared-blocked, then retired

They were **not** removed. Removing them would have shrunk the denominator
without saying so — precisely what AC-8 forbids — and would have erased the fact
that `{cuda,metal,vulkan}_ntt_provider.spl`, 1,130 lines that *do* exist, were
written against types that did not. So the three paths stayed in both manifests,
enumerated in the gate's verdict line on every run, counted as **blocked, never
as covered**:

```
coverage-contract manifest-existence-gate: PASS declared=37 present=34 blocked=3 absent=0 stale_blocked=0
```

**Then the gate caught a live state change.** A later run in the same session
went RED in the other direction:

```
coverage-contract manifest-existence-gate: FAIL declared=37 present=34 blocked=3 absent=0 stale_blocked=3 stale_blocked_paths=src/lib/gc_async_mut/crypto_accel/cuda_session.spl,src/lib/gc_async_mut/crypto_accel/metal_session.spl,src/lib/gc_async_mut/crypto_accel/vulkan_session.spl
Results: 8 total, 7 passed, 1 failed
```

with the three manifest files byte-identical (md5 checked before and after each
run). A parallel session had landed
`src/lib/gc_async_mut/crypto_accel/{cuda,metal,vulkan}_session.spl` at
`2026-08-05 06:36:14`; they are untracked (`??`) as of this writing. The block
had outlived the gap, and the stale-block check forced its retirement rather
than letting three owners sit outside the denominator indefinitely. The declared-
blocked set is now **empty**, and the gate is fully green:

```
coverage-contract manifest-existence-gate: PASS declared=37 present=37 blocked=0 absent=0 stale_blocked=0
```

Owner-level accounting, measured:

| | count | share |
|---|---|---|
| owners declared | 23 | 100% |
| owners with source on disk | 23 | 100% |
| owners declared blocked | 0 | 0% |

Caveat: the three session modules are new and untracked. If they are reverted,
the gate goes RED with `absent=3` — loudly, which is the point.

## 3. Re-measured branch coverage: **none exists**

There is no measured branch-coverage figure to correct, because none has ever
been produced in this tree:

1. **No raw coverage stream.** No decision/condition coverage artifact for this
   campaign exists anywhere outside `.git`.
2. **No composed receipt.** The strings `x25519mlkem768-branch-coverage-v2` and
   `simple-native-coverage-run-v2` appear only in the contract, its two specs,
   and the schema fixture `test/fixtures/crypto/x25519mlkem768/branch_coverage_receipt_schema.sdn`.
   No instance document exists.
3. **Both campaign specs were dead at file level before this change, and both
   now run and fail.** Measured on the binary above with
   `--no-cache --no-cover-check --no-db --no-session-daemon`:

   | spec | before | after |
   |---|---|---|
   | `x25519mlkem768_critical_inventory_spec.spl` | `Results: 1 total, 0 passed, 1 failed` | `Results: 4 total, 2 passed, 2 failed` |
   | `x25519mlkem768_coverage_receipt_composer_spec.spl` | `Results: 1 total, 0 passed, 1 failed` | `Results: 4 total, 2 passed, 2 failed` |

   The `1 total` in the "before" column is the FILE-LEVEL wrapper, not an
   example count: `src/app/test/x25519mlkem768_coverage_receipt.spl` failed to
   parse (`Unexpected token: expected expression, found Assign`) and killed both
   specs before a single `it` block ran. The file is unmodified in git and was
   never edited here, so the parse failure was pre-existing. It stopped
   reproducing after this change; the only tree deltas are the two manifest
   files and the new gate spec, and the most likely trigger is the added
   `use app.io.mod.{file_exists}` altering module load order. **Mechanism
   unproven — recorded as an observation, not a fix.**

So the honest figure is: `branch_outcome_total = 0`, `branch_outcome_covered = 0`,
`branch_coverage_basis_points` **undefined**. Any percentage previously attributed
to this campaign was not produced by this machinery.

### 3a. Four real failures were unmasked

With the file-level death gone, four `it` blocks that had never executed now run
and fail. These are pre-existing defects in the calibrator and composer, not
regressions from this change — the composer spec does not touch either file
edited here, and the inventory's owner list is proven byte-identical and
order-identical to the copy it replaced.

| spec | failing example | observed |
|---|---|---|
| critical inventory | `should derive concrete compiler identities for the exact twenty-three-owner snapshot` | fails |
| critical inventory | `should reject incomplete owner and true-false requirement sets` | `expected symbolic-critical-row-invalid to equal symbolic-owner-set-incomplete` |
| composer | `composes exact twenty-three-owner measured outcomes` | fails |
| composer | `rejects a missing owner and an uncovered critical outcome` | fails |

All four are "twenty-three-owner" cases — the same 23-owner snapshot whose
3 owners are phantom. They need their own triage pass.

## 4. AC-8 verdict: **UNMEASURABLE**

Not met, not missed — unmeasurable. The 98% bar cannot be scored because the
measurement path has never executed end to end, and the manifest it would have
been scored over was 8.1% phantom until today.

AC-8 additionally demands **100%** coverage of backend-selection and fallback
branches, which live in the three GPU NTT providers. Their session types were
absent for the whole life of this campaign, so the providers erased to ANY and
dropped out of native lowering. The session modules landed today (section 2) but
are untracked and unverified here — whether the providers now type-check, and
whether their fallback branches are reachable at all, is **not established** and
must not be assumed either way.

## 5. To make AC-8 measurable

1. Triage the four unmasked failures in section 3a, and pin down why the
   receipt's parse failure stopped reproducing — an intermittent parse failure
   in the coverage composer is itself a coverage-illusion risk.
2. Verify the newly landed `crypto_accel` session layer actually resolves
   `CryptoCudaSession` / `CryptoMetalSession` / `CryptoVulkanSession` for the
   three providers. An unresolved `use` is only a WARN, so a green exit status
   does not answer this — check that the providers stop dropping to the
   interpreter.
3. Produce a raw decision-condition coverage stream over all 23 owners and
   compose a receipt.
4. Only then quote a basis-points figure, and justify every unreachable branch in
   this document rather than excluding it.
