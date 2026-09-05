# Stage-2 hello world SEGVs in `native_compile` (step 5/6) — newly exposed by the unwrap-theft fix

- **Filed:** 2026-08-25
- **Status:** OPEN. Newly exposed, not newly introduced.
- **Severity:** blocks the Stage-2/Stage-3 self-host lane (rc=139 on hello world).
- **Parent:** `stage3_n_modules_zero_segv_mir_lowering_x86_64_2026-08-24.md`
- **Predecessor:** `poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25.md` (FIXED)
- **Gate:** `check-stage2-option-unwrap-not-stolen.shs` — its *behavioural* check
  is red because of THIS, not because of unwrap theft. Its *symbolic* check is green.

## Why this is a new record and not the old one

The two `Poll.unwrap` bind sites are fixed and measured: `lower_and_check_impl`
went 4 → 0 `Poll_dot_unwrap` call sites, whole-binary 272 → 0, and the
`E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` signature is **absent** (measured
count 0). The rc=139 that remains has a different location and a different
signature.

**Do not re-open the unwrap hunt from this crash.** That is the specific mistake
this record exists to prevent — the parent record was rewritten twice for
premature attribution, and the second bind site was found only after the first
fix's differential was read correctly.

## Evidence

Stage 2 built from base `c6041e04d4e` + the second-site fix by the sanctioned
invocation: **757 compiled, 0 failed**, linked; rejected at sanity, preserved as
`build/bootstrap-bind2/stage2/x86_64-unknown-linux-gnu/simple.rejected`.

Hello world, positional form, reproduced by hand (the bootstrap harness reports
this as `UNDIAGNOSABLE: the stage failed with no error message of any kind`,
which is the harness suppressing the smoke's stderr — not an absence of
evidence):

```
[build] borrow_check   unknown/unknown step 4/6 +895ms done
[build] process_async  unknown/unknown step 4/6 +895ms done
[build] optimize_mir   unknown/unknown step 4/6 +895ms done
[build] weave_aop      unknown/unknown step 4/6 +895ms done
[build] native_cache   1/1            step 5/6 +1353ms complete
[build] native_compile 0/1            step 5/6 +1353ms .tmp.hw
Segmentation fault (core dumped)          rc=139
E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED count = 0
```

The pipeline now completes HIR lowering, borrow-check, async processing, MIR
optimisation, AOP weaving and the native cache, then dies entering
`native_compile`. **No pre-fix build ever reached this phase** — the earlier
crash at MIR lowering masked everything downstream. That is the sense in which
this is newly *exposed*: the code was always there, nothing could reach it.

## Not yet established

- Whether lane-s7's `--entry` vs positional discriminator still applies. The
  `--entry` run here was reaped with no `.rc` file, which per the attribution
  harness is **UNKNOWN, never a pass**. Unmeasured, not inferred. Note that
  `--entry` without `--source` scans the whole default source graph and is very
  slow; bound it with `--source <dir>` when retrying.
- Whether this shares a cause with the parent record's Stage-3 `aot:lower_to_mir`
  death. Same rc, different phase — do not assume either way without evidence.

## Reproduce

The Stage-2 binary measured here is **preserved** (the lane worktree is gone):
`/mnt/data/evidence-bind2/stage2-bind2-simple.rejected`, sha256 `4475ccb2e80e07ca…`,
alongside `hw_pos.log` (the hand-reproduced smoke) and `gate-unwrap.log`.

```sh
S2=/mnt/data/evidence-bind2/stage2-bind2-simple.rejected
printf 'fn main():\n    print "hello"\n' > /tmp/hw.spl
"./$S2" native-build /tmp/hw.spl --backend=cranelift -o /tmp/hw.bin; echo "rc=$?"
# expect rc=139, and ZERO E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED lines
```
