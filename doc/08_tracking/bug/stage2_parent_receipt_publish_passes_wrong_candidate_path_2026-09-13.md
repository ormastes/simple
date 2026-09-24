# Site 14: Stage 2 is ADMITTED, then the parent-receipt publisher is handed the wrong candidate path, and Stage 3 cannot be admitted

- **Status:** OPEN (2026-09-13)
- **Lane:** BOOT-13, measured on `build/bootstrap-boot13b` (canonical
  `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=llvm
  --mode=dynload --jobs=10 --stop-after-stage2`), branch
  `work/bootstrap-full-10-2026-09-12` at `8b2516a6477`
  (origin/main + BOOT-10/11 fixes + the merged site-12 fix `cb0ce4f16fe` + PR #800's
  site-13 fix + BOOT-13's declare-prototype fix).
- **Severity:** the Stage-2 blocker that SUCCEEDS site 13
  (`stage2_cross_module_call_mangling_asymmetry_undefined_symbol_2026-09-13.md`,
  now closed). It is not caused by that fix — it was masked by it: no
  `--stop-after-stage2` run in this fan-out (BOOT-4..BOOT-12) had reached Stage-2
  admission before, so this post-admission step had never executed in any of them.
- **Not a compiler defect.** This is entirely in the bootstrap shell driver.

## Stage 2 really is admitted

`build/bootstrap-boot13b/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env`:

```
schema=simple-bootstrap-stage2-admission-v2
status=admitted
candidate_path=/home/yoon/dev/simple-boot13/build/bootstrap-boot13b/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple
candidate_sha256=d19daa8c090c2a30ec6f56304ea354c947edc870c822235f97b97b3d30e0d1ae
admission_identity=c5af075f469dafb0c57f808999d4b8dc8f80434a6e6f99e4f0205d61c1388020
checks_executed_at_admission=1
```

and `stage2-receiver.log` ends:

```
bootstrap_stage2_struct_receiver=PASS
bootstrap_stage2_positional_stage3_route=PASS
```

with `grep -c 'undefined symbol' stage2-receiver.log` = **0**. The canonical
`build/bootstrap-boot13b/stage2/aarch64-unknown-linux-gnu/simple` exists
(152289464 B, sha256 `d19daa8c090c2a30ec6f…` — the same bytes).

## The measured cause — one path argument, two different files

`bootstrap-from-scratch.sh:3206-3221` (inside the
`bootstrap_stage2_trust_root -eq 1` branch that `--full-bootstrap` turns on) calls:

```sh
sh "${repo_root}/scripts/bootstrap/publish-stage2-parent-receipts.shs" \
  "$(absolute_path "${stage2_bin}")" \
  "${stage2_admission_receipt_absolute}" \
  ...
```

`stage2_bin` is `${output_dir}/stage2/${PLATFORM}/simple` (line 2762). But
`publish-stage2-parent-receipts.shs:44` asserts, under `set -eu`:

```sh
[ "$(field candidate_path)" = "$candidate" ]
```

and the admission receipt's `candidate_path` is the IMMUTABLE ADMITTED COPY,
`${stage3_provenance_dir}/stage2-admitted/simple` (`stage2_admitted_bin`, line
2510) — a different path holding the same bytes. Measured directly:

```
receipt candidate_path:      .../build/bootstrap-boot13b/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple
publisher arg (stage2_bin):  .../build/bootstrap-boot13b/stage2/aarch64-unknown-linux-gnu/simple
equal? NO
```

**Pinned by tracing the real publisher, not inferred from reading it.** Five
`[ -f ] && [ ! -L ]` / `bootstrap_stage3_canonical_file` guards and four `field`
comparisons run before this one under `set -eu`; all of them pass. Re-running the
script with `sh -x` and the eight arguments `bootstrap-from-scratch.sh` passes
(read-only — the script writes nothing before the assertions) exits `rc=1` with
this as the LAST assertion executed:

```
+ [ 1 -eq 1 ]
+ [ simple-bootstrap-stage2-admission-v2 = simple-bootstrap-stage2-admission-v2 ]
+ [ 1 -eq 1 ]
+ [ admitted = admitted ]
+ [ 1 -eq 1 ]
+ [ /home/yoon/dev/simple-boot13/build/bootstrap-boot13b/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple = /home/yoon/dev/simple-boot13/build/bootstrap-boot13b/stage2/aarch64-unknown-linux-gnu/simple ]
```

The assertion fails, `set -e` exits, and the caller prints:

```
error: could not publish producer-bound Stage 2 parent receipts
```

This is deterministic and fires on EVERY successful Stage-2 admission under
`--full-bootstrap`, so `build/.../stage2/<triple>/` is left with the compiler and
no `stage2-sanity.receipt` / `stage2-provenance.receipt` beside it.

## Consequence: Stage 3 cannot be admitted

`scripts/check/lib/bootstrap-planner-admission-bound.shs:147` requires
`parent_stage2_sanity_path` and `parent_stage2_provenance_path`. With the
receipts absent:

```
sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
  --target=//bootstrap:stage3 --reason=verify-landed-compiler-fix \
  --parent-compiler=.../build/bootstrap-boot13b/stage2/aarch64-unknown-linux-gnu/simple ...
producer rc=64
bootstrap-admission-error: parent-stage2-sanity-unavailable
```

so Stage 3/4 is blocked on this alone, not on any compiler behaviour.

## Secondary finding (documentation, not a defect)

`$S/boot4/stage3.sh` and its descendants pass `--reason=self-host-convergence-check`
for `--target=//bootstrap:stage3`. That pairing is **not** in the allowlist
(`bootstrap-planner-admission-bound.shs:105-116`): it is a `//bootstrap:stage4`
reason. It answers `bootstrap-admission-error: typed-reason-not-allowed-for-target`
(rc 64). For a stage3 admission after landing a compiler fix the allowed reason is
`verify-landed-compiler-fix`. Every lane that copied that script has been passing an
invalid reason; it simply never got far enough to matter before.

## Fix sketch (not applied here — out of this lane's scope)

Pass `stage2_admitted_bin` (the path the receipt names) as the publisher's
`CANDIDATE`, or record `stage2_bin` in the receipt. Either way the two must be
derived from one variable; the assertion itself is correct and should stay
fail-closed.
