# Stage 3 is hard-blocked on Stage-2 admission (2026-08-31, aarch64-apple-darwin)

Status: BLOCKED — not a defect in the Stage-3 lane. Investigation + pre-staged runbook.

## 1. Stage-3 entry contract (both lanes)

### Lane A — `--stop-after-stage3`
`scripts/bootstrap/bootstrap-from-scratch.sh:386-393` — excludes resume/full-cli/
deploy/release/diagnostic and requires `--mode=dynload`.
`:409-424` — the trust-root receipt exception is granted **only** to
`--stop-after-stage2 --full-bootstrap`. Every other path, `--stop-after-stage3`
included, falls to the `elif` at `:417` and exits **64** with
`bootstrap-policy-error: reason-receipt-required`.
`:432-437` — receipt `target` must be exactly `//bootstrap:stage3`.
`:438-441` — `bootstrap_planner_v2_verify <receipt> <root>` must pass.

### Lane B — `--resume-stage3-from-admitted=<output>`
`bootstrap-from-scratch.sh:501-510`: mutually exclusive with rebuild/deploy/
diagnostics, `--jobs=1` only, then `exec resume-stage3-from-admitted.sh`.
That script (`:25-31`) re-verifies the same v2 receipt and re-checks
`target == //bootstrap:stage3`, then at `:178-194` requires ALL of these to exist
as canonical non-symlink files under `<output>/stage3/<platform>/`:

    stage2 = <output>/stage2/<platform>/simple
    admitted = stage3/<platform>/stage2-admitted/simple
    stage2_admission = stage3/<platform>/stage2-admitted/admission.env
    seed, stamp (simple.inputs.sha256), libsimple_native_all.a
      under stage3/<platform>/stage2-runtime-authority/
    stage2-sanity.env, stage2-receiver.env, stage2-receiver.log,
    stage2-command.transcript, logs/<platform>/stage2-native-build.log,
    source-inputs-before.txt, git-state-before.env,
    runtime-origin-{before,after}.txt, runtime-admitted.txt,
    tool-authority-before.txt
    + dirs: stage2-runtime-authority/, stage2-native-cache/

## 2. How a receipt is legitimately produced

You do **not** hand-compute the four sha256 values, and you do **not** run
`bootstrap_receipt_main.spl` yourself. The error message at `:417` quotes the
*inner* command the producer execs. The real producer is:

    sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
      --target='//bootstrap:stage3' \
      --reason=verify-landed-compiler-fix \
      --parent-compiler=build/bootstrap/stage2/aarch64-apple-darwin/simple

Where each digest comes from (`produce-bootstrap-planner-admission-v2.shs`):
- `parent_compiler_sha256` — `:150` sha256 of the Stage-2 binary itself.
- `runtime_snapshot_sha256` — `:165-169` sha256 of a sorted
  `find src/runtime -type f ! -path './vendor/*' | sha256sum` manifest.
- `planner_source_closure_sha256` — `:173-179` sha256 of a snapshot holding the
  planner source hash + its `extern fn` lines (the planner imports no modules).
- `planner_sha256` — `:213` sha256 of the planner binary built **by the Stage-2
  parent** via `native-build --entry-closure --entry src/app/cli/bootstrap_reason_planner.spl`.
- `cache_scope_key` = `sha256("<runtime_sha>:<closure_sha>")` (`:187`), and it
  names the admission directory — verified independently at
  `bootstrap-planner-admission-bound.shs` verify_structure.

Note the planner SOURCE is `src/app/cli/bootstrap_reason_planner.spl`
(pinned literally in `verify_structure`), not `bootstrap_receipt_main.spl`.
Allowed `//bootstrap:stage3` reasons: `bootstrap_planner_v2_reason_allowed`,
`bootstrap-planner-admission-bound.shs` — `seed-missing`, `seed-corrupt`,
`seed-target-unsupported`, `seed-cannot-parse-required-language-feature`,
`seed-cannot-lower-required-compiler-feature`, `bootstrap-runtime-abi-major-changed`,
`bootstrap-artifact-format-major-changed`, `bootstrap-core-interface-major-changed`,
`verify-landed-compiler-fix`.

## 3. Why Stage 3 can make ZERO progress today — hard prerequisite

Stage-2 admission failed and the binary was renamed
(`bootstrap-from-scratch.sh:2428`, `stage2-rejected/`):

    build/bootstrap/stage2/aarch64-apple-darwin/simple           MISSING
    build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected  sha 9050d3a8c1e387d54a5975a517637392b02f1cc1435ff7c1a44ffadaf7c1e7b8 (Aug 31 06:28)
    build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/ DOES NOT EXIST

Blocking cause (`stage3/aarch64-apple-darwin/stage2-receiver.env`, status=fail,
probe_exit=1; log tail):

    error: bootstrap MIR lowering: E-MIR-TYPE-Unknown: unreachable HirTypeKind
    disc=-1: 0 while lowering
    'compiler.common.module_path_naming._module_path_naming_text_index_of'

### Proof A — the stale Aug-24 receipt no longer verifies
    sh scripts/bootstrap/bootstrap-from-scratch.sh --validate-bootstrap-receipt \
      --stop-after-stage3 --bootstrap-receipt=build/bootstrap/stage3-admission.env \
      --backend=llvm
    -> bootstrap-policy-error: planner-admission-v2-unbound
       bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2   exit 64

Why: `verify_structure` loops over ten `<stem>_path` fields and calls
`bootstrap_planner_v2_canonical_file` + re-hash on each. The receipt's
`parent_compiler_path=.../stage2/aarch64-apple-darwin/simple` no longer exists,
and its recorded `parent_compiler_sha256=8cc20c89…` does not match anything on
disk. There is also `bootstrap_planner_v2_verify_parent_compiler_binding`, which
requires receipt-sha == produced-sha == consumed-sha at consumption time.

### Proof B — a fresh receipt cannot be minted
    sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
      --target='//bootstrap:stage3' --reason=verify-landed-compiler-fix \
      --parent-compiler=build/bootstrap/stage2/aarch64-apple-darwin/simple
    -> bootstrap-admission-error: parent-compiler-missing-or-not-canonical   exit 64

The producer's step 2 (`:97-142`) refuses any parent that is not under
`<output>/stage2/`, that lacks a passing `stage2-sanity.receipt` +
`stage2-provenance.receipt`, or whose sha does not equal both receipts'
`candidate_sha256`. This runs BEFORE the admission lock, so the failed attempt
left no side effects.

**Conclusion:** admission is a hard prerequisite, not a soft one. Stage 3 needs an
*admitted* Stage-2 binary in two independent places — the receipt chain
(producer step 2 + `verify_parent_compiler_binding`) and the resume lane's
required-inputs loop (`resume-stage3-from-admitted.sh:178-194`, which demands
`stage2-admitted/simple` and `stage2-admitted/admission.env`). No legitimate
receipt exists or can be produced until the `E-MIR-TYPE-Unknown` defect is fixed
and a Stage-2 run admits.

Not attempted, deliberately: restoring a stale binary into
`stage2/aarch64-apple-darwin/simple`. No byte-identical admitted copy of
`8cc20c89…` survives anywhere (`stage2-admitted/` is gone), so this would be
fabrication, not recovery.

## 4. Pre-staged runbook — run in order the moment Stage 2 admits

    # 0. no concurrent bootstrap
    pgrep -f bootstrap-from-scratch   # must print nothing

    # 1. preconditions: admitted parent present, shas agree
    P=build/bootstrap/stage2/aarch64-apple-darwin
    shasum -a 256 "$P/simple"
    grep candidate_sha256 "$P/stage2-sanity.receipt" "$P/stage2-provenance.receipt"
    # all three hex values must be identical, and
    #   'stage2-sanity: pass' + 'stage2-provenance: pure-simple' must be present

    # 2. mint the receipt (derives all four sha256s itself)
    sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
      --target='//bootstrap:stage3' \
      --reason=verify-landed-compiler-fix \
      --parent-compiler="$P/simple"
    # last stdout line: 'bootstrap-admission: produced <receipt>'  exit 0

    # 3. validate without executing (cheap, safe)
    sh scripts/bootstrap/bootstrap-from-scratch.sh --validate-bootstrap-receipt \
      --stop-after-stage3 --bootstrap-receipt=<receipt> --backend=llvm
    # 'bootstrap-policy: receipt-valid target=//bootstrap:stage3 ...' exit 0

    # 4a. Lane A — fresh Stage 3
    sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage3 \
      --mode=dynload --backend=llvm --bootstrap-receipt=<receipt>

    # 4b. Lane B — resume from an admitted Stage 2 (only if stage2-admitted/ exists)
    sh scripts/bootstrap/bootstrap-from-scratch.sh \
      --resume-stage3-from-admitted=build/bootstrap \
      --bootstrap-receipt=<receipt> --jobs=1 --backend=llvm
    # Pass --bootstrap-receipt, NOT SIMPLE_BOOTSTRAP_REASON_RECEIPT. The receipt
    # gate at bootstrap-from-scratch.sh:417 tests the FLAG variable and fires
    # 'reason-receipt-required' (exit 64) long before the exec at :510. The
    # script exports SIMPLE_BOOTSTRAP_REASON_RECEIPT itself (:444-445) only
    # after the receipt verifies, which is what resume-stage3-from-admitted.sh
    # then reads at :24-31. Setting that env var by hand is both insufficient
    # (the flag gate still refuses) and unnecessary.

## 5. Where the real diagnostic lives when Stage 3 says UNDIAGNOSABLE

    build/bootstrap/stage3/aarch64-apple-darwin/stage2-receiver.log   (Stage-2 probe)
    build/bootstrap/stage3/aarch64-apple-darwin/stage3-sanity.env
    build/bootstrap/stage3/aarch64-apple-darwin/stage3-native-build-status.env
    build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log

`resume-stage3-from-admitted.sh:78-130`
(`bootstrap_stage3_resume_effective_status`) classifies a shell-status-0 run
that hides a crashed worker by grepping the log for
`^error: native-build worker exited with code ` — worker status `4294967295`
means signal-or-wait-failure, NOT SIGSEGV.

## RESOLVED 2026-08-31 — Stage 2 ADMITTED

The bootstrap now exits `rc=0` with "Stage 2 admitted; stopping before Stage 3 as
requested." Verified N=10: `rc=0` 10/10, `lines=12` (non-vacuous) 10/10,
`bootstrap_stage2_struct_receiver=PASS` 10/10.

Nine defects were fixed to get here: seed positional entry; 3x Stage-2 SIGSEGV
chains; `rt_heap_ref_wellformed` lost to a stale-snapshot clobber; `(24<<32)`
LocalId corruption from an un-unwrapped `LocalId?`; cross-file trait no-op
shadowing; MC/DC probes emitted with no runtime backing; text `+` merged as an
array; the stolen `unwrap` making every call-result return emit `ret 0`; and
`print` not newline-terminating.

Stage 3 is no longer blocked by admission. It requires its own planner-admission-v2
receipt with typed reason `verify-landed-compiler-fix` (target `//bootstrap:stage3`),
produced by `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`.
Stage 4 needs a DIFFERENT reason -- one of `self-host-convergence-check`,
`release-trust-verification`, `diverse-double-compilation`.
