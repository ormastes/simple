# Lane EVD — shared fail-closed evidence receipt (master plan §21.4, lane A11)

## Status: DONE (unit module + spec landed, not committed)

## What landed

- `src/lib/nogc_sync_mut/spec/evidence_receipt.spl` (new, no name collision —
  sibling of `condition.spl`/`decorators.spl`/`env_detect.spl`/`feature_doc.spl`
  in the `std.spec` package):
  - `EvidenceReceipt` struct with exactly the §21.4 field list: `commit`,
    `source_digest`, `compiler_digest`, `image_digest`, `target`, `firmware`,
    `machine_or_qemu`, `test_id`, `test_version`, `start_time`, `duration`,
    `result`, `metrics`, `logs`, `artifacts`, `failure_reason`.
  - `RuleOutcome` / `VerifyOutcome` plain outcome structs (no cross-module
    `Result.Ok/Err` — those don't resolve reliably from an imported method
    body per the landmine list).
  - Pure verification functions, all IO parameterized in (no IO inside the
    module itself):
    - `receipt_artifact_present(receipt, path_exists: bool)` — FAILs
      `missing_artifact` when `artifacts == ""` (nothing declared) or when
      `path_exists` is false (declared but absent on disk).
    - `receipt_artifact_fresh(receipt, artifact_mtime, run_start)` — FAILs
      `stale_artifact` when `artifact_mtime < run_start` (artifact predates
      the run it's supposed to be evidence for).
    - `receipt_execution_honest(receipt)` — FAILs `hosted_fallback_in_baremetal`
      when `target == "bare_metal"` and `machine_or_qemu == "hosted_fallback"`;
      FAILs `interpreter_fallback_in_native_perf` when
      `target == "native_perf"` and `machine_or_qemu == "interpreter_fallback"`.
    - `receipt_arch_supported(receipt)` — FAILs `unsupported_arch_claims_pass`
      when `machine_or_qemu` is `"unsupported"`/`"blocked"` but `result ==
      "PASS"`. Honestly reporting `result: "unsupported"`/`"blocked"` for the
      same machine value PASSES this rule (it is not counted as a green
      result, but it is not a rule violation either).
    - `receipt_verify(receipt, path_exists, artifact_mtime, run_start)` — runs
      all four rules in order, fail-closed, returns the first failing rule +
      its distinct reason; only passes when every rule passes.
  - `receipt_to_sdn(receipt) -> text` — plain `+` string concatenation, no
    brace-literal template (SDN block braces + Simple's `}}` collapse +
    `{name}` interpolation would corrupt a literal-brace approach).
  - Design note: no extra fields were added beyond the §21.4 list. The
    honesty/arch-support rules are derived purely from the relationship
    between `target` (declared execution class: `bare_metal`, `native_perf`,
    ...), `machine_or_qemu` (what actually produced the result: `board:...`,
    `qemu:...`, `hosted_fallback`, `interpreter_fallback`, `unsupported`,
    `blocked`), and `result`.

- `test/01_unit/lib/spec/evidence_receipt_spec.spl` (new dir + file): 9
  examples across 6 `describe` blocks — full honest receipt, missing
  artifact (declared-but-absent + nothing-declared), stale artifact, hosted
  fallback in bare-metal, interpreter fallback in native-perf, unsupported
  arch claiming PASS (fail) vs. unsupported arch honestly reporting
  `unsupported` (pass).

## Spec verdict

Ran via the repo recipe (`bin/simple` deployed seed hangs on `simple test`):

```
mkdir -p /tmp/evd/bin
cp bin/release/x86_64-unknown-linux-gnu/simple /tmp/evd/bin/evdjob
cp src/compiler_rust/target/bootstrap/simple /tmp/evd/bin/simple_seed
timeout 240 /tmp/evd/bin/evdjob run test/01_unit/lib/spec/evidence_receipt_spec.spl
```

Final verdict: **9 examples, 0 failures** (printed per-`describe` as 2+2+1+1+1+2,
all green). One benign `[gc-warning] Higher-layer module 'std.nogc_sync_mut.spec'
... imported in restricted context (family: nogc_async_mut)` line — pre-existing
GC-layering advisory for the `std.spec` package generally, not caused by this
change, does not affect the pass/fail verdict.

## Fail-once calibration (deliberate-red oracle)

Per instructions, made `receipt_artifact_present` always return `_ok(...)`
(inserted an early `return _ok("artifact_present")` as the first line) and
reran the same command. Observed:

```
Evidence receipt: missing artifact = FAIL
  ✗ fails with a distinct missing_artifact reason when the file is absent
    expected ok to contain missing_artifact
  ✗ fails when no artifact is declared at all
    expected ok to contain missing_artifact

2 examples, 2 failures
```

All other describe blocks stayed green (5 of 6 blocks, 7/9 examples) — confirms
the oracle is wired to the real rule output, not a tautology, and that the
failure is isolated to the exact rule that was neutered. Reverted the early
return; reran; back to 9/9 green (verified above).

## Next increment: migrate inlined fail-closed helpers onto this module

Candidate consumers found (none touched this lane — out of exclusive-path
scope):

1. `test/01_unit/os/arch/duplicate_owner_spec.spl` (Stage S's landed guard —
   do not edit directly; a follow-up lane should own the migration). Has its
   own inlined `Then_no_duplicate_trees` / `shell_lines`-based hit-counting
   fail-closed pattern (not an evidence-receipt struct per se, but the same
   "must actually detect, verify with a deliberate-red oracle" discipline
   this module now generalizes).
2. `test/03_system/hardware/kv260_network_verification_gate_spec.spl` and its
   mirror `test/03_system/.spipe_matchers_kv260_network_verification_gate_spec.spl`
   — already assert on a `"missing_artifact_dir"` fail string inside a
   generated script; a good first real migration to `receipt_artifact_present`
   semantics.
3. `test/03_system/os/baremetal/feature/breakpoint_counter_profile_spec.spl`
   and `breakpoint_counter_target_adapter_spec.spl` — baremetal-target specs
   that plausibly need the hosted-fallback-in-bare-metal honesty check.
4. `doc/08_tracking/os/production_status.sdn` `evidence:` row (owner: "spipe
   sdn receipts", lane A11, maturity: partial, note: "fail-closed on
   missing/stale artifacts not yet universal") — once 2-3 real consumers
   migrate, flip this row's `maturity` to `partial` -> `production` and update
   the note to point at `std.spec.evidence_receipt` as the canonical owner.

No existing `evidence_receipt`/receipt-writer owner was found anywhere under
`src/lib` or `src/app` before this lane (checked via
`grep -rln "evidence_receipt\|receipt\|artifacts:" src/lib src/app --include="*.spl"`
— hits were all unrelated GPU/render/protocol "receipt" wire-format modules,
not an SDN evidence-receipt owner), so this module is a genuinely new,
non-duplicate owner.

## Blockers

None. Module is pure, IO-free, and unit-tested; ready for other lanes to
import via `use std.spec.evidence_receipt.{...}`.

## Not touched (out of scope)

- `test/01_unit/os/arch/duplicate_owner_spec.spl` — Stage S's file, per
  instructions.
- No commit/push performed — working copy only, per instructions.
