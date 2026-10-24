# Status-3 shard transaction omits the durable archive its own contract says archive callers require

- **Date:** 2026-10-24
- **Status:** OPEN — blocks the full bootstrap on `release/1.0.0`
- **Verdict:** **producer gap**, not an over-strict consumer
- **Files:** `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` (producer),
  `src/compiler/80.driver/driver_hir_archive_production_controller_v1.spl` (consumer)
- **Upstream cause:** the codec refusal recorded in
  `hir_codec_encodes_nil_non_optional_scalar_that_decode_refuses_2026-10-24.md`

## Symptom

With the module campaign now clearing (see
`stage2_admitted_but_compiler_test_matrix_blocks_managed_resume_2026-10-24.md`),
the Stage 2 compiler-test matrix fails one layer later. Two tasks fail
identically, with one shared cause:

```
task=compiler_cli_build|result=FAIL|status=1
task=test_runner_build|result=FAIL|status=1

[ERROR] phase 3 FAILED
[ERROR]   bounded HIR real source transaction omitted compact publication
error: in-process native-build: bounded HIR real source transaction omitted compact publication
```

The three `compiler_bootstrap_tests` / `interpreter_interpreter_tests` /
`loader_interpreter_tests` rows reporting
`UNSUPPORTED|status=full-cli-artifact-not-built` are **downstream consequences**
of the first task, not separate defects.

## The status contract

`DriverHirShardTransactionReceiptV1` (`driver_hir_pipeline_lowering.spl:117-122`)
carries `status: i64`, `archive: HirBodyArchiveV1?`,
`declaration_registration: MonoArchiveRegistrationReceiptV1?`. Its documented
status codes (`:118-119`, repeated at `:716-717`):

| status | meaning |
|---|---|
| 0 | validated cache hit |
| 1 | published full HIR |
| 2 | source diagnostic |
| **3** | **codec-refused UNCACHED** |
| < 0 | infrastructure/ownership failure |

## What the consumer does

`driver_hir_archive_production_controller_v1.spl:137-152` handles `status < 0`
(return false) and `status == 2` (poison + continue), then:

```simple
if receipt.archive == nil or receipt.declaration_registration == nil:
    mem_snapshot_abort()
    return production_fail_v1(driver, "bounded HIR real source transaction omitted compact publication")
val published = driver_hir_archive_journal_publish_v1(journal, driver.ctx, source_index, name,
    receipt.declaration_registration.unwrap())
```

**Status 3 is never handled**, so a codec-refused shard falls into this check.

## Why the consumer is RIGHT and the producer is wrong

The producer's own comment on the refusal path
(`driver_hir_pipeline_lowering.spl:795-800`) states the contract:

> (codec encode-reject / selfcheck / unstable roundtrip). The blob is not
> admitted as a cache entry. The caller records PASS+UNCACHED; this worker
> reclaims its module and the main build lowers the source again on a cache
> miss. **Archive callers still require their separate durable archive below.**

So the durable **archive** is explicitly SEPARATE from the **cache** entry, and
is still required for archive callers. The archive-production controller is an
archive caller. The codec-refused path nevertheless returns status 3 with
`archive`/`declaration_registration` unset, which violates that sentence.

Two fix shapes were considered and rejected, with reasons:

- **Treat status 3 as "done" and skip the journal publish.** Rejected: the
  controller's completeness check (`:173-175`) requires
  `journal.logical_order == schedule.logical_publication_order`, so a skipped
  publish fails a *different* way — `"bounded HIR actual complete
  visit/publication coverage differs"`. Skipping is not a fix, it is a
  relocation.
- **Relax the `archive == nil` check for status 3.** Rejected: that discards
  the durable archive the quoted contract requires, silently, for every
  codec-refused module.

The counters would also have to move: `:156-158` sets
`completed[source_index] = true` and bumps both `physical_done` and
`logical_done`, and `:173` requires `physical_done ==
schedule.layout_source_order.len()`. Any status-3 handling must satisfy that
too.

## Sibling consumer, for reference

`driver_hir_pipeline_lowering.spl:1252` — the non-archive shard consumer — does
handle it: `if shard_status == 1 or shard_status == 3: hir_shard_lowered =
hir_shard_lowered + 1`. And `driver_hir_shard_cache_stored_v1` (`:207`) is
`status == 0 or status == 1`, correctly excluding 3 from "cached". So the
codebase already distinguishes *lowered* from *cached*; only the archive
controller conflates "no cache entry" with "no archive".

## The upstream trigger

Status 3 fires on "codec encode-reject / selfcheck / unstable roundtrip". That
is the refusal documented in
`hir_codec_encodes_nil_non_optional_scalar_that_decode_refuses_2026-10-24.md`:
the encoder writes a nil sentinel for a nil NON-optional scalar with `w.ok`
still true, while 231 decoder sites reject that same byte, so such a module
encodes cleanly and can never decode. Fixing that asymmetry would remove the
status-3 occurrences driving this failure, which makes it the cheaper root fix
of the two if it holds for this module.

**Not established:** that the modules tripping this in the full-CLI build are
refused for that specific reason. The decode-step attribution is measured there;
the specific failing check inside decode is not.

## Not caused by the adjacent enum fix

Checked, because the timing invites the inference. The builtin-generic-enum-seed
fix (`register_builtin_enum_dual`, PR #4270) cannot be implicated: the compiler's
own compilation unit declares `enum Result<T, E>` at
`src/compiler/30.types/const_key_validator.spl:189`, so `Result` already got its
generic flag from the user-declaration path (`module_lowering.spl:998-1001`) when
compiling the compiler — that fix is a no-op for this build and only affects
standalone modules that rely on the builtin seed. For `Option` the change only
makes a guard *skip*, which is strictly more permissive. These two tasks were
also simply **never attempted** in the previous run, because the module campaign
failed first and later tasks were skipped; the failure is newly observed, not
newly caused.

## Next step

Make the codec-refused path honor the quoted contract: produce the durable
archive and the declaration registration for archive callers even when the cache
store is refused, so the controller's publication and its `:173` coverage check
both see a complete module. Alternatively, eliminate the trigger upstream by
fixing the encoder/decoder nil-scalar asymmetry.

Verification costs a full Stage 2 rebuild (~40 min on this host): the defect is
in the pure-Simple self-hosted driver and only takes effect in a rebuilt Stage 2
binary.

## CORRECTION 2026-10-24: the verdict above is WRONG — not a producer gap

This record concluded "**producer gap**, not an over-strict consumer", on the
strength of the producer comment at `driver_hir_pipeline_lowering.spl:795-800`
("Archive callers still require their separate durable archive below").
**Withdrawn.** Both the consumer check and the producer's status-3 behaviour are
correct. The defect is one layer below both, in the generated HIR decoder.

### What actually happens

`src/compiler/20.hir/generated/hir_codec.spl` decoded every non-optional scalar
as

```simple
val f = if raw == "N": nil else: flat_pool_parse_i64(raw)
if f == nil: r.reject_malformed("nil_in_non_optional_scalar")
```

**nil's immediate is 3**, so a genuine i64 `3` compares equal to nil and the
blob is refused. Measured against the Stage 2 compiler itself: `i64 3 -> nil`,
`i64 7 -> 7`; bool and text are fine. 231 such sites existed.

So the chain is: any module whose HIR carries a `3` in a non-optional scalar is
refused at decode -> the codec refusal sets `store_refused_codec` -> the shard
transaction returns **status 3** with no archive, exactly as designed -> the
archive-production controller fails closed, exactly as designed. Measured:
re-running `test_runner_build` with `SIMPLE_HIR_CACHE_SELFCHECK=1` gives
**259/259 modules `reason=decode`**, and a one-file hello-world probe on the
archive route reproduces in ~1 s.

The entry module named in the logs
(`src/app/cli/_CliMain/main_and_help.spl` for `compiler_cli_build`,
`src/app/test_runner_new/main.spl` for `test_runner_build`) is not special — it
is merely the first store attempted.

### Why the earlier reasoning went wrong

The producer comment is real and says what it says, but it describes the
*cache-entry vs durable-archive* distinction, not this situation. I read a
true sentence as an explanation of the observed failure without establishing
that the refusal itself was legitimate. It was not: the codec was refusing
every module for a reason that has nothing to do with archives.

The two fix shapes rejected above remain correctly rejected, and for the reasons
given — they would both have papered over a universal decode failure.

### Corroboration this should have been found by

`doc/08_tracking/bug/hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md`
— "HIR codec writes integer 3 and bool true as nil under a stage-2 compiler" —
is the **encoder half of this exact hazard**, fixed 2026-10-10
(`hir_codec_support.spl:362-383`). The decoder half was never done. That record
existed the whole time and names the mechanism outright.

### Why only the archive route shows it

The archive-production route requires `SIMPLE_BOOTSTRAP != "1"` plus a runtime
bundle and strict tool authority (`driver_orchestration.spl:92-105`,
`native_tool_authority_v1.spl:160-166`). The compiler-test matrix sets exactly
that (`bootstrap-phase-verification.shs:878`, `:892`, `:921-923`), whereas
Stage 2/3/4 builds run with `SIMPLE_BOOTSTRAP=1`
(`bootstrap-from-scratch.sh:3630`, `:4157`, `:2691`) and take the non-archive
route, which tolerates a codec refusal (`driver_hir_pipeline_lowering.spl:1252`
counts status 3 as lowered). That is why Stage 2 itself builds 1,487 modules
happily while the full-CLI build inside the matrix cannot complete one.

### The fix

In the generator (`src/app/compiler_schema/codec_gen.spl`, `_emit_dec`): refuse
the wire nil sentinel on the **raw text**, before any typed local exists, then
bind a plain `i64`/`bool`/`text`. No decoded scalar is ever compared against
nil. `_emit_nil_scalar_reject` and its two call sites are deleted as redundant.
Wire format unchanged; the encoder is untouched. 290 reject sites after
regeneration (231 plus 59 optional-inner scalars that previously yielded
`Some(nil)`), and zero `== nil` tests on decoded scalars.
