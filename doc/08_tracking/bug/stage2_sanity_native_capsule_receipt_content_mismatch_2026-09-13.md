# macOS Stage 2 sanity: the smoke unit fails native-capsule receipt verification (2026-09-13)

Status: ROOT CAUSE FOUND. The receipt path is FIXED (PR #708 restored the
fix PR #702 had clobbered; PR #710 split the gate). The remaining defect is
in CODEGEN, not in this file, and now has a measured reproducer: run 9
printed `field=34363944961:runtime=632` for the same object in the same
process. See "Run 9" below. Original run-8 framing retained for history:

> This is the CURRENT macOS Stage 2 blocker (run 8) and it is a
DIFFERENT defect from the one it replaced. It fires EARLIER than run 7's — in
`native_compile`, before any link — so run 7's `Linking failed: nil` site is no
longer reached.

## Verdict, verbatim (run 8)

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: native capsule collection failed -- module, tag and detail follow
scripts.check.cert.redeploy_gate.fixtures.hello_world
native-capsule-receipt-invalid
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s) — ERROR: scripts.check.cert.redeploy_gate.fixtures.hello_world
error: Stage 2 bootstrap compiler sanity failed
warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
```

Rejected Stage 2 candidate (preserved, not deployed):
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`

Stage 2 itself built clean again; the failure is entirely in the smoke build the
candidate performs.

## What the numbers say

`driver_native_capsule_result_reason_v1`
(`src/compiler/80.driver/driver_aot_native_output.spl:855-896`) rebuilds the
expected receipt text

```
native-capsule-result-v1\n{capsule_identity}\n{object_path}\n{fp.size}\n{fp.content_hash}\n
```

and compares it byte-for-byte with the receipt the compile step wrote. **Both
sides are 1648 bytes and they differ**, which by that function's own comment
localises the fault to CONTENT, not truncation. The only fields that can differ
at equal length are the fixed-width ones: `fp.size` (unlikely to keep the length)
and `fp.content_hash` (a fixed-width digest — the obvious candidate). That would
mean the object file on disk hashes differently at verification time than when
the receipt was written, or one of the two hash computations is wrong in the
stage-2 NATIVE binary while being right in the interpreter.

## The differing field, measured

The written receipt is on disk; its 4th line — `fp.size` — reads

```
37196932097
```

for an object file that is **632 bytes**. The 5th line, `fp.content_hash`, is
`76e16357e568394bbe191e9c9f3633f4ba8dd5c5bf8b97d725f5474936eb327a`, which is
byte-for-byte what `shasum -a 256` gives for that object. So the hash is right
and **the size is garbage** — a value around 0x8_A8xx_xxxx, the shape of a
pointer or an undecoded box, not a file size. Both sides are 1648 bytes because
both garbage values have the same digit count; they differ because the garbage
is not stable between the write and the verify.

`FileFingerprint.size` is filled by `incremental_file_size` ->
`extern rt_file_size` (`driver_build/incremental.spl:60,639`), and it is read
back through an optional bind:

```
val object_fp = FileFingerprint.from_file(capsule.object_path)
if val fp = object_fp:
    expected = "native-capsule-result-v1\n...\n{fp.size}\n{fp.content_hash}\n"
```

`rt_file_size` itself is NOT the defect: a two-call native probe built by the
seed tier (`extern fn rt_file_size(path: text) -> i64`, printed twice) returns
the true size, twice, on this host. The suspicion is therefore the
**optional-bound scalar FIELD read** (`if val fp = object_fp: ... fp.size`) in
the stage-2 native binary — the same family as the earlier optional-bound scalar
field divergence — with `content_hash`, a `text` field beside it, surviving
intact.

Not yet established, and the next steps:
1. dump both texts (not just the lengths) for this one unit and diff them — the
   differing FIELD is the whole diagnosis and the current message deliberately
   withholds it;
2. if it is `content_hash`, re-hash the object outside the compiler and see which
   of the two sides is wrong;
3. check whether `FileFingerprint.from_file` / the hash helper is another
   native-vs-interpreter divergence, which is the family this lane keeps hitting
   (`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`).

## Relationship to the link-nil blocker

Run 8 carried the link-payload hardening (PR #702: every `"" == ok` status on the
darwin link path is site-named and reported unconditionally, and the orchestrator
refuses to format a nil into `Linking failed: ...`). That hardening is **not
disproven and not proven** by this run: the failure now stops before the linker
is reached, so no `[linker-wrapper]` line and no `Linking failed:` line appears
at all. The link-nil record stays OPEN until a run gets past capsule collection.

## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap \
   --mode=dynload --jobs=half
```
from a worktree with a virgin evidence root. ~35 min with a cold Rust seed.

## Related

- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md`
- PR #702

## ROOT CAUSE (2026-09-13): the fix was already written, and PR #702 reverted it

Run 8 did not disprove anything — **it executed a compiler built without the
fix.** Commit `54660c1a0d4` ("fix(driver): say HOW the AOT diagnostic was lost",
PR #702) is a **stale-snapshot clobber** of
`src/compiler/80.driver/driver_aot_native_output.spl`. It is a net
**+22 / -100** on that one file, and of its 22 added lines only 11 are its own
work (the `diagnostic_note` interpolation); the other 11 are the OLD code it
restored. What it reverted:

- `0e437dec9b1` (PR #677) — the `rt_file_size` extern and all three receipt
  sites composing line 4 from the runtime instead of `fp.size` / `materialized.size`;
- `418399c2d84` (PR #670) — the `first-diff-line=<n>:expected=…:actual=…`
  diagnostic, which is literally what this record's "next step 1" asked for.

Evidence: `git log -S'rt_file_size(capsule.object_path)' -- <file>` names
`54660c1a0d4` as the removing commit; `git log 0e437dec9b1..54660c1a0d4^ -- <file>`
is EMPTY, so #702's parent for this file was #677's commit and nothing else
intervened. `git show 54660c1a0d4 --stat` shows exactly one file touched, so
the clobber is scoped to this file and nothing else was lost.

This is the `.claude/rules/vcs.md` § "Sync must never clobber" failure mode,
disclosed here as that section requires. The receipt-verifier spec
`test/01_unit/compiler/driver/native_capsule_result_receipt_spec.spl` was left
RED on `main` by the clobber (its `first-diff-line=4` assertion had nothing to
assert against) — a standing signal that went unread.

## Fix

1. **Restored** both reverted commits' content, preserving #702's own
   `diagnostic_note` addition. Verified: zero `fp.size` / `materialized.size`
   READS remain (the 3 grep hits are the explanatory comments), and the
   `first-diff-line` verifier is back.
2. **Added a fail-closed plausibility gate**,
   `driver_native_capsule_receipt_size_reason_v1(field_size, runtime_size)`.
   Both receipt sites already take the written size from `rt_file_size`; the
   `fp.size` struct-field read of the same quantity is now passed in purely as a
   **canary**. `FileFingerprint.from_file` sets `size = incremental_file_size(path)
   -> rt_file_size(path)` (`driver_build/incremental.spl:60,640`), so the two are
   the same quantity and equality is a sound invariant, not a vacuous one.
   The gate fails closed on a negative stat sentinel, on any value >= 2^40 (a
   pointer, never a byte count), and on field/runtime divergence — turning the
   codegen miscompile into a named failure at the site that notices it
   (`capsule-receipt-size-implausible:field=…:runtime=…`) instead of an opaque
   `receipt-content-mismatch` far away.

Spec: 4 new examples in
`test/01_unit/compiler/driver/native_capsule_result_receipt_spec.spl`
("native capsule receipt size plausibility"), including the verbatim run-8
value 37196932097 against a 632-byte object. Measured on the Rust seed:
**4 examples, 0 failures**; the restored `first-diff-line=4` example also passes.

**Pre-existing RED, not caused by this change and left RED per
`.claude/rules/testing.md`:** the spec's first example calls
`driver_native_collect_capsule_result_v1` with 5 arguments (a leading
`receipt_ctx()`) while the function takes 4
(`driver_aot_native_output.spl:1033`). Byte-identical at `HEAD` before this
change, so it is spec/impl arity drift predating this lane.

### Which half of the gate is load-bearing

**The `field != runtime` inequality is the check that fires here. The 2^40 bound
is a backstop and would NOT have caught this host's pointers.** The three
measured garbage values — 37196932097 (run 8), and 53657758209 / 53657761281
(PR #677's two same-process reads) — are all ~3.7e10 to 5.4e10, i.e. **below**
2^40 = 1099511627776. Tagged aarch64 heap addresses on this host land two orders
of magnitude under that bound. Nobody may later rely on the magnitude test
alone; it exists only for a value so large it cannot be anything but a pointer,
and this defect's pointers are not that large.

## Run 9 (2026-09-13) — the canary fired, and it is the mode-matched reproducer

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root, worktree `agent-a87b4c8362f754818`, carrying PR #708. Stage 1
built and admitted; Stage 2 built its 834-unit closure clean; the failure is
again entirely inside the smoke build the candidate performs — **but it is a
different failure, and it names the defect exactly.** Verbatim:

```
error: AOT compile error -- unit, reason and lengths follow on the next lines
error:   unit (bare):
scripts.check.cert.redeploy_gate.fixtures.hello_world
error:   reason (bare):
capsule-receipt-size-implausible:field=34363944961:runtime=632:<...>/object.scripts.check.cert.redeploy_gate.fixtures.hello_world.o
error:   name-len=53 reason-len=403
```

`receipt-content-mismatch` **does not appear.** What this establishes, on the
real Stage-2 artifact in the real build mode — which F45's single-entry T1
probes could not reproduce:

1. **`rt_file_size(path)` is CORRECT under `--mode=dynload --entry-closure`.**
   It returned **632**, the true byte count of the object.
2. **The optional-bound scalar field read is MISCOMPILED in that same binary,
   in the same function, on the same file.** `fp.size` returned
   **34363944961** = `0x8_0010_2001`. The same log's earlier line
   `[DEBUG] Creating codegen adapter for backend=<enum@0x80101efe0>` shows a
   live heap object at `0x8_0101_efe0` — the same `0x8_…` address space. It is
   a tagged heap pointer, not a byte count.
3. Therefore **PR #677's remedy is right and is now proven end to end**: going
   to the runtime for the value produces the correct number where the struct
   field produces a pointer. The receipt itself is sound in run 9; nothing
   garbage was written.
4. The 2^40 backstop did **not** fire (34363944961 is ~3.1% of 2^40). The
   `field != runtime` inequality is what caught it, as recorded above.

**The build stopped only because the canary is fail-closed.** Without it, run 9's
receipt would have been written and verified correctly from `rt_file_size` on
both sides. The defect is no longer in the receipt path; it is in codegen, and
it now has a measured, reproducible witness with both values named.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted. Rejected candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`.

## Run 10 (2026-09-13) — capsule collection PASSES; this record's blocker is cleared

Same command, virgin evidence root, carrying the split gate (PR #710). Stage 1
admitted; Stage 2 built its closure clean; **the smoke build got past native
capsule collection for the first time in this chain.** No
`receipt-content-mismatch`, no `native-capsule-receipt-invalid`, no
`capsule-receipt-size-implausible`. The receipt was written and verified.

The advisory canary fired **three times**, and the three lines are the clearest
statement of the codegen defect this chain has produced:

```
[receipt-size-canary] optional-bound scalar field read miscompiled: field=51251192833:runtime=632 path=<...>.o
[receipt-size-canary] optional-bound scalar field read miscompiled: field=51251189761:runtime=632 path=<...>.o
```

Same file, same process, **different field values 3072 bytes apart**
(0xBEF7A1801 vs 0xBEF7A0C01) — the identical stride PR #677 measured
(0xc7e407601 vs 0xc7e406a01). A fresh box per read. Meanwhile `runtime=632` is
stable and correct on every one of the three reads. The struct-field read is
non-deterministic; the runtime call is not.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted. Rejected candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`.

### The blocker moved to the run-7 link site

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
```

This closes the open question in
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`: run 8 could
not reach the link, so PR #702's hardening was neither proven nor disproven.
**It is now reached, and it is RED.** Two facts for that record, not this one:

1. the orchestrator's refusal to format a nil into `Linking failed: ...` WORKS —
   the message names the condition instead of printing a bare nil;
2. but **the `[linker-wrapper]` prints the message points at do not appear in
   the log at all** (`grep 'linker-wrapper'` matches only the error line that
   references them). The hardening's own diagnostic channel is empty, so the
   failing site is still unnamed. That is the next thing to fix, and it belongs
   to that record.

### Status of THIS record

The receipt path is fixed and proven. What remains is a **codegen** defect —
optional-bound scalar (`i64`) field reads under `--mode=dynload --entry-closure`
return a fresh tagged heap pointer per read — with a standalone reproducer that
needs no bootstrap:

- binary: the run-9/run-10 `simple.rejected` Stage 2 candidate
  (run 9 copy preserved, sha256
  `a9e61220cb17e438a959083ebb4554138dd2bc3bd333ea8de0ee1ce6c6aeb736`,
  139044728 bytes);
- input: `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`;
- signal: the `[receipt-size-canary]` line, which names both values.

**Not established, and deliberately not guessed:** the compiler file:line that
lowers this read. A mode-flag bisect (dynload vs static, entry-closure on/off,
jobs) costs roughly one full Stage 2 build per variant and did not fit the time
budget of this lane. F45's single-entry probes do not reproduce it, and a
single-entry probe built against a stale Stage 1 snapshot fails earlier for an
unrelated reason (`unknown extern rt_env_vars`), so it is not a shortcut. The
next session should bisect from the reproducer above rather than re-derive it.
