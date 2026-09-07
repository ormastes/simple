# Stage 2 sanity fails at `native-capsule-source-mutated` on hello world, and the reason is nondeterministically unreportable

**Status:** ROOT-CAUSED and WORKED AROUND 2026-09-07; the underlying native-codegen field-binding defect is OPEN.
found alongside it are fixed (see "What was fixed").
**Component:** `src/compiler/80.driver/driver_aot_native_output.spl`,
`src/compiler/80.driver/driver_types.spl`,
`src/compiler/80.driver/driver_build/build_outcome.spl`
**Found via:** `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`
(aarch64-unknown-linux-gnu), 2026-09-07
**Supersedes the "one observation" note in**
`doc/08_tracking/bug/stage3_selfhost_parser_rejects_arrow_match_arms_2026-09-06.md:222-233`

## Symptom

Stage 2 **builds successfully** (`Build complete: 834 compiled, 0 cached, 0
failed`, `Time: 662.7s compile + 57.3s link = 720.0s total`) and then fails its
own sanity gate. The failing sub-check is the `hello_world_positional` probe of
`candidate_frontend_smoke`
(`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:357-397`).
Real error, from `stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
(**not** from `stage2-native-build.log`, which is a clean success log):

```
[build] native_cache 1/1 step 5/6 +3658ms dt=1ms complete
[build] native_compile 0/1 step 5/6 +3658ms dt=0ms scripts.check.cert.redeploy_gate.fixtures.hello_world
===== build outcome summary =====
OK=0
ERROR=1
ERROR: 1 unit(s)
  - scripts.check.cert.redeploy_gate.fixtures.hello_world
      reason: native-capsule-source-mutated:scripts.check.cert.redeploy_gate.fixtures.hello_world
===== end build outcome summary =====
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)
```

## Reproducer (3 seconds, no bootstrap)

```sh
C=<stage2 binary>
SIMPLE_BINARY=$C SIMPLE_BIN=$C SIMPLE_BOOTSTRAP_DRIVER=$C \
SIMPLE_FRONTEND_DELEGATE=$C SIMPLE_FRONTEND_DELEGATED=1 \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_EXECUTION_MODE= \
SIMPLE_NATIVE_BUILD_FORCE_WORKER=0 SIMPLE_BOOTSTRAP=0 SIMPLE_LIB=$PWD/src \
  "$C" native-build --backend llvm --runtime-bundle core-c-bootstrap \
  --entry-closure --cache-dir <fresh> --mode one-binary \
  scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output <out>
```

Reproduced on three independently built Stage-2 binaries:
`4d0c20ba36add1d5bb3407852480ad83143084bbf8c4ed42e8a36d5ad9feab7c`,
`39330f638ee8c632c47f4a19fb6d29e1c3253e66e97f9b5e3969df16c5039f30`,
`a11d1c069e8957287fc0e11eaf48181f75dd4d5fb00b0955ee4f3f33ee848a95`.

It is **not** lane-specific: it reproduces with a default `--output`, a default
cache dir, no `SIMPLE_CACHE_SCOPE`, with a relative AND an absolute entry path,
and with the fixture copied to an unrelated directory
(`reason: native-capsule-source-mutated:build.capsule_repro.sub.hw`). The
lane-isolation hypothesis in the 2026-09-06 record is therefore ruled out.

`--entry` instead of a positional entry "passes", but that is **not a control**:
`run_native_build_bootstrap` routes `--entry` (without `SIMPLE_BOOTSTRAP_STAGE4=1`)
to `run_rt_native_build`, i.e. the Rust seed FFI, which never executes this
pure-Simple code (`src/app/cli/bootstrap_main.spl:381-396`).

## Where the verdict comes from

`driver_native_collect_capsule_result_v1`
(`driver_aot_native_output.spl`) fires on either of two invariants:

```
if capsule.cache_source != "" and (
    capsule.source_identity == ""
    or driver_native_disk_source_identity(capsule.cache_source)
        != capsule.source_identity):
    return "native-capsule-source-mutated:{module_name}"
```

* `capsule.source_identity` = `sha256_text(source.content)` for the single
  `ctx.sources` entry whose `module_name` matches
  (`driver_types.spl`, `frozen_native_cache_source_identity_v1`), `""` if the
  match count is not exactly 1.
* `driver_native_disk_source_identity(path)` = `sha256_text` of
  `SourceFile.load(path).content`, `""` on `Err`.

## What is ruled out (evidence, not inference)

1. **Genuine on-disk mutation: NO.** Nothing writes the fixture during the run;
   the same failure occurs for a fixture copied to a private directory.
2. **Post-HIR source eviction (the obvious candidate): NO.** `evict_sources()`
   sets every `SourceFile.content` to `""` and is called from
   `driver_hir_pipeline_lowering.spl:433` (streaming HIR) and
   `driver_orchestration.spl:194` (low-memory). **Neither runs on this lane.**
   With `SIMPLE_COMPILER_PHASE_PROFILE=1` the repro emits no
   `phase3:streaming_source_reclaim`, no `phase2:source_reclaim` and no
   `phase1:streaming_preparse_source_reclaim`.
3. **Duplicate/alias module records: NO.** The same trace shows
   `phase1:load_sources:bulk:done logical=1`,
   `phase1:load_sources:owner_copy:done n=1`,
   `phase1:fingerprint:source idx=0 of=1 path=…hello_world.spl bytes=30` and
   `phase2:parse:closure:sources collected=1 unique=1`. Exactly one source, with
   its real 30 bytes, present at phase 1.
4. **The source-level semantics are correct.** Run interpreted under the Rust
   seed (`build/capsule-repro/hash_probe.spl`):

   ```
   len=30
   sha256_text(content)=2976a380c6fdfee06ca2b9452d65bc6a3514862c2a626d64e982503241ada42a
   sha256_text(empty)=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
   ```

   `sha256sum scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
   `= 2976a380c6fdfee06ca2b9452d65bc6a3514862c2a626d64e982503241ada42a` — the two
   sides of the comparison agree when the same code is interpreted.

**Verdict: FALSE POSITIVE, and compiled-code-specific.** Nothing mutates the
source; the compiled Stage-2 binary diverges from the semantics of its own
source in `sha256_text(source.content)` vs
`sha256_text(SourceFile.load(path).content)`. Which of the two sides is wrong is
NOW ESTABLISHED — see ROOT CAUSE below. (This paragraph is kept as written at the time; the answer is: the disk side is wrong.)

## ROOT CAUSE (established 2026-09-07, after the first revision of this record)

`driver_native_disk_source_identity` returns the sha256 of the **PATH STRING**,
not of the file's content, in the Stage-2-compiled compiler. Source says:

```
fn driver_native_disk_source_identity(source_path: text) -> text:
    match SourceFile.load(source_path):
        case Ok(source): sha256_text(source.content)
        case Err(_): ""
```

The `case Ok(source)` payload's `.content` read yields field 0 (`path`) instead
of `content`. `SourceFile` is `path, authored_path (defaulted), content,
module_name`.

Evidence — a first-ever compile of a module name, on Stage-2 binary
`a11d1c069e8957287fc0e11eaf48181f75dd4d5fb00b0955ee4f3f33ee848a95`, with the
new verdict text:

```
[native-compile-failed] build.capsule_repro.sub.hw_fresh_a: native-capsule-source-mutated:build.capsule_repro.sub.hw_fresh_a:cache_source=build/capsule-repro/sub/hw_fresh_a.spl:frozen=2976a380c6fdfee06ca2b9452d65bc6a3514862c2a626d64e982503241ada42a:disk=009f18fc41410f2512f4fc413689d7fa0f17b3cef6bbad4c1ab488994e1c170b
```

and the two inputs, measured:

```
$ sha256sum build/capsule-repro/sub/hw_fresh_a.spl
2976a380c6fdfee06ca2b9452d65bc6a3514862c2a626d64e982503241ada42a   <- frozen= (CORRECT)

$ printf 'build/capsule-repro/sub/hw_fresh_a.spl' | sha256sum
009f18fc41410f2512f4fc413689d7fa0f17b3cef6bbad4c1ab488994e1c170b   <- disk=  (the PATH)
```

Confirmed on a second, independent module: for
`build/capsule-repro/sub/hw_fresh_b.spl` the emitted `disk=` is `47d1543b17b10d26…`,
byte-identical to `printf 'build/capsule-repro/sub/hw_fresh_b.spl' | sha256sum`.

So the **frozen side is correct** and the **disk side is wrong**, and every
capsule verification on this lane compared a content digest with a path digest.
Interpreted under the Rust seed the same expression returns the correct content
digest (`build/capsule-repro/hash_probe.spl`), so this is a native-codegen
field-binding defect, not a source-level one.

## The "nondeterministic reason loss" in the first revision of this record was WRONG

It is not nondeterministic and it is not "leading statements of
`driver_native_record_module_failure` do not execute". Both claims were an
artefact of only ever re-running module names that had already been compiled in
this workspace.

The rule, measured: the **first-ever** compile of a given module name reports the
full reason (and the `print` in `driver_native_record_module_failure` fires); a
**repeat** run of the same module name reports
`reason: (none recorded — BUG in the producer: a non-OK unit must carry a
diagnostic)` and no print. A fresh `--cache-dir` does not reset it — the state
that survives is keyed by module name (`object_path = "{object_base}.{module_name}.o"`
plus its `.capsule-receipt`), outside the cache dir.

```
--- FIRST compile of a never-seen module ---
rc=1
      reason: native-capsule-source-mutated:...:frozen=2976a380...:disk=009f18fc...
--- SECOND run, same module ---
rc=1
      reason: (none recorded — BUG in the producer: a non-OK unit must carry a diagnostic)
```

That repeat-run path reaches `driver_native_record_module_failure` with an EMPTY
`detail` (or records through some path not yet identified) — a real, separate
observability defect, but a deterministic one with a named trigger. **Anyone
reproducing this must use a module name never compiled in that workspace, or
they will measure the empty-reason path and conclude the wrong thing.**

## Fix landed

`driver_native_disk_source_identity` (BOTH duplicate definitions, see below) now
reads the file directly with `_sffi_file_read_text` and hashes that, avoiding the
defective match-payload field read. This is also strictly more correct than the
original: the frozen side hashes content obtained by
`_driver_cached_entry_source_scan` from a raw `rt_file_read_text`, never through
`SourceFile.load`, which additionally strips a coverage-wrapper marker line
(`source_file_coverage_identity`) and would therefore have disagreed for
`simple_cov_*` / `spipe_wrapped_*` inputs even with correct codegen. The
`""`-on-empty behaviour matches `SourceFile.load`, which returns `Err` for an
empty file. The gate is NOT relaxed: a file genuinely rewritten between parse and
native-compile still fails it.

## Still open

1. **The underlying native-codegen defect.** A `case Ok(record):` binding reads
   the wrong field of the payload struct. Only one call site is worked around
   here; every other match-bound struct field read in compiled Simple is
   suspect. `SourceFile`'s middle field `authored_path` carries a DEFAULT
   (`= ""`) while its neighbours do not, which is the most likely trigger to
   investigate first.
2. **The empty-`detail` repeat-run path** described above.
3. **Duplicate top-level definitions** in `driver_aot_native_output.spl`,
   introduced by `848f626638b` ("surgical extraction of PR #235"):
   `driver_native_disk_source_identity` twice (bodies identical — both had to be
   patched) and `driver_native_module_source_identity` twice (bodies DIFFERENT:
   one reads the SoA owners via `driver_native_frozen_source_lookup`, the other
   iterates `ctx.sources`). Not the cause here, but a merge artefact of that
   shape will bite something.

## What was fixed alongside (separate commit)

1. The stage-2 failure diagnostic read only `stage2-native-build.log` while
   `stage2_status` is also set by the sanity gate, the receiver check and the
   admission publish. `check-stage-log-diagnosable.shs --log` is now repeatable,
   scans every candidate and NAMES the one carrying the reason;
   `bootstrap-from-scratch.sh` passes all eight stage-2 logs. Proven in situ on
   a real bootstrap run.
2. `native-capsule-source-mutated` now names WHICH invariant fired and quotes
   `cache_source`, `frozen=` and `disk=` — without which the root cause above
   could not have been read off a single run.

## Verified: the blocker is cleared, and the NEXT one is named

Stage 2 rebuilt with the fix (binary `d7ee97d8059f1d92…`), first-ever compile of
a fresh module name:

```
[native-compile-failed] build.capsule_repro.sub.hw_fix_1: native-capsule-receipt-invalid:build.capsule_repro.sub.hw_fix_1:receipt-content-mismatch:expected-bytes=1069:actual-bytes=1069
```

`native-capsule-source-mutated` no longer fires — the source-identity invariant
now passes. The next blocker is `receipt-content-mismatch` in
`driver_native_capsule_result_reason_v1`: the `.capsule-receipt` written beside
the object and the string rebuilt for comparison are **the same length (1069
bytes) and different content**, which is the signature of one equal-width field
(a hex digest) differing — i.e. very likely the SAME field-binding defect class,
one layer further in (`capsule.capsule_identity`, `capsule.object_path`,
`fp.size` or `fp.content_hash`). Stage 3 is still not reached.
