# Native test preprocessing flattens full paths into an oversized filename

Status: P2 — source repair implemented; verification pending. No new native calibration executed.

Bug ID: `native_test_wrapper_filename_name_max_2026_11_08`.

## Observed boundary

The retained native positive calibration failed before any assertion or native
compilation. Its coverage wrapper exists (3106 bytes), but preprocessing returned
an empty path and the caller reported `native-test-source: source is missing`.
The original authored fixture was present. The result is infrastructure failure,
not a failed test assertion and not a passing calibration.

Evidence retained on the Linux/aarch64 host:
`/home/yoon/dev/simple-borrow-generic-acceptance-20261030/build/borrow-generic-acceptance-20261030/test-runner-candidate/calibration/positive-direct2-run/terminal.sdn`.

The runner artifact was
`/dev/shm/simple-borrow-generic-test-runner-candidate-20261030/attempt2/bin/simple_test_runner`,
SHA256 `c1f05a99226f376f627fca6285066823c6105c0f1f8828527006add9add2bd21`.
Its launch receipt declares source
`60f3e00e8c9d26db18fb120d16ba02d372311802`. The diagnosis inspected that exact
Git source; it did not assume present dirty-worktree bytes were baked into the
runner. Per-file producer/source equivalence has not been independently admitted.

## Source cause and exact calculation

At that source revision:

- `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:1222–1237`,
  `build_coverage_wrapper`, replaces separators in the full original path and
  embeds the resulting text in `simple_cov_<pid>_<base>.spl` beneath the temp root.
- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:749–758`,
  `preprocess_spipe_file`, replaces separators in the entire generated coverage
  absolute path, strips `.spl`, and constructs
  `spipe_wrapped_<pid>_<flattened-path>_<32-hex-nonce>_native.spl`.
  Completion evidence requires exclusive creation. A refusal returns an empty
  path, losing the distinction between generated-output failure and missing input.

Recorded PID: `2164927`. Original fixture:
`/home/yoon/dev/simple-borrow-generic-acceptance-20261030/build/borrow-generic-acceptance-20261030/test-runner-candidate/calibration/positive.spl`.
Temp root was the sibling `positive-direct2-run/tmp` directory. The coverage
absolute path is **320 bytes**. Its flattened name minus `.spl` is316 bytes;
adding the required prefix, PID, separator,32hex nonce and suffix produces a
**382-byte filename component**, exceeding the observed POSIX **NAME_MAX255**.
This component cannot be created on that filesystem.

The exclusive-create failure itself was not logged. This source calculation
explains the observed failure path but does not exclude an earlier nonce-source
failure. No new execution is claimed.

## Bounded invocation filename repair (2026-11-08)

The generated source files are invocation artifacts, not path-keyed cache
entries. Their filenames now use a fixed ASCII prefix, positive process ID,
and a validated 32-hex invocation nonce. No source pathname is flattened into
either coverage or SPipe filenames. `coverage_wrapper_filename` preserves
`_spec.spl` classification; `spipe_wrapper_filename` preserves `_native.spl`.
Even the maximum signed 64-bit process ID produces fewer than 128 ASCII bytes.
A SHA256 path hash is unnecessary for these temporary invocation files.

Every native/legacy SPipe branch now uses checked entropy, the bounded
helper and exclusive creation. The completion branch retains its existing
16-byte entropy and exclusive-create protections. Coverage wrappers now also obtain checked entropy and use
exclusive creation; a nonce or write refusal returns no generated path, rather
than pretending a missing wrapper was written. Checked coverage/preprocessing APIs return distinct source, entropy, token
and exclusive-create refusal reasons. The native preparation coordinator
preserves those reasons before source staging; source rejection is never
mislabeled as a filesystem failure. Legacy exported tuple/text APIs preserve
their arity and return shapes and print the actual refusal diagnostic. Its real native caller
preserves elapsed time; the release-base interpreter now bypasses coverage wrapping entirely.
Existing source contents, source-marker handling, manifest contracts and
owned cleanup distinctions are preserved. AOT staging retains its original
source binding. The coverage builder does not newly add an authored-source
marker; legacy coverage attribution still uses its generated path and remains
unqualified. No broader legacy attribution fix is claimed. The release-base interpreter MC/DC repair already removed that coverage call;
this change preserves its unwrapped source route and selected execution policy.


The downstream non-AOT compile artifact was another full-path flattening
boundary. `native_test_temporary_artifact_path` now encodes the full source
path plus invocation-identity SHA256, process ID and existing invocation start,
with unchanged
`.coverage-native`, `.mcdc-native` and `.smf` suffix selection. Every component
is at most 127 ASCII bytes for signed 64-bit fields. This digest preserves source-path distinctions lost by slash-to-underscore
flattening and includes the invocation identity, so equal path/PID/start values
do not merge different invocations. Generated routes reuse their owned staged
source path or existing checked-nonce preprocessing path without another entropy
draw. A plain non-spec route with coverage/MC-DC off has neither; only that
route obtains one checked nonce and reports entropy refusal before compilation.
No clock-only fallback is allowed. The already-bounded explicit-AOT naming, private-cache
shape predicate, evidence and completion names remain unchanged.

## Executed host boundary evidence and remaining qualification

A fresh host filesystem harness, isolated with Python `-I` and CPU9, observed
`NAME_MAX=255` and an actual `ENAMETOOLONG` for the recorded 382-byte native
component. A separate real nested authored source makes the old coverage
component exceed 255 and also receives `ENAMETOOLONG`. The proposed bounded
ASCII formats create successfully and preserve payload bytes. Existing-name
exclusive refusal preserves the original payload; missing-parent refusal
preserves authored input; concurrent exclusive creates have exactly one winner.
Retained evidence: `.spipe/name_max_20261108/host-filesystem.sdn`.
A separate new artifact-boundary harness observed ENAMETOOLONG for the old
flattened artifact and successful byte-preserving creation of all three bounded
mode formats at maximal positive/negative signed identity widths, up to 127
bytes: `.spipe/name_max_20261108/artifact-filesystem.sdn`. Neither harness
executes the Simple helper, provider or compiler.

The first host harness failed during a standard-library import because an
unrelated `/tmp/bisect.py` shadowed Python's `bisect`; its attempted old runner
path did not exist, so no compiler or runner executed. Python isolation fixed
the analysis environment. No old native calibration, bootstrap, runner rebuild
or exhausted acceptance attempt was retried. This host evidence establishes
filesystem constraints and exclusive-create behavior only; it does not execute
the Simple helpers or establish their linked provider/runtime behavior.

Behavioral helper specs cover suffixes, maximal PID byte bounds, invocation and
process separation, invalid nonce/PID rejection and distinct nil-entropy
reasons. Artifact specs cover byte bounds, all mode suffixes, flattened path
aliases and process/start separation. Real owner specs
call `build_coverage_wrapper` and `preprocess_spipe_file` with long source paths,
read generated payloads and clean only their owned output before assertions.
Additional owner cases cover native non-completion and legacy branches, real
write refusals, source-rejection cleanup and exclusive-create collision. The
same preparation coordinator is called by the native runner and by the
refusal/cleanup specs; the test does not bypass it with a copied implementation. These nineteen authored
scenarios are **NOT RUN**. The full long-path native runner positive/negative
calibrations, core/lib/MCP checks, native backends and generated doc execution
remain required on an admitted current full runtime. No fixed/closed, new
compiler/runtime qualification or all-P2 completion is claimed.

## Required reproduction and prevention evidence

Execute a real spec at a long nested authored path with a long physical temp
root and enabled default MC/DC, preserving its digest/source markers. Require
nonzero assertions and the expected result through the actual native runner.
Pair it with a deliberate failing assertion, separate coverage/native write
refusals, an exclusive-create collision, concurrent invocation separation and
short-path semantic parity. Verify filename byte bounds directly, not just
character counts. Do not close this bug from a source-only name calculation.

A short physical temp directory would calculate234 bytes for the same original
fixture (and a short physical fixture path would reduce it further). This is
only a possible diagnostic path workaround, not a production repair, test
qualification or permission to retry. The temp owner resolves symlinks with
`pwd -P`, so a short alias to the old long directory does not provide that bound.

The prior calibration budget remains exhausted. No diagnostic exception,
calibration retry, runner rebuild or new test execution was performed here.
