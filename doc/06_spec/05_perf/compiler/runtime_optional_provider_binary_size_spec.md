# Runtime Optional-Provider Binary Size and Startup Cohorts

BS7 qualifies a minimal NoGC hello and interpreter startup only from an
admitted pure-Simple Stage4 compiler. Development evidence contains at least
30 Simple and 30 Python samples; release evidence contains at least 100 of
each. The checker recomputes p50 and p95 startup and max RSS and requires Simple
to remain within 110% of the same-host Python baseline. Each sample row must
bind to the hash of its supplied interpreter or Python executable. The
NoGC hello binary is a separate size-gate input.

## Canonical Stage4 authority — 2026-11-07

Both the producer and checker require these actual authority inputs in addition
to their existing cohort, workload, observation and matched-link arguments:

```sh
--stage4-receipt "$STAGE4_COMPILER.provenance.env" \
--stage4-compiler "$STAGE4_COMPILER" \
--stage4-source-root "$STAGE4_SOURCE_ROOT"
```

The adjacent receipt must use `simple-bootstrap-stage4-provenance-v1` and
`artifact_kind=pure-simple-full-cli`. The existing canonical Stage4 verifier
checks the compiler, source and deep Stage3 authority. A hand-written
`stage=4`/`compiler_kind` label, retained-manual/self provenance or Phase2 Hello
receipt cannot replace it. The compiler is separate from the measured NoGC
hello and interpreter binaries. The cohort v1 format and numerical limits are
unchanged.

The updated shell contract fixture passed its bounded final run. It copies the
unmodified Stage4 verifier and stubs only its deep Stage3 dependency in a
private copied facade, exercising joins and refusal propagation. Its compiler,
source and startup data are synthetic; no fixture compiler is executed or
admitted. Original failures and the three-cycle limit are recorded in
`doc/08_tracking/bug/bs7_stage4_label_not_canonical_provenance_2026-11-07.md`.
This result does not execute the SPipe wrapper or qualify a native cohort.

**Still open:** actual startup/RSS acquisition, workload compiler/runtime/build
bindings, NoGC inventory acquisition and owner-backed no-demand observations.
The scripts consume supplied evidence; empty traces alone do not prove zero
loads or effects. No new size/startup/application PASS is claimed. Historical
measurement and execution notes below retain their original scope.

The NoGC binary must be below 2 MiB. Linux release-small additionally requires
at most 15 KiB and at most 105% of a same-toolchain C hello with the same
startup wrapper, required runtime archive, linker options, section GC, and
strip policy. The C `__simple_main` uses `puts` and must print the same bytes
as the Simple entry. A bare C `main` remains an advisory comparison. Other native
formats use an admitted fixed format allowance. Collector sections,
constructors, initialization roots, optional-provider mappings, and provider
initializations must all be absent.

Rust seed and pre-Stage4 measurements are diagnostic only and cannot satisfy
this specification. A current-source Stage4 compiler now builds the
one-source `Hello World` fixture and the literal-print fixture. The latter's
numeric size sublimits pass with a matched C `puts` link, but it was built
with `--O1 --no-debug`; admitted `release-small`, NoGC/provider/startup/RSS
evidence remains pending.

## Literal-print size scenarios

1. Build `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` with an
   admitted **current-source** pure-Simple Stage4 compiler in Linux
   `release-small` mode. Require the executable to print exactly `hello` and a
   newline. Inspect the retained-section map from its unstripped build: the
   plain-literal path must not retain `rt_string_new_literal`, `rt_to_string`,
   or `rt_literal_intern_table`.
2. Capture the exact Linux LLD response and opened inputs for that Simple
   ELF. Replace only its program object with a same-host C `__simple_main`;
   keep the archived startup/runtime/CRT inputs and link flags. Strip both
   outputs with the same tool. Feed their paths, the capture and its receipt,
   C source, expected stdout bytes, tool paths, Stage4 admission receipt,
   empty NoGC/provider traces, and interpreter/Python startup/RSS samples to
   the production BS7 cohort checker. The C entry must use `puts`. It must
   replay both links before applying both
   Linux limits: at most **15,360 bytes** and at most **105% of matched-startup C**.
3. Reject a C-entry runtime probe as Simple compiler evidence, even when the
   probe calls the same runtime writer and prints the same output.

The historical Simple hello was 13,944 bytes with LLD. A direct-writer C-entry
probe was 5,152 bytes, a difference of 8,792 bytes (about 63%); the probe
omits the Simple entry wrapper and forced roots. Neither number measures the
new current-source Simple output. The old ELF has no `mmap` import; its
524,288-byte literal cache is zero-filled `.bss`, not file content. The
analysis is in
`doc/09_report/compiler/target5_strict_core_hello_2026-09-27.md`.

## Executable checker examples

The companion `test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl`
contains two `describe`/`it` examples with assertions. One runs the production
BS7 producer/checker fixture and requires its clean cohort plus rejected
mutations, including captured-link tampering, expected-stdout drift, separate
interpreter binary drift, sample binary drift, and a
label-only input. The other
invokes the production checker without admission inputs
and requires a failing exit and the missing-input diagnostic. These examples
test the checker with a real LLD fixture but synthetic Stage4 and startup
receipts; they do not measure an admitted Stage4 cohort.
Historically, the shell fixture passed before the final C `puts` source switch;
that earlier session did not finish the updated fixture within its three-cycle
cap. The 2026-11-07 contract-only result above supersedes that fixture status,
without changing the historical native measurement or SPipe execution status.
A direct attempt to run
the SPipe wrapper with the fresh Stage4 compiler stopped during source parse:
its flat AST bridge rejected declaration nodes within a 40-file source closure
before either example ran. The SPipe wrapper therefore has no executed PASS.

**Live size status:** the current-source literal `hello` fixture passes the
numeric matched C `puts` sublimits (13,544 versus 13,264 stripped bytes;
see `doc/09_report/compiler/target5_literal_hello_puts_matched_2026-09-29.md`).
The earlier 13,608-byte C result used the Simple runtime writer and is only
a diagnostic. An admitted `release-small` profile, Stage4 admission receipt,
NoGC/provider traces, and 30/100-sample production cohort remain open.
Do not infer a release-size PASS from the checker examples or the one-source
size comparison.
