# Runtime Optional-Provider Binary Size and Startup Cohorts

BS7 qualifies a minimal NoGC hello and interpreter startup only from an
admitted pure-Simple Stage4 compiler. Development evidence contains at least
30 Simple and 30 Python samples; release evidence contains at least 100 of
each. The checker recomputes p50 and p95 startup and max RSS and requires Simple
to remain within 110% of the same-host Python baseline. Each sample row must
bind to the hash of its supplied Simple or Python executable.

The NoGC binary must be below 2 MiB. Linux release-small additionally requires
at most 15 KiB and at most 105% of a same-toolchain C hello with the same
startup wrapper, required runtime archive, linker options, section GC, and
strip policy. A bare C `main` remains an advisory comparison. Other native
formats use an admitted fixed format allowance. Collector sections,
constructors, initialization roots, optional-provider mappings, and provider
initializations must all be absent.

Rust seed and pre-Stage4 measurements are diagnostic only and cannot satisfy
this specification. A current-source Stage4 compiler now builds the
one-source `Hello World` fixture; the literal-print fixture and admitted
NoGC/provider/startup/RSS cohort remain pending.

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
   C source, tool paths, Stage4 admission receipt, empty NoGC/provider traces,
   and startup/RSS samples to the production BS7 cohort checker. It must
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
mutations, including captured-link tampering, sample binary drift, and a
label-only input. The other
invokes the production checker without admission inputs
and requires a failing exit and the missing-input diagnostic. These examples
test the checker with a real LLD fixture but synthetic Stage4 and startup
receipts; they do not measure an admitted Stage4 cohort.
The shell fixture passed in this isolated worktree. A direct attempt to run
the SPipe wrapper with the fresh Stage4 compiler stopped during source parse:
its flat AST bridge rejected declaration nodes within a 40-file source closure
before either example ran. The SPipe wrapper therefore has no executed PASS.

**Live size status:** a separate current-source one-source `Hello World`
fixture has a captured-link matched C size pass (13,544 versus 13,608 stripped
bytes; see `doc/09_report/compiler/target5_exact_hello_link_c_gate_2026-09-29.md`).
The literal-print fixture above, Stage4 admission receipt, NoGC/provider
traces, and 30/100-sample production cohort still have no passing result.
Do not infer a release-size PASS from the checker examples or the one-source
size comparison.
