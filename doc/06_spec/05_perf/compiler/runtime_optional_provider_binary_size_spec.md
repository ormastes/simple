# Runtime Optional-Provider Binary Size and Startup Cohorts

BS7 qualifies a minimal NoGC hello and interpreter startup only from an
admitted pure-Simple Stage4 compiler. Development evidence contains at least
30 Simple and 30 Python samples; release evidence contains at least 100 of
each. The checker recomputes p50 and p95 startup and max RSS and requires Simple
to remain within 110% of the same-host Python baseline.

The NoGC binary must be below 2 MiB. Linux release-small additionally requires
at most 15 KiB and at most 105% of a same-toolchain C hello with the same
startup wrapper, required runtime archive, linker options, section GC, and
strip policy. A bare C `main` remains an advisory comparison. Other native
formats use an admitted fixed format allowance. Collector sections,
constructors, initialization roots, optional-provider mappings, and provider
initializations must all be absent.

Rust seed and pre-Stage4 measurements are diagnostic only and cannot satisfy
this specification. Heavy native cohorts remain pending until an admitted
Stage4 binary is available.

## Literal-print size scenarios

1. Build `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` with an
   admitted **current-source** pure-Simple Stage4 compiler in Linux
   `release-small` mode. Require the executable to print exactly `hello` and a
   newline. Inspect the retained-section map from its unstripped build: the
   plain-literal path must not retain `rt_string_new_literal`, `rt_to_string`,
   or `rt_literal_intern_table`.
2. Strip that Simple ELF and a same-host, same-toolchain matched-startup C hello. Feed their
   exact paths, hashes, Stage4 admission receipt, empty NoGC/provider traces,
   and startup/RSS samples to the production BS7 cohort checker. Require both
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
BS7 producer/checker fixture and requires its clean cohort plus six rejected
mutations. The other invokes the production checker without admission inputs
and requires a failing exit and the missing-input diagnostic. These examples
test the checker using synthetic evidence; they do not measure a Stage4 hello.
The shell fixture itself passed in this isolated worktree. The two SPipe
examples have not run under an admitted current-source pure-Simple test runner.

**Live size status: BLOCKED.** The admitted current-source Stage4 compiler and
check worker are unavailable, so the three literal-print qualification steps
above have no passing executable result. Do not infer a release-size PASS from
the checker examples.
