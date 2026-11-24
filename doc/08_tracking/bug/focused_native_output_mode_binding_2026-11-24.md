# Focused native-build ignores an explicit object output mode

The Windows focused worker probe in run 45363635244 used the verified
93f7b103237c native Phase2 compiler (SHA256
`f8be04ff2979d4b41cd038f8aa3601619891ec7cf74b55dbe73f06c84baa85f0`),
renamed to `simple.exe`, and requested `--emit-object`.

Its real file worker completed one HIR unit and one MIR module with sealed PASS
records and an AMD64 COFF object. The coordinator then attempted an executable
link and failed to find `src/runtime/runtime.c` in the independent tiny project.
The owner exited 1 normally, quiescent, at 132332 KiB peak RSS under a 6291456
KiB cap. This was neither a memory failure nor another missing-worker-ledger
failure. The full Phase3 build was not started.

`bootstrap_main` recognizes the flag, but its focused Stage3 dispatch returns
before the positional route's output-mode binding. The focused owner previously
never bound `SIMPLE_NATIVE_BUILD_EMIT_OBJECT`. The repair reuses the canonical
argument parser and output-mode snapshot/bind/restore owner around the actual
focused compiler call. Omitted flags preserve inheritance, conflicting modes
remain invalid, and Stage4 strict output restrictions remain enforced.

The independent `running-image-unhashable` diagnostic is a cache-identity
downgrade: this producer hashes `/proc/self/exe` only. It did not prevent the
Windows worker from compiling the object, and does not establish failure of
the Windows kernel image-path helper.

`check-focused-native-output.py` requires a freshly compiled actual dispatcher
fixture outside all runtime-source ancestors. It checks real relocatable bytes,
default executable-link failure at the expected missing-runtime boundary,
conflict refusal, Stage4 refusal, and output-mode restoration. A source review
or checker syntax pass is not execution of these assertions. Native execution
and compiler-generation qualification must be reported separately.
