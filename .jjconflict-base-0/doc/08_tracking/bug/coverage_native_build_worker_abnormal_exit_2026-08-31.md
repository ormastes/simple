# native-build worker wrapper exits abnormally, so no coverage-native spec can build (2026-08-31)

Status: OPEN. Found while making the coverage wrapper-compile path fail closed (PR #157).

`bin/simple test <spec> --coverage --mode=native` never produces a binary on this
host. The compile step (`native-build --backend llvm --source src/lib
--entry-closure --entry <wrapped spec> --runtime-bundle core-c-bootstrap`) exits
non-zero after ~12s with:

    !!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
    error: native-build worker wrapper exited abnormally (signal or wait failure,
    code -1) before producing a binary; its process group has been terminated.

Reproduce (seed built from the tree, `--no-cache` to defeat the result cache):

    bin/release/x86_64-unknown-linux-gnu/simple test \
      test/perf/graphics_2d/no_duplication_spec.spl --coverage --mode=native --no-cache

Independent of PR #155: reproduces with #155 applied and with it reverted.
Plain `--mode=native` without `--coverage` also fails to compile on this host
(pre-existing `Compilation failed:` arm), so the fault is not coverage-specific.

Why it went unnoticed: until PR #157 this failure was converted into a green
verdict by the coverage interpreter fallback -- the spec was re-run unwrapped on
the interpreter and its pass counts reported as a normal pass. With the
fail-closed default the failure is now visible as
`ABORTED BEFORE EXECUTION ... this is NOT a test result`.

Known remaining (separate, minor): the non-coverage `Compilation failed:
{compile_stderr}` arm still leads with the seed's "bootstrap seed only" banner
instead of the real diagnostic; the `first_line` fix in PR #157 covers only the
abort/degrade messages.
