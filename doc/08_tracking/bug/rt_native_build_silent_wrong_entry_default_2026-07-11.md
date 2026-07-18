# BUG: rt_native_build arg parser silently compiles the wrong entry (defaults to src/app/cli/main.spl)

**Status:** source fixed 2026-07-15 in the pure-Simple bootstrap wrapper and
Rust seed parser; executable native-build proof pending

## Symptom

`bootstrap_main native-build probes/hello.spl -o probes/hello_out` exits 0 and
links a binary, but the binary prints nothing (zero write syscalls under
strace): the build silently compiled `src/app/cli/main.spl`, not `hello.spl`.

## Root cause

`rt_native_build`'s Rust arg parser
(`src/compiler_rust/native_all/src/lib.rs:395-462`) has no single-file entry
inference: any bare positional path is pushed to `source_dirs`, and
`entry_file` unconditionally defaults to `src/app/cli/main.spl` when that file
exists — regardless of the file actually passed.

## Fix direction

Preferred (pure Simple, per repo rules): in `src/app/cli/bootstrap_main.spl`'s
native-build dispatch, detect a single-file `.spl` positional arg and inject
the explicit entry flag the Rust parser understands (in progress under #138).
Longer term this call site is removed entirely when the rt_native_build seed
FFI is cut. The Rust parser's silent wrong-entry default should still be made
loud (error, not fallback) if it survives.

## Resolution

The pure-Simple bootstrap wrapper detects only the isolated single bare `.spl`
form and compiles it as the entry. Commands containing `--source` or positional
source directories stay on the full native builder so those inputs are not
dropped. The surviving Rust seed parser now applies entry inference at its
trust boundary: one bare `.spl` becomes the entry, explicit `--entry` wins, and
multiple bare `.spl` inputs without an explicit entry fail with an ambiguity
diagnostic. Directory-only stage builds retain their legacy CLI entry default.
Focused pure-Simple classification and Rust resolver regressions cover these
decisions; compile/run marker proof remains pending a runnable bootstrap
artifact.
