# Native slang-pack argv defect

Status: source-proven defect with a local repair; runtime verification UNRUN.
Reviewed source: f3aab661d3ba6045fa98b9b0191e9ff228d28836.

`runtime_startup_args.h` preserves argv[0]. `sys_get_args` forwards the complete
argument array. `slang_pack/core.spl::_command_args` only removes a prefix when
it encounters a `.spl` path, and `_argv_from_args` prepends another program name.
Consequently a native invocation with `--help` falls through to `run` with the
executable as the input and `--help` as the output directory. The packer can then
try to load the executable. Do not use that invocation as a harmless help probe.

The repair makes process argv ownership explicit. `main.spl` passes `true` to
`run_main_args`, which forwards the flag to `_command_args`. That helper starts
its existing loop at index one only for a nonempty process argument array.
The flag defaults to false for existing normalized callers. This works for
renamed executables without guessing their filename or suffix. It adds no
whole-array scan, no global state, and no additional result array. The existing
first-`.spl` source-runner prefix rule remains unchanged.

The combined candidate `7e0686e2ab1` still had the defective app code. Its generic
argv probe changes preserve literal argument boundaries and do not normalize
this app's argv[0], so this app repair is independent.

`test/01_unit/app/slang_pack/native_argv_regression_spec.spl` covers native
normalization, renamed executables, empty arrays, literal boundaries, input
array preservation, source/interpreter prefixes, and normalized callers. Its
dispatch cases use only no-argument and JSON usage; they cannot reach tensor
loading. Help is checked by the pure normalization helper to avoid executing a
potentially unsafe old help path. All Simple execution remains UNRUN. Source
review and host control checks are not a native PASS.

The frozen f3 current-producer link successor uses **no arguments**. Its native
array has only the executable; the extra prepended name makes `run` see two
arguments, which reaches `_usage` and returns `EXIT_USAGE=2` before `_do_pack`.
The oracle is twelve exact UTF-8 lines from `_usage` and `log_options_help`,
with LF terminators and empty stderr. A canonical five-second process owner
checks the exit, exact output, closed process tree, and observer errors.
This checks old-source usage behavior; it does not qualify tensor conversion
or validate the new repair. Its immutable source and controls are unchanged by
the app repair.

Successor controls are under runtime/windows-restart-20261004/
progressive-f3-p177808-slang-pair-attempt1. Cranelift and LLVM use fresh separate
backend/source/producer cache namespaces and one isolated canonical source
checkout. Backend requests are sequential because that checkout's SCV writer
authority is shared. Historical successful binaries are left untouched.
