# Native-build silently ignores unsupported options

Status: source-confirmed; native reproducer unrun; CLI fix pending.

The coverage-retained-parser SSpec originally passed `--no-stub-fallback` and
`--max-threads=1`. These are not supported native-build options. In
`src/app/io/_CliCompile/native_build.spl`, the argument loop handles
`--threads`, `--jobs`, `-j` and their supported equals forms, but has no handler
for those two options. Its final branch only handles non-option positional
entries, then increments the cursor. Unrecognized dash-prefixed options are
silently ignored rather than rejected.

Consequence: a caller can believe stub fallback is disabled or worker count
is bounded when neither instruction has reached its intended owner. The
wrapper correction uses supported `--threads 1`, a private cache, explicit
Cranelift/dynload selection and a required `SIMPLE_NO_STUB_FALLBACK=1`
environment policy. This corrects the caller without claiming to fix CLI
validation.

Bounded reproduction, once an admitted pure-Simple host is available: invoke
native-build on a real minimal fixture with a deliberately unsupported option
and retain exit status, diagnostics and whether compiler work began. Expected:
nonzero option error before any parse/build work. Source behavior presently
allows the option to fall through. Runtime reproduction has not been run.

Follow-up acceptance: reject unknown options without breaking supported
option/value and positional forms; prove the negative option cannot launch
compiler work; retain positive native compilation coverage. Do not treat an
unsupported policy spelling as a successful policy application.
