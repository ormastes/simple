# RT/HAL external comparator fixtures

These test-only C and Rust executables implement the fixed
`rthal-scalar-v1` comparison protocol. Pure Simple remains the semantic and
effect owner. A child receives the already-observed Pure receipt and returns
only its three four-word digests; `replay` never performs the host effect.

`setup_and_compare.spl` requires canonical absolute compiler paths, their
64-digit SHA-256 identities, the canonical repository root, and absolute output
paths. The output directory must already exist. It compiles both fixtures only
through `EnvAccessPlan.RunAllowedTool` as static non-PIE ELF executables, admits
each result through the runtime's ELF descriptor gate, pins each executable by
a fresh SHA-256 identity, installs that provider plan, and runs two exact cases.
Dynamic ELF, static PIE, or a toolchain without complete static closure returns
a typed `RTHAL-FIXTURE-BLOCKED-v1` scenario receipt instead of substituting a
dynamic fixture.

Required arguments:

- `--repo=<canonical-absolute-root>`
- `--cc=<canonical-regular-file>` and `--cc-sha256=<64hex>`
- `--rustc=<canonical-regular-file>` and `--rustc-sha256=<64hex>`
- `--c-output=<absolute-path>` and `--rust-output=<absolute-path>`

The provider ABI is exactly 24 arguments after `argv[0]`: schema, mode, case
ID, effect flag, then operation, input, outcome, error, and trace digests (four
signed 64-bit decimal words each). Success emits exactly
`RTHAL1 <outcome-4> <error-4> <trace-4>` and a newline. Malformed input exits
nonzero without a receipt.
