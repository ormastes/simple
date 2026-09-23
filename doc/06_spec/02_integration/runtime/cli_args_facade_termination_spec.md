# CLI argv facade termination

Manual for `test/02_integration/runtime/cli_args_facade_termination_spec.spl`.
This manual is authored from the scenarios; doc generation and execution are
pending a verified full self-hosted CLI. No execution PASS is claimed.

Requirement REQ-ARGV-FACADE-001: argument access through the historical
`app.io.cli_ops.get_args` facade terminates and preserves the provider result.

1. Launch the spec with an attested full CLI under an external 30-second
   process-tree deadline and an explicit memory ceiling.
2. Read the scalar argument count. Call the facade 64 times and compare every
   returned argument with its scalar entry. Every count and value must match.
3. Read negative, first-out-of-range, and next-out-of-range scalar indices.
   All must return empty text.

Native evidence uses the paired facade and direct-provider fixtures in
`test/fixtures/runtime/cli_args_*_native.spl`. Compile with stub fallback
disabled. Invoke each binary with `alpha`, `two words`, an empty string, and
`--literal` as four distinct arguments. Both must print their named success
marker and exit 0. A wrong final argument must exit 22; a missing argument
must exit 21. Enforce the deadline from the parent process because infinite
recursion cannot report its own failure.

The native literal oracle checks argv independently of the scalar wrappers.
The integration spec shares their runtime provider and checks consistency.
Neither replaces fresh Stage 4 bootstrap startup acceptance or cross-target
execution. See the linked bug report for the remaining evidence matrix.
