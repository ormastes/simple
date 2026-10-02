# Reverse-reference module ownership

Status: source candidate; native fixture, SSpec and HIR/MIR integration UNRUN.

The executable spec is `test/01_unit/compiler/cache/reverse_reference_module_ownership_spec.spl`.
The standalone native producer is `test/fixtures/reverse_reference_ownership/main.spl`.
This is a real active-collector test, not a source-text assertion.

Compile the fixture once from the immutable candidate using a hello-qualified
native producer and the canonical resource guard. Record the producer executable
SHA256, producer source commit, target source commit/tree, compiled fixture SHA256,
compile argv, successful compile receipt, and actual hello binding for that same
producer. A self-reported identity is insufficient admission evidence. Do not use
the seed as a general runner. Explicit diagnostic admission remains provisional.

Set `SIMPLE_REVERSE_PRODUCER_SHA256`,
`SIMPLE_REVERSE_PRODUCER_SOURCE_REVISION`, and `SIMPLE_REVERSE_SOURCE_REVISION`
to the pinned receipt identities. Run each invocation in a fresh process:

```text
<compiled-fixture> baseline 4
<compiled-fixture> scoped 4
<compiled-fixture> baseline 8
<compiled-fixture> scoped 8
```

Capture stdout as `<mode>-<count>.env` and the canonical sampled 7 GB process-tree
receipt as `<mode>-<count>.resource.env.process-tree.env`. Sampling enforcement is
not a hard Job memory ceiling. No build/cache state changes occur between modes;
the first module is deliberately largest and initializes capture state cold.

The fixture uses actual registration, SHA256 evidence, aliases, known-family and
snapshot APIs. It verifies every prior fact's field values, digest and order after
each close, pending reads, duplicate registration within/across modules, a
recoverable module error, abort cleanup, nested refusal, sealed-batch invalidation,
inactive collection, and stale phase tokens. Validation scratch is separately
reclaimed in both modes. Complete is emitted only after all semantic checks.

Point `SIMPLE_REVERSE_REPORT_DIR` at the reports and run the spec with an admitted
self-hosted runner. Missing metrics fail. Acceptance requires identical final
state, strictly fewer live bytes/objects, elapsed <= baseline * 1.5 + 20 ms,
N-to-2N elapsed <= 3x + 20 ms, retained bytes <= 3x + 64 KiB, and peak RSS <=
baseline + 16 MiB under the unchanged 7 GB sampled cutoff.

This collector gate does not qualify HIR/MIR integration or enable streaming.
Follow with actual retained-HIR, streaming-HIR and MIR fixtures with collection
active, parser/semantic-error paths, full feature parity, and capped full-module
memory/time acceptance. PR2208's parser ownership/policy fix and PR2213's
diagnostic capture must be preserved when integrating overlapping helpers.
