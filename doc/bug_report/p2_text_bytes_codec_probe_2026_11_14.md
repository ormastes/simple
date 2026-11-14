# P2 text-byte provider returns an invalid array in an isolated codec probe

Status: open, producer-bound reproduction; shared bug registry update pending owner
coordination. No claim of recurrence with the latest compiler or the full imported
production closure. Found while implementing directory TLDR schema 2.

On 2026-11-14 an isolated native probe extracted exact production package codec,
wire, hash256, registry, physical reader/budget, UTF-8 validator and canonical
`text_bytes.spl` provider functions. Imports were flattened without replacing the
algorithms. The provider calls `rt_text_to_bytes` through its declared extern.

Producer: `/home/yoon/dev/simple-boot-s3gen-20261112/build/bootstrap/pinned-src/pinned-df719eff44cf/build/bootstrap-s3gen/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`
SHA256: `3b38223677dd46f92c29c12f20566dc9e65c6b65b1456c9c89c95907b5e106ec`.

Expected: `text_to_bytes("pkg").len() == 3`; legacy codec encode/decode succeeds.
Observed: runtime reports `rejected invalid array handle before dereference;
probable compiler/FFI ABI mismatch`, byte length 0, text validation false, package
validation false, then `PANIC: legacy encode`. No schema-2 case executes.

Control: replace only the package codec block with unchanged release commit
`0aa438444da8f731a8a0d3187fb39ed0800c6eef`, remove schema-2 tests and retain the same
helpers, producer and legacy input. Compile succeeds; the identical failure
recurs. This separates the failure from the new schema extension, but does not
identify whether flattening, compiler FFI lowering or provider ABI is responsible.

## Retained evidence

Directory: `/tmp/dir-tldr-codec-probe-20261114`.
`extract.py`, `extraction.sdn`, `baseline.sdn`, `compile2.log`, `compile3.log`,
`compile4.log`, `run3.log`, `run4.log`, generated binaries and link receipts.
The baseline source SHA256 is
`fd445d7ebb0ad356e87ca2bf464a546b0c14c856bb719d9dfa058d87b4b04e2c`;
feature diagnostic source (`/tmp/dir-tldr-codec-probe-feature.spl`) is
`d3eb2fcee40238e11ce8547ebbbb906524db0bf6c2a5b44ae509a5e2faab9396`.
Canonical provider source SHA256:
`ccfa60bae43f92d54f1ff06a7e8803373dddba735b01935b053620a19a04da84`.
The baseline linked executable SHA256 is
`b2010de26d5bff7e069290aa84547f977c5ae83c1b6b3a4914f1919b2774a609`.
Link command names generated native runtime objects; those temporary objects were
removed by the producer, so an independent runtime-object hash was not retained.

From the private Git fixture, under `ulimit -v 2097152` and `timeout 60s`, execute
`<producer> native-build --source src --entry src/main.spl --entry-closure
--cache-dir /tmp/dir-tldr-codec-probe-20261114/cache --threads 1 -o <output>`.
Then run output under a 10-second limit. Four compile attempts total: initial
missing-extraction-helper failure, complete feature probe, diagnostic feature
probe, unchanged-codec control. Stop further same-cause retries. Explicit output
cache was private; producer logs still showed its default global HIR cache path.

Next diagnostic: inspect generated call/return representation for the exact
provider and reproduce with the normal imported owner under an admitted newer
producer. Do not change production codec semantics merely to hide this failure.
