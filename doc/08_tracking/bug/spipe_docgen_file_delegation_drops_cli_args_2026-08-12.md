# spipe_docgen delegated CLI loses program arguments

## Status

FIX IMPLEMENTED, FINAL CHECK PENDING — still blocks release evidence.

## Evidence

On 2026-08-12, the bounded diagnostic command

```sh
bin/simple spipe-docgen test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl \
  --output /mnt/data/<temp>/out --no-index \
  --provenance-receipt /mnt/data/<temp>/docgen-receipt.env
```

reached `src/app/spipe_docgen/spipe_docgen/main.spl` but printed usage and
returned 1. No receipt was emitted. The focused direct receipt-writer spec
passes, so the defect is in delegated argv propagation, not receipt
serialization.

The dispatch path was
`cli_run_spipe_docgen -> cli_run_file -> process_run_inherit`; the delegated
program observes no usable arguments through `rt_cli_get_args()` even though
the parent passes the stripped command arguments.

Diagnosis showed the argument-sensitive execution selector scanned only the
thin compatibility entrypoint, not its imported implementation, and therefore
selected the JIT lane whose delegated argv behavior is not yet equivalent.
The compatibility owner now acquires arguments itself, making interpreter
selection explicit, and removes only the file-delegation entry path before
calling `run_spipe_docgen`. The first focused attempt after moving acquisition
to the wrapper exposed that entry-path prefix; the bounded three-cycle cap was
reached after correcting it, so the final command has not been rerun.

## Required fix

In a fresh verification turn, run the canonical delegated command once and
require a valid receipt whose binary hash matches the executing file. Then run
it with an admitted pure-Simple binary. Do not synthesize a receipt or promote
the Rust bootstrap seed to release evidence.
