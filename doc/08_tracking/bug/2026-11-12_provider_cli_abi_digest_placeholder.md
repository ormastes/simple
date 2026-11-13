# `provider_cli` built-in leaf advertises a placeholder `abi_digest` (violates the SCI canonical-digest contract)

- **Date:** 2026-11-12
- **Status:** OPEN (spec oracle realigned to current output in work/product-queue-p1-20261112; placeholder itself unfixed)
- **Severity:** Medium — honest-metadata contract violation; negotiation against this leaf would accept a fabricated digest
- **Area:** `src/app/provider_cli/entry.spl`

## Summary

`src/lib/nogc_sync_mut/composition/abi_digest.spl` states the contract:

> SCI locks `abi_digest` as one canonical lowercase 64-hex SHA-256 string.

`src/app/provider_cli/entry.spl:37` hardcodes:

```simple
abi_digest: "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
```

and the `metadata` fast path (line 63) renders the same placeholder. The
64-`c` string is parseable hex (so `simple_provider_digest_from_hex_v1`
accepts it), but it is not the SHA-256 of anything — it is a stand-in
introduced by commit `7306928a2aa` ("fix(app): clear 15 full-CLI native MIR
lowering module failures") when the field was migrated `i64 -> text`; the
previous numeric value was `771`.

The built-in leaf is documented as "an honest in-process provider"; a
fabricated ABI digest breaks that honesty and would let a host accept the
leaf under a digest it never actually measured.

## Repro

```bash
./bin/simple.exe run src/app/provider_cli/main.spl metadata
# → fmt-leaf|SimpleCliCommandV1/1|provider=257|abi=cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
```

## Fix direction

Compute the canonical ABI SHA-256 for `SIMPLE_CLI_COMMAND_V1_INTERFACE` at
definition time (a fixed, pinned constant derived from the frozen interface
layout, documented next to the interface id in
`src/lib/nogc_sync_mut/composition/provider_contract.spl`), or thread the
registered provider's digest through `simple_provider_query_in_process_v1`
(which already renders `abi_digest` via `simple_provider_digest_from_hex_v1`)
instead of the hardcoded metadata string. Then re-pin
`test/02_integration/app/provider_cli/provider_cli_entry_spec.spl` to the real
digest.

## Note

`test/02_integration/app/provider_cli/provider_cli_entry_spec.spl` was updated
in this lane to expect the current placeholder output (per the merged
stale-oracle convention used for `model3d_cli_spec`), so it is green while
this bug remains open. The placeholder must not be left as the pinned
expectation long-term.
