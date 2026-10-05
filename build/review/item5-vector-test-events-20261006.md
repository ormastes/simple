# Item 5 vector apply-event native check

This is a bounded native C check for the production vector provider apply boundary. It does not qualify the Simple provider loader or a Simple DB/HTTP application.

Source is based on release commit `62e10c94cb9a2749911a64419cf8064e064e50ba` in isolated worktree `D:/dev/simple-item5-vector-test-events-20261006`. The final four source SHA-256 values are:

- `src/runtime/providers/vector/bitmap_provider.c`: `731DD327A2C8F70FB2264FD11B8FD01582FDF3E3613414FAE78B0C5E40E3DDEE`
- `scripts/check/check-vector-provider-test-events.shs`: `A81E743D9683CC81152223A41EAC4717A4FC7D062D3519E147C125B52FAC4F4B`
- `src/runtime/test/vector_provider_event_selfcheck.c`: `924D9AACA9F004E6F8FFD6C8B54DF9FFCE501240D5DA2AB8FFFCA26E13B8AD2F`
- `src/runtime/test/vector_provider_test_events.c`: `2A1BFF259EEDC401918C9D012AE4C72248516B22654B99F318CD45392B0D8113`

The script ran in a private WSL clone at base `62e10c9` and exited 0:

```sh
sh scripts/check/check-vector-provider-test-events.shs /var/tmp/item5-vector-events-native-provider_callpaths-cycle2-20261006
```

Cycle 2 passed 11 cases with scalar oracles and strict receipts: no provider load (0 loads/0 events); load without call (1/0); 15-word scalar-tail bitmap AND (success, 0 loops); 33-word bitmap AND and OR (2 AVX512 loops each); 193-byte HTTP byte search and CRLF search (3 loops each); invalid request (status 1, 0 loops); and forced no-AVX bitmap, no-AVX HTTP, and no-BW HTTP (status 5, 0 loops each). The host advertised AVX512F/BW. The harness records the launched selfcheck PID and checks it against the observer receipt PID.

The receipt validator rejected 11 malformed fixtures covering appended and same-line-count duplicate keys, missing fields, extra fields, wrong PID, status/event sum mismatch, loops without success, malformed number, u64 overflow, oversize input, and missing final newline. Receipts are capped at 4096 bytes; instrumentation aborts on receipt/counter overflow or write failure.

The production-flag-off provider object is byte-identical to the pinned release source object under the same feature flags and generated identity. Both objects have SHA-256 `cb62ff9beff45a1fb27d4874a52619423869d2a0fc0161d337a57998882a7bc7`. Bounded disassembly scans found no ZMM, kmov, or byte-compare target families in the baseline provider object and found ZMM instructions in the bitmap and HTTP kernel objects. This scan is not a complete ISA audit.

The test-only observer adds atomic callback and receipt overhead. These results prove native provider outputs, refusals, and executed AVX512 loops for the exercised calls; they do not measure production latency. The Simple app/provider-loader path, app correctness/performance, non-x86 providers, and early transport-error events remain untested here. Cycle 1 failed only because its harness omitted `SIMPLE_VECTOR_ENABLE_HTTP`; the test build was corrected to set both the capability and kernel feature macros before cycle 2.

Artifacts and per-case RSS receipts are preserved at `/var/tmp/item5-vector-events-native-provider_callpaths-cycle2-20261006`. `artifacts.sha256` records the observer, three provider DSOs, and harness; `receipts.tsv`, `build.log`, and the three disassembly files carry the detailed evidence.
