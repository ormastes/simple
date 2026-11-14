# Initializer link receipt V2 focused execution

Status: 13 native checks passed; production initializer object capture, backend
startup discovery, final aggregation and full authored specs remain unrun.

The separate receipt probe used two compile attempts. Attempt 1 stopped in HIR
because the extraction omitted `hash256_hex_valid`; no codec executed. Attempt 2
added that exact production declaration, `hash256_hex_nibble`, and its length
constant. No production source workaround or hash replacement was made.
The older PackageInit codec remains at five attempts; these are separate criteria.

The admitted Linux/AArch64 P2 SHA256 was
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
The probe compiled with core-c, one worker, entry closure and a private explicit
cache in 5.35 seconds. HIR logs still name the producer's global HIR cache; this
is not a claim that every cache was isolated.

Prelaunch MemAvailable was 57,973,668 KiB, above the required 36 GiB.
`CAP_MEM_MAX=2G CAP_REQUIRE=1 scripts/resource/run_capped.shs` established a
systemd scope; the in-scope launcher asserted memory.max=2147483648 and
memory.swap.max=0 before invoking the 60-second compiler timeout. No address-space
ulimit was used. Native execution under the same cap and a 10-second deadline
returned zero and printed `initializer-link-receipt-v2: 13 checks PASS`.

Checks cover the independently known SHA256 key vector; exact initializer order;
repeated ordered object hashes; corruption, extra data, old schema and padded
count refusal; changed object order; and explicit checked-empty startup.
They do not exercise maximum-size inputs or all eight authored codec scenarios.

Artifacts retained at `/tmp/initializer-link-receipt-v2-probe-20261114`:
`extraction.sdn`, tracked `src/main.spl`, `compile.log`,
`compile-attempt2.log`, `compile-attempt2.exit`, `run-attempt2.log`,
`run-attempt2.exit`, `scope-attempt2.txt`, and `capped-command.sh`.

Private fixture commit: `67652e0e80913c6b272d072eae398c565055cce1`.
Fixture SHA256: `1f7339ddc5f67307167a2138ffdca9b9f2029d33fca08c6a3c83d1e2d55fbff7`.

Actual scope evidence:
```text
0::/user.slice/user-1000.slice/user@1000.service/app.slice/run-r9cda5d04d1ee41b4917870f758008a3b.scope
memory.max: 2147483648
memory.swap.max: 0
```

Execution receipt: `execution.sdn` links the prepared extraction manifest to
the exact tracked source, producer, logs, cap and executable. The original
`prepared_not_executed` extraction status is retained as preparation provenance.
Executed binary SHA256: `e58d00d8438e680bd2277cd9ba21d761c135ac637bc47bbfa0216224c5ddd1d7`.
