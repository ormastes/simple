# SDN canonical string escape is quadratic: a 2 MB string is OOM-killed

- **Status:** closed (2026-11-15)
- **Where:** `src/lib/common/sdn/encode.spl` `_sdn_enc_escape`
- **Symptom:** `test/03_system/app/orchestrator/feature/container_output_plan_codec_v2_spec.spl`
  timed out at 900 s. The case "bounds total and nested encoded bytes" encodes a
  2,097,154-byte string through the spec's `output_codec_wire_v2`.

## Root cause
`out = out + ch` for every byte copies the whole prefix on each step, so cost is
O(n^2) in both time and memory. Measured on the seed: 128 KB took 1.3 s, 512 KB
took 14.5 s, and 2 MB was SIGKILLed (rc=137) at about 17 s.

## Fix
Scan bytes with `byte_at`. Copy unescaped runs as single slices, then do one `join`.
A string with no escapes returns unchanged. Output is byte-identical.

| input | before | after |
|---|---|---|
| 2 MB encode + decode probe | killed (rc=137) | 0.41 s, 182 MB RSS |
| codec_v2 spec | timeout at 900 s | 6.4 s, 5/5 |

Specs: `test/01_unit/lib/common/sdn/sdn_encode_escape_linear_spec.spl` (repro at
2 MB, plus escape-boundary and all-escape generalizations, 3/3).
`traceability_sdn_strict_roundtrip_spec` still passes 10/10.
