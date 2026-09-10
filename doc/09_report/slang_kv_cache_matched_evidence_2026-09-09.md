# Slang KV-cache matched evidence

Date: 2026-09-09
Measured source: `dd68490f33208bc84e99af8a5e57a64d82082991`
Result: **PASS**

The matched real-model run completed 50 fresh-process samples: five workloads,
five paired repetitions, and both snapshot and physical-page lanes. All 50
samples passed the per-sample token, telemetry, and cleanup gates. All 25 pairs
had identical output digests and generated-token vectors.

| Workload | Snapshot median ms | Physical median ms | Snapshot max RSS KiB | Physical max RSS KiB |
|---|---:|---:|---:|---:|
| cold | 28 | 29 | 313052 | 287316 |
| exact repeat | 39 | 42 | 313072 | 288916 |
| prefix extension | 41 | 61 | 312816 | 294100 |
| alternating prefix | 74 | 103 | 313100 | 299332 |
| eviction pressure | 184 | 226 | 313720 | 296800 |

These observations establish correctness and matched execution evidence; they
do not establish a universal physical-page speedup. The executor was the
Rust-built bootstrap seed identified below, so this run is physical-provider
and differential evidence, not self-hosted Simple release-performance evidence.

## Identity

- Model: `stories15M-q4_0.gguf`, 19,077,344 bytes,
  SHA-256 `6151b1929d7f5aa3385d9ddef3393e55587c0a55de661562322bc51dfda93a04`.
- Tokenizer: embedded in that exact GGUF artifact and therefore covered by the
  same immutable model hash.
- CPU: heterogeneous ARM `Cortex-X925,Cortex-A725`; complete `LC_ALL=C lscpu`
  receipt SHA-256
  `846a540840d15b76a27ec7f1d2a17d0beeab6e05ac7196a7bb99d8e32dee32ba`.
- Architecture/kernel: `aarch64`, Linux `6.17.0-1032-nvidia`.
- Threads: 1; greedy sampler; GPU layers: 0; KV: F32; flash attention and KQV
  offload disabled.
- Generated-token budget: 2 per request; repetitions: 5 paired runs per
  workload with alternating lane order.
- Snapshot limits: 4 entries and 2,147,483,648 bytes. Physical limits: 64
  tokens/page, 16 pages, 4 prefixes, and 2,147,483,648 bytes.
- Requested context: 1024; all 50 stderr receipts yielded exactly
  `n_ctx=1024,n_batch=1024,n_ubatch=1024`.
- Executor: Rust bootstrap seed at
  `src/compiler_rust/target/debug/simple`, SHA-256
  `8170cf2ed52614727f4f0d923895f263bcb8b1c30bf3f2f1aa1e81fb4401b220`.
- Backend SHA-256:
  `eeecb47392952acc1b232f430824a2f9834eec14b46d3972dc81ddd15525197b`.
- llama provider SHA-256:
  `f50adb6dbc197b4c65d301316974454d8949a8e94589fde085f64412be6ed426`.

## Evidence receipts

The reviewable evidence is published under
`doc/09_report/evidence/slang_kv_cache/20260909T130630Z/`. Raw per-process
stdout/stderr and GNU-time logs remain local because they contain verbose
provider diagnostics; their admitted status, timing, RSS, output/token
digests, configuration, and cleanup telemetry are preserved row-by-row in the
published manifest.

Published artifact digests:

- manifest: `75415f6b9d0cc7c0a539d893b1783bb401b06abe32c2389f20a2a147495bc230`;
- identity: `e7bb3f9ce0fa7798ca8fa74fe3c782b70f1a1df1674cce1ea8654bc45bb1fa77`;
- parity: `91ae3dce1f5703a2baa17cca8ad6290449a4204cf979ff1c3c72ac3c29020af7`;
- Markdown summary:
  `495ea6abf2becd2657e625482b9aa45ba18b575686bc5ee69846f2a9abfedc97`;
- TSV summary:
  `4c60db066a25afbc73fb87cd05e37c3b7bfa84dddecaec0217484fa0c19ad6d5`.

The identity receipt records the ARM CPU models directly and binds the full
CPU identity receipt without altering the completed benchmark artifacts.
