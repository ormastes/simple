# Slang KV-cache matched evidence

Date: 2026-09-09
Measured source: `7c5d29b0fe7e9b26f3763c02a83bff0b63b8452e`
Result: **PASS**

The matched real-model run completed 50 fresh-process samples: five workloads,
five paired repetitions, and both snapshot and physical-page lanes. All 50
samples passed the per-sample token, telemetry, and cleanup gates. All 25 pairs
had identical output digests and generated-token vectors.

| Workload | Snapshot median ms | Physical median ms | Snapshot max RSS KiB | Physical max RSS KiB |
|---|---:|---:|---:|---:|
| cold | 101 | 84 | 311976 | 286412 |
| exact repeat | 196 | 164 | 312260 | 288312 |
| prefix extension | 200 | 308 | 313024 | 293876 |
| alternating prefix | 338 | 487 | 311132 | 297092 |
| eviction pressure | 543 | 555 | 312528 | 295520 |

These observations establish correctness and matched execution evidence; they
do not establish a universal physical-page speedup.

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
- Requested context: 128. llama.cpp clamped every observed context, batch, and
  micro-batch to 1024; all 50 stderr receipts yielded exactly
  `n_ctx=1024,n_batch=1024,n_ubatch=1024`.
- Backend SHA-256:
  `eeecb47392952acc1b232f430824a2f9834eec14b46d3972dc81ddd15525197b`.
- llama provider SHA-256:
  `f50adb6dbc197b4c65d301316974454d8949a8e94589fde085f64412be6ed426`.

## Evidence receipts

The raw local evidence remains under `build/perf/slang-kv-cache/` and is bound
by these digests:

- manifest: `805b7004cb5cd6ecf297e7c9bfc1096c2571060b3bfb2f11bc52b25fce9b9853`;
- identity: `6c32112eacdea6dfad28327674bac75430cc3d56297c91011d527c4beb8653f6`;
- parity: `a4d416694f7bb250ba8be2cefc30f36a6e023ed4bc2a5397e917d053ce35e89c`;
- Markdown summary:
  `dd1004b31d8beeaadff6e8aa88b777fa45894fc1fd8021d35e23879fb77c9d24`;
- TSV summary:
  `972918eae1e1781ebc2c74e580bca444274988d64211dd1bd00177a301bcfb6c`.

The original identity receipt's `cpu_model` field is blank because this ARM
host does not publish a matching `model name` entry through `/proc/cpuinfo`.
The independently hashed `lscpu` receipt above supplies the missing CPU
identity without altering the completed benchmark artifacts.
