# Slang KV-cache matched evidence

Date: 2026-09-09
Measured source: `5bbdd24b224060586891772a4fba6d297b6bbe6d`
Result: **PASS**

The matched real-model run completed 50 fresh-process samples: five workloads,
five paired repetitions, and both snapshot and physical-page lanes. All 50
samples passed the per-sample token, telemetry, and cleanup gates. All 25 pairs
had identical output digests and generated-token vectors.

| Workload | Snapshot median ms | Physical median ms | Snapshot max RSS KiB | Physical max RSS KiB |
|---|---:|---:|---:|---:|
| cold | 27 | 29 | 312896 | 287556 |
| exact repeat | 39 | 43 | 313016 | 288984 |
| prefix extension | 42 | 61 | 312964 | 294056 |
| alternating prefix | 74 | 102 | 313060 | 298472 |
| eviction pressure | 181 | 226 | 313600 | 296848 |

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

The raw local evidence remains under `build/perf/slang-kv-cache/` and is bound
by these digests:

- manifest: `51e6883ae2f31aa62f9f5f005a02210bb0bba84df1e2a8e051b4102e49da0d68`;
- identity: `f3c396d24d52c85914259edb5b348907db8ba3c1a7273bc473d219ce0f8e65e2`;
- parity: `91ae3dce1f5703a2baa17cca8ad6290449a4204cf979ff1c3c72ac3c29020af7`;
- Markdown summary:
  `ffd1132507931152fbef3050deda0c5aa31bb34ba7f138ad91c0ce809a61f758`;
- TSV summary:
  `a40f68b2892c9e2e9f940d4a87521605e5dfef12a623afaccc998a62ab7b18fd`.

The identity receipt records the ARM CPU models directly and binds the full
CPU identity receipt without altering the completed benchmark artifacts.
