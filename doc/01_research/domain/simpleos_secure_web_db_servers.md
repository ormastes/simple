<!-- codex-research -->
# SimpleOS secure web and database servers — domain research

## Benchmark controls

- nginx comparisons must pin worker count/affinity, `reuseport`, sendfile/AIO, keep-alive, protocol/TLS, logging, payload, concurrency, warm-up, and client capacity. Report latency distributions, failures, CPU, and RSS as well as throughput. Sources: [nginx core](https://nginx.org/en/docs/http/ngx_http_core_module.html), [nginx HTTPS](https://nginx.org/en/docs/http/configuring_https_servers.html), [h2load](https://nghttp2.org/documentation/h2load-howto.html).
- PostgreSQL comparisons need identical schema, data, durability, and read/write scripts. Run multi-minute repeated `pgbench` trials, size scale for concurrency, monitor vacuum/contention, and ensure the client is not the bottleneck. Source: [PostgreSQL pgbench](https://www.postgresql.org/docs/current/pgbench.html).
- SSR needs separate render-only and live TTFB/FCP/LCP/INP rows, cold/warm cache, representative DOM/data, streaming, semantic/hydration correctness, and pixel evidence. Source: [Rendering on the Web](https://web.dev/articles/rendering-on-the-web).

## GPU boundary

CPU event loops and sharded state come first. GPU offload should batch coarse independent work; transfer and launch overhead commonly defeats small operations. GPUDirect-class networking additionally depends on suitable GPU/NIC topology, drivers, queues, and privileges and is not implied by QEMU. Sources: [CUDA best practices](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/), [DOCA GPUNetIO](https://docs.nvidia.com/doca/sdk/doca-gpunetio/).

## Cryptographic baseline

- TLS 1.3 baseline: [RFC 8446](https://www.rfc-editor.org/info/rfc8446/).
- ML-KEM parameter sets and vectors: [NIST FIPS 203](https://csrc.nist.gov/pubs/fips/203/final).
- TLS hybrid X25519MLKEM768 is still an Internet-Draft; pin the implemented draft/version and group encoding: [draft-ietf-tls-ecdhe-mlkem](https://datatracker.ietf.org/doc/draft-ietf-tls-ecdhe-mlkem/).
- OpenSSH supplies the `mlkem768x25519-sha256` interoperability oracle: [OpenSSH release notes](https://www.openbsd.org/openssh/releasenotes.html).

Correctness gates precede performance: KATs, independent-oracle differential tests, malformed ciphertext/implicit-rejection behavior, certificate and host-key authentication, then native paired ABBA trials. Benchmark handshake, resumed session, steady-state traffic, SSH exec/SFTP, and crypto primitives separately. GPU rows require physical-device receipts and batch-size crossover curves.

