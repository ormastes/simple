# `src/os/services/netstack/tcp_connection.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0002"></a>FR-NET-0002 | Complete TCP data path wakeups and close/error semantics | Finish the pure Simple TCP data path so socket send/recv operations have observable readiness, bounded buffering, peer close handling, RST propagation, and retransmission/timeout errors suitable for HTTP workloads. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
