# async_http_server,_memory_registration,_and_network_backend_layer

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0006"></a>FR-NET-0006 | Prototype RDMA/exoskeleton transport for web serving | Add an opt-in RDMA transport experiment for controlled deployments where web responses can use registered memory, queue pairs, and completion queues outside the normal TCP socket path. The default Simple web server must remain TCP-compatibl | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
