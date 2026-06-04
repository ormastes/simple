# `src/lib/nogc_async_mut/io/packet_ring.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0010"></a>FR-NET-0010 | Add bounded ring-buffer data structure for packet RX/TX paths | Provide a pure Simple power-of-two ring buffer with push/pop/peek and a batch-drain operation bounded by a per-quantum budget. The ring must make empty vs full unambiguous via the head==tail convention and expose a one-line CI-log summary. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
