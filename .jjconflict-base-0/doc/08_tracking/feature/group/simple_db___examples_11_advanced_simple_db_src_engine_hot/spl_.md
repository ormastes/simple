# simple_db__(examples/11_advanced/simple_db/src/engine/hot.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-HOT-001"></a>FR-HOT-001 | HOT: integrate pd_upper/pd_lower free-space check before chaining | `HotChain.try_update` currently chains a HOT update unconditionally at the logical-page-group level. A real PostgreSQL HOT update is only valid when the page has sufficient free space (pd_upper − pd_lower > tuple_size). The | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
