# simple_db__(examples/11_advanced/simple_db/src/engine/tier_cache.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPOSTGRE-M4-001"></a>FR-SPOSTGRE-M4-001 | L2 NVMe tier cache (Aurora Optimized Reads pattern) | When a clean DRAM page is about to be evicted from `BufferPool`, write it to a DB_TEMP arena on local NVMe instead of discarding it. On subsequent page fault, | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
