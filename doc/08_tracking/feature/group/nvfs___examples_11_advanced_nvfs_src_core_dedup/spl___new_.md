# nvfs__(src/os/services/nvfs/src/core/dedup.spl_—_new)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NVFS-N7b-001"></a>FR-NVFS-N7b-001 | Inline deduplication: content-addressable DDT extending reflink machinery | Add an inline deduplication layer (N7b) backed by a content-addressable Deduplication Table (DDT). The DDT maps `content_hash (u8[32]) → DedupEntry` where DedupEntry carries the canonical logical_page_no, birth_gen, refcount, and flags (56  | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
