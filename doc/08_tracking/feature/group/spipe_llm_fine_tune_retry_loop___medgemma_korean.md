# spipe_llm_fine-tune_retry_loop_/_medgemma_korean

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPIPE-LLM-0001"></a>FR-SPIPE-LLM-0001 | Run fixed-format/data-quality retry | Execute the retry attempt | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-SPIPE-LLM-0004"></a>FR-SPIPE-LLM-0004 | Obtain licensed fixed-format data cache | Complete retry5 by recording licensed data access, cache path, and checksum evidence | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-SPIPE-LLM-0005"></a>FR-SPIPE-LLM-0005 | Run real QLoRA retry after data gate | Run real QLoRA/eval only after licensed data cache evidence exists | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
