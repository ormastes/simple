# Requested Features

**Database:** `doc/08_tracking/feature/feature_db.sdn`

| ID | Group | Priority | Title | Requirement | External |
|----|-------|----------|-------|-------------|----------|
| FR-WM-GLASS-WIN-0001 | wm_glass | P0 | Prove Windows Vulkan and SIMD WM glass parity | [link](doc/02_requirements/feature/wm_glass_theme_host_simpleos.md; doc/02_requirements/nfr/wm_glass_theme_host_simpleos.md) | - |
| FR-WM-GLASS-LINUX-0001 | wm_glass | P0 | Prove Linux Vulkan RenderDoc and SIMD WM glass parity | [link](doc/02_requirements/feature/wm_glass_theme_host_simpleos.md; doc/02_requirements/nfr/wm_glass_theme_host_simpleos.md) | - |
| FR-WM-GLASS-X86-QEMU-0001 | wm_glass | P0 | Prove x86 QEMU WM glass rendering and events | [link](doc/02_requirements/feature/wm_glass_theme_host_simpleos.md; doc/02_requirements/nfr/wm_glass_theme_host_simpleos.md) | - |
| FR-WM-GLASS-ARM-QEMU-0001 | wm_glass | P0 | Prove ARM QEMU WM glass rendering and events | [link](doc/02_requirements/feature/wm_glass_theme_host_simpleos.md; doc/02_requirements/nfr/wm_glass_theme_host_simpleos.md) | - |
| FR-GPU-QEMU-0001 | simpleos_gpu | P0 | Complete cross-host QEMU GPU acceleration | [link](doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md; doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md) | - |
| FR-GPU-BOARD-0001 | simpleos_gpu | P1 | Add UNO Q Adreno 702 native GPU adapter | [link](doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md; doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md) | - |
| FR-GPU-BOARD-0003 | simpleos_gpu | P1 | Add UP Squared N4200 Intel native GPU adapter | [link](doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md; doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md) | - |
| FR-COMPILER-013 | compiler_—_native_list_concat_lowering | P1 | Lower builtin `list + [item]` to fresh-copy push | - | - |
| FR-DRIVER-0003 | lexer_+_parser_+_hir_+_struct_layout | P2 | Native bitfield syntax `struct Foo @packed { a: u16:4 }` | - | - |
| ECDSA_P384_P521_RUNTIME_PRIMITIVES_2026_05_02 | ecdsa | P2 | ECDSA-P-384 + ECDSA-P-521 primitives for TLS 1.3 | - | - |
| EDITOR_MARKDOWN_EDITING_SUBSYSTEM_2026_05_28 | `app/editor`_+_`lib/editor` | medium | Editor markdown-editing subsystem (for full TUI render) | - | - |
| ENGINE2D_TRAIT_FACADE_BACKEND_EXECUTION_2026_06_02 | engine2d | P2 | Engine2D Facade Must Preserve Backend Pixel Mutations | - | - |
| HKDF_RFC5869_2026_05_01 | hkdf | P2 | HKDF RFC 5869 Implementation | - | - |
| HTTPS_SERVER_INTERPRETER_EXTERNS_2026_05_28 | https | P2 | HTTPS Server — Pure Simple TLS Record-Layer | - | - |
| P256_SCALAR_MULT_CONSTANT_TIME_2026_05_01 | p256 | P2 | Constant-time P-256 scalar multiplication | - | - |
| FR-PLUG-0002 | plugin_/_15.blocks | P1 | `.so` block-proxy constructor for `activate_plugin` | - | - |
| FR-PLUG-0003 | plugin_/_15.blocks_/_10.frontend.desugar | P1 | Sugar registry AST round-trip | - | - |
| FR-PLUG-0004 | plugin_/_70.backend.cranelift | P2 | Static lowering / fusion of sugar rules through Cranelift | - | - |
| FR-PLUG-0002-2 | plugin | P2 | FR-PLUG-0002 (structural) — `.so` block-proxy constructor | - | - |
| FR-PLUG-0003-2 | plugin | P2 | FR-PLUG-0003 (structural) — Sugar registry AST round-trip | - | - |
| FR-PLUG-0004-2 | plugin | P2 | FR-PLUG-0004 (verification only) — Static lowering markers | - | - |
| FR-RISCV-TP-INIT-2026-05-02 | riscv | P2 | FR-RISCV-TP-INIT-2026-05-02: Wire tp Register at Baremetal Boot for Per-CPU Base | - | - |
| FR-RISCV-HAL-PROD-WIRING-2026-05-02 | riscv | P2 | FR-RISCV-HAL-PROD-WIRING-2026-05-02: Wire Real Production Bodies for HalSmp/HalCache | - | - |
| RSA_PSS_PURE_SIMPLE_MODEXP_PERF_2026_05_02 | rsa | P2 | Pure-Simple RSA modexp interpreter perf cliff | - | - |
| SCILIB_PERF_SUGAR | scilib | P0 | Scilib Perf-Sugar Wedge Tracker | - | - |
| SHA512_256_FOR_DIGEST_AUTH_2026_05_02 | sha512 | P2 | FR: SHA-512/256 for HTTP Digest Auth (RFC 7616) | - | - |
| SIMD_INT_INTRINSICS_FOR_CRYPTO_2026_05_01 | simd | P2 | Feature: extend SIMD surface with int bitwise / rotate / shuffle ops for crypto | - | - |
| SIMD_U32X4_I64X4_INTRINSICS_2026_05_02 | simd | P2 | FR: Vec4u32 and Vec4i64 SIMD Intrinsics | - | - |
| FR-WEBRENDER-001 | `simple_web_html_layout_renderer.spl` | P1 | Generic-HTML layout render speed under the interpreter | - | - |
| FR-WEBRENDER-002 | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/` | P2 | Pixel-level test coverage for the generic layout path | - | - |
| FR-WEBRENDER-003 | `simple_web_html_layout_renderer.spl`_+_`browser_renderer.spl` | P2 | Chrome-compatible text antialiasing / CSS coverage | - | - |
| FR-SPIPE-LLM-0001 | spipe_llm_fine-tune_retry_loop_/_medgemma_korean | P1 | Run fixed-format/data-quality retry | [link](doc/02_requirements/language/tools/spipe_llm_finetune_process.md; doc/02_requirements/nfr/spipe_llm_finetune_process.md) | - |
| FR-SPIPE-LLM-0002 | spipe_fine-tune_readiness_gate | P1 | Require target-reaching eval before acceptance | [link](doc/02_requirements/language/tools/spipe_llm_finetune_process.md; doc/02_requirements/nfr/spipe_llm_finetune_process.md) | - |
| FR-SPIPE-LLM-0003 | llm-backed_medical_qa_app/server_handoff | P1 | Add medical safety and deployment evidence | [link](doc/02_requirements/language/tools/spipe_llm_finetune_process.md; doc/02_requirements/nfr/spipe_llm_finetune_process.md) | - |
| FR-SPIPE-LLM-0004 | spipe_llm_fine-tune_retry_loop_/_medgemma_korean | P1 | Obtain licensed fixed-format data cache | [link](doc/02_requirements/language/tools/spipe_llm_finetune_process.md; doc/02_requirements/nfr/spipe_llm_finetune_process.md) | - |
| FR-SPIPE-LLM-0005 | spipe_llm_fine-tune_retry_loop_/_medgemma_korean | P1 | Run real QLoRA retry after data gate | [link](doc/02_requirements/language/tools/spipe_llm_finetune_process.md; doc/02_requirements/nfr/spipe_llm_finetune_process.md) | - |
| STATIC_FILE_COMPRESSION_CACHE_INTEGRATION_2026_05_01 | static | P2 | Wire StaticCompressionCache into StaticFileHandler.handle() | - | - |
| FR-SPIPE-LLM-0006 | spipe_llm_fine-tune_retry_loop_/_medgemma_korean | P1 | Promote retry7 acceptance only after real evidence | [link](doc/02_requirements/language/tools/spipe_llm_finetune_process.md; doc/02_requirements/nfr/spipe_llm_finetune_process.md) | - |
| FR-LLM-RUNTIME-0001 | llm_runtime_vllm_torch_interface | P1 | Prove live local vLLM serving | [link](doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md; doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md) | - |
| FR-LLM-RUNTIME-0002 | llm_runtime_vllm_torch_interface | P1 | Complete Slang NVFS streaming adapters | [link](doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md; doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md) | - |
| FR-LLM-RUNTIME-0003 | llm_runtime_vllm_torch_interface | P1 | Prove live CUDA Torch optimizer execution | [link](doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md; doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md) | - |
