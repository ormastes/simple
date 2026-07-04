# Vector Font Compute Matrix Evidence

- status: pass
- iterations per scene: 1

| text run | font size | status | reason | CUDA glyphs | OpenCL glyphs | GPU returned glyphs | GPU returned pixels | CPU fallback hits | report |
|---|---:|---|---|---:|---:|---:|---:|---:|---|
| HARDENED | 24 | pass | pass | 4 | 4 | 8 | 1896 | 0 | doc/09_report/vector_font_compute_hardened_24_evidence_2026-05-31.md |
| HARDENED | 16 | pass | pass | 4 | 4 | 8 | 784 | 0 | doc/09_report/vector_font_compute_hardened_16_evidence_2026-05-31.md |
| GUIWM | 24 | pass | pass | 3 | 2 | 3 | 720 | 0 | doc/09_report/vector_font_compute_guiwm_24_evidence_2026-05-31.md |
| GUIWM | 32 | pass | pass | 3 | 2 | 3 | 1248 | 0 | doc/09_report/vector_font_compute_guiwm_32_evidence_2026-05-31.md |
| CUDAOPENCL | 16 | pass | pass | 5 | 5 | 9 | 896 | 0 | doc/09_report/vector_font_compute_cudaopencl_16_evidence_2026-05-31.md |
| FontRender | 32 | pass | pass | 5 | 5 | 9 | 3296 | 0 | doc/09_report/vector_font_compute_fontrender_32_evidence_2026-05-31.md |
| TASKBAR | 20 | pass | pass | 4 | 3 | 6 | 1000 | 0 | doc/09_report/vector_font_compute_taskbar_20_evidence_2026-05-31.md |
| COMMAND | 28 | pass | pass | 4 | 3 | 7 | 2380 | 0 | doc/09_report/vector_font_compute_command_28_evidence_2026-05-31.md |
| STATUSOK | 18 | pass | pass | 4 | 4 | 6 | 792 | 0 | doc/09_report/vector_font_compute_statusok_18_evidence_2026-05-31.md |
