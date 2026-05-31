# Vector Font Compute Matrix Evidence

- status: pass
- iterations per scene: 1

| text run | font size | status | reason | CUDA glyphs | OpenCL glyphs | GPU returned glyphs | CPU fallback hits | report |
|---|---:|---|---|---:|---:|---:|---:|---|
| HARDENED | 24 | pass | pass | 4 | 4 | 8 | 0 | doc/09_report/vector_font_compute_hardened_24_evidence_2026-05-31.md |
| HARDENED | 16 | pass | pass | 4 | 4 | 8 | 0 | doc/09_report/vector_font_compute_hardened_16_evidence_2026-05-31.md |
| GUIWM | 24 | pass | pass | 3 | 2 | 3 | 0 | doc/09_report/vector_font_compute_guiwm_24_evidence_2026-05-31.md |
| GUIWM | 32 | pass | pass | 3 | 2 | 3 | 0 | doc/09_report/vector_font_compute_guiwm_32_evidence_2026-05-31.md |
| CUDAOPENCL | 16 | pass | pass | 5 | 5 | 9 | 0 | doc/09_report/vector_font_compute_cudaopencl_16_evidence_2026-05-31.md |
| FontRender | 32 | pass | pass | 5 | 5 | 9 | 0 | doc/09_report/vector_font_compute_fontrender_32_evidence_2026-05-31.md |
