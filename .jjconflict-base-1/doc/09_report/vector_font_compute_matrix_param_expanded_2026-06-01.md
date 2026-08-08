# Vector Font Compute Matrix Evidence

- status: in-progress
- iterations per scene: 1

| text run | font size | kernel params | status | reason | CUDA glyphs | OpenCL glyphs | GPU returned glyphs | GPU returned pixels | CPU fallback hits | report |
|---|---:|---|---|---|---:|---:|---:|---:|---:|---|
| HARDENED | 24 | CUDA 2x32 / OpenCL 2:1 | pass | pass | 4 | 4 | 8 | 1896 | 0 | doc/09_report/vector_font_compute_hardened_24_evidence_2026-06-01.md |
| HARDENED | 16 | CUDA 1x64 / OpenCL 1:1 | pass | pass | 4 | 4 | 8 | 784 | 0 | doc/09_report/vector_font_compute_hardened_16_evidence_2026-06-01.md |
| GUIWM | 24 | CUDA 2x16 / OpenCL 2:1 | pass | pass | 3 | 2 | 3 | 720 | 0 | doc/09_report/vector_font_compute_guiwm_24_evidence_2026-06-01.md |
| GUIWM | 32 | CUDA 3x32 / OpenCL 3:1 | pass | pass | 3 | 2 | 3 | 1248 | 0 | doc/09_report/vector_font_compute_guiwm_32_evidence_2026-06-01.md |
| CUDAOPENCL | 16 | CUDA 2x64 / OpenCL 4:1 | pass | pass | 5 | 5 | 9 | 896 | 0 | doc/09_report/vector_font_compute_cudaopencl_16_evidence_2026-06-01.md |
| FontRender | 32 | CUDA 4x32 / OpenCL 4:1 | pass | pass | 5 | 5 | 9 | 3296 | 0 | doc/09_report/vector_font_compute_fontrender_32_evidence_2026-06-01.md |
| TASKBAR | 20 | CUDA 2x32 / OpenCL 2:1 | pass | pass | 4 | 3 | 6 | 1000 | 0 | doc/09_report/vector_font_compute_taskbar_20_evidence_2026-06-01.md |
| COMMAND | 28 | CUDA 3x64 / OpenCL 3:1 | pass | pass | 4 | 3 | 7 | 2380 | 0 | doc/09_report/vector_font_compute_command_28_evidence_2026-06-01.md |
