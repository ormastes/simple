# Vector Font Compute Matrix Evidence

- status: pass
- scope: expanded
- iterations per scene: 1

| text run | font size | kernel params | status | reason | CUDA glyphs | OpenCL glyphs | GPU returned glyphs | GPU returned pixels | CPU fallback hits | report |
|---|---:|---|---|---|---:|---:|---:|---:|---:|---|
| PIPELINESTATUSOK | 24 | CUDA 4x64 / OpenCL 4:1 | pass | pass | 8 | 8 | 14 | 3048 | 0 | doc/09_report/vector_font_compute_pipeline_status_ok_24_evidence_2026-06-01.md |
| VECTORFONTGPU | 36 | CUDA 5x32 / OpenCL 5:1 | pass | pass | 7 | 6 | 10 | 5328 | 0 | doc/09_report/vector_font_compute_vectorfontgpu_36_evidence_2026-06-01.md |
| GPUREADBACKWM | 12 | CUDA 3x16 / OpenCL 3:1 | pass | pass | 7 | 6 | 10 | 624 | 0 | doc/09_report/vector_font_compute_gpureadbackwm_12_evidence_2026-06-01.md |
