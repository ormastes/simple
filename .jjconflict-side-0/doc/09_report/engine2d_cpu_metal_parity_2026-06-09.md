# Engine2D CPU vs Metal Bit-Level Parity

- status: pass
- reason: cpu-metal-bitexact
- verdict: pass
- policy: exact bitmap, no blur, no tolerance
- harness: test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl

## Scenes
- clear: MATCH mismatches=0/1024 gpu_ok=true
- rects: MATCH mismatches=0/1024 gpu_ok=true
- gradient: MATCH mismatches=0/1024 gpu_ok=true
- line: MATCH mismatches=0/1024 gpu_ok=true
- circle: MATCH mismatches=0/1024 gpu_ok=true
- rounded_rect: MATCH mismatches=0/1024 gpu_ok=true
- triangle: MATCH mismatches=0/1024 gpu_ok=true
