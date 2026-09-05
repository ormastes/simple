# Vulkan Engine2D Readback Evidence

- status: fail
- reason: evidence-program-failed
- spec status: not_run
- probe status: 
- available: 
- backend: 
- present exercised: 
- readback exercised: 
- clear status: 
- clear pixels: 
- clear expected checksum: 
- clear actual checksum: 
- clear mismatches: 
- clear source: 
- clear backend handle: 
- clear device identity: 
- clear expected pixels: 
- clear actual pixels: 
- rect status: 
- rect pixels: 
- rect expected checksum: 
- rect actual checksum: 
- rect mismatches: 
- rect source: 
- rect backend handle: 
- rect device identity: 
- rect expected pixels: 
- rect actual pixels: 
- blur/tolerance used: false
- vulkan strict exit code: 
- cpu/vulkan parity exit code: 
- execution mode: interpret
- Vulkan ICD: 

## Raw Evidence
- vulkan_engine2d_readback_status=fail
- vulkan_engine2d_readback_reason=evidence-program-failed
- vulkan_engine2d_readback_spec_status=not_run
- vulkan_engine2d_readback_probe_status=
- vulkan_engine2d_readback_available=
- vulkan_engine2d_readback_backend_name=
- vulkan_engine2d_readback_present_exercised=
- vulkan_engine2d_readback_readback_exercised=
- vulkan_engine2d_readback_clear_status=
- vulkan_engine2d_readback_clear_pixels=
- vulkan_engine2d_readback_clear_expected_checksum=
- vulkan_engine2d_readback_clear_actual_checksum=
- vulkan_engine2d_readback_clear_mismatches=
- vulkan_engine2d_readback_clear_source=
- vulkan_engine2d_readback_clear_backend_handle=
- vulkan_engine2d_readback_clear_device_identity=
- vulkan_engine2d_readback_clear_expected_pixels_path=
- vulkan_engine2d_readback_clear_actual_pixels_path=
- vulkan_engine2d_readback_rect_status=
- vulkan_engine2d_readback_rect_pixels=
- vulkan_engine2d_readback_rect_expected_checksum=
- vulkan_engine2d_readback_rect_actual_checksum=
- vulkan_engine2d_readback_rect_mismatches=
- vulkan_engine2d_readback_rect_source=
- vulkan_engine2d_readback_rect_backend_handle=
- vulkan_engine2d_readback_rect_device_identity=
- vulkan_engine2d_readback_rect_expected_pixels_path=
- vulkan_engine2d_readback_rect_actual_pixels_path=
- vulkan_engine2d_readback_blur_or_tolerance_used=false
- vulkan_engine2d_readback_vulkan_strict_exit_code=
- vulkan_engine2d_readback_cpu_vulkan_parity_exit_code=
- vulkan_engine2d_readback_execution_mode=interpret
- vulkan_engine2d_readback_icd_path=
- vulkan_engine2d_readback_evidence_log=build/vulkan-engine2d-readback/evidence.log
- vulkan_engine2d_readback_vulkan_strict_log=build/vulkan-engine2d-readback/vulkan_strict.json
- vulkan_engine2d_readback_cpu_vulkan_parity_log=build/vulkan-engine2d-readback/engine2d_cpu_vulkan_parity.json

## Evidence Log
- timeout: the monitored command dumped core
- Segmentation fault

## Follow-up diagnosis

- The deployed `release/x86_64-unknown-linux-gnu/simple` crashes before script
  execution in `startup.launch_metadata.startup_normalize_program_args`; its
  gdb stack is `cli_run_file` → `cli_handle_run` → `CliMain.main`.
- A direct current-source Engine2D capture artifact also cannot be used as
  evidence: its one-thread bootstrap build emitted unresolved support stubs and
  then faulted through a null function pointer.
- The fresh Rust bootstrap runner reaches `renderdoc_available=1`, but JIT
  lowering fails with `Unknown type: DrawIrRenderTarget`, then reports
  `BACKEND_UNAVAILABLE backend unavailable: vulkan` in interpreter fallback.
- With the default loader path, Mesa llvmpipe loads LLVM 20 into the Rust
  bootstrap process (which statically links LLVM 18) and crashes in
  `llvm::cl::AddLiteralOption`. Setting
  `VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/intel_hasvk_icd.json` selects the
  Intel hardware ICD and removes that LLVM collision. It does not resolve the
  Draw-IR JIT/lowering blocker.
