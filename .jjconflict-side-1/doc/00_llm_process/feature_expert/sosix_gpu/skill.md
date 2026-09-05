# SOSIX-G Feature Expert

Use `doc/01_research/local/sosix_gpu_api_extension_final_report.md` for the frozen SOSIX-G research and `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md` for implementation ownership.

The semantic center is a typed asynchronous SOSIX operation model. GPU and compatibility APIs are façades, not parallel implementations. Start with `TRACE_WRITE`, `FS_READ_AT`, `FS_WRITE_AT`, and `CANCEL`; pre-open capabilities and registered buffers; no blocking device call or silent direct-data fallback.

QEMU acceptance must use the canonical descriptor and `src/os/sosix/qemu_evidence/matrix_contract.spl` for its typed 24-cell contract, prove guest boot, mount, target-side `ls`, and an arbitrary in-guest program, and retain exact provenance. Resolve storage through the shared resolver/config contract and run the shared settings check. External host rows remain blocked until fresh native evidence exists.

WM/renderer boundary research is `doc/01_research/local/sosix_wm_renderer_host_interface.md`. SOSIX owns async host display/input/timer/file/process services; Draw IR, layout, rasterization, Engine2D, and transient GPU material remain in their canonical rendering owners.
