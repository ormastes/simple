# SOSIX actual provider boundary — authored manual

Source: `test/02_integration/io/sosix_tool_text_spec.spl`. Eleven scenarios, all UNRUN; no generated/native evidence claimed. Prerequisite: admitted native fixture at an absolute `SIMPLE_SOSIX_TEXT_FIXTURE` path and POSIX provider.

Cases cover missing/empty/multilingual/malformed environment values and NUL mutation refusal; actual cwd/directory names; bare resolver and nonzero child exit; malformed capture/legacy error and command preflight; exact NUL capture and invalid caps; native console stdout/stderr exact byte order; fatal legacy malformed environment with typed witness; bounded repeated conversions and oversized rejection; raw malformed directory entry; malformed resolver output; provider timeout and output-truncation markers.

The fixture's raw invalid inputs intentionally use existing low-level provider APIs. Temporary files are removed on the tested successful path, environment values restored in the parent API case; child-only PATH mutation does not alter the parent environment. Native fixture failure may require ordinary test artifact cleanup, never build-cache cleanup.

Requirements UTF8-SOSIX-01,03,05..10. Stdin/PTY/Windows Unicode providers and explicit arbitrary-encoding process capture remain open; no substitute test or skipped success covers them. Performance workload is authored only; no RSS/latency bound is qualified.
