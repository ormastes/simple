# Windows native capture evidence prerequisite specimen

Status: **NOT_RUN**, one source-authored scenario. Corresponding source:
`test/01_unit/lib/io/process_capture_evidence_windows_native_v1_spec.spl`.

Required setup: actual native canonical Windows-thread runner, installed
`C:/Windows/System32/whoami.exe`, explicit clean SystemRoot environment and
cwd, and a genuine sampled Unix expiry. Missing setup fails; this cannot
silently pass on Linux or under a scripted owner.

The scenario executes real readonly whoami through the existing canonical
Windows command reducer, with at most512 fixture turns and10ms scheduling
yields in test code. Actual per-stream/combined EOF, terminal and positive
cleanup retirement are checked. Unsupported seen/truncation/POSIX-reap/raw
native-error/identity facts remain nil. Actual raw bytes remain available if
localized output is not UTF8; no lossy text or empty success is substituted.

The original owner is retained for bounded after_each cleanup, and admission
refuses to overwrite any prior retained owner. The production Windows step
adds no Sleep or positive wait. The case is NOT_RUN. Partial handle/heap/
pipe/termination failures, canonical cross-thread faults, actual ABI/link and
scheduler behavior, managed provider/logs and live engines are NOT_COVERED.
