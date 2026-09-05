# Robust lint lane scan exceeds bounded verification time

Status: Open

After repairing split profile parsing and lint admission, running robust lint
over `src/lib/nogc_async_mut` produced no terminal verdict or filtered SFFI
diagnostic within 120 seconds and was stopped. Per-file robust checks terminate,
so the defect is in directory-scale discovery/execution rather than SFFI009 or
SFFI010 semantics.

The migration workaround is the source-only SFFI call-authority census. It
scans the complete owned source/test tree in 24.21 seconds with 7,424 KiB peak
RSS and supports a fail-on-missing gate. It is deliberately not called from a
runtime hot path.

Required fix: profile directory lint with phase timings, reuse parsed/compiler
state across files, avoid repeated module loading, and add a realistic warm
latency/RSS release gate. Do not weaken or skip AST lints to meet the target.
