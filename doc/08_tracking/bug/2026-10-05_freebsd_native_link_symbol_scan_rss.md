# FreeBSD native link symbol scan crosses the RSS cap

Status: scoped source repair with focused Rust unit tests; full FreeBSD Phase 2 remains unqualified.

## Observed failure

- Frozen FreeBSD source `fc979ade9d6fc3dc3d395f4e7e50d3f621e96f35` compiled 1,198 modules, reused none, and failed its Stage 2 native build after the compile summary. The retained `stage2-native-build.log` and `.rss.env` are under `/home/yoon/dev/simple-freebsd-phase2-qemu-20261003/build/freebsd/phase2-run-20261003/terminal-fc979-llvm-attempt3/`. The process-tree RSS guard recorded peak 8,204,976 KiB against 5,859,375 KiB, exit 88.
- `_main_stub.o` exists in the preserved native-object directory, while `_init_all.c`, `_init_all.o`, the linker response file, and final executable do not. The Rust `native_project` path runs `generate_init_caller` immediately after compiling the main stub. It invokes `nm -g` once per input object through `Command::output()` before writing `_init_all.c`.
- A controlled FreeBSD probe used a Rust parent with 4,294,967,296 touched bytes and the same watchdog. A `Command::output()` sleep completed; repeated `nm -g` against one preserved 555,697-byte object reached one completed call before the guard exited 88 at 8,411,520 KiB. Probe source, log, and receipt are retained at `/home/yoon/dev/simple-rss-spawn-probe-20261005/`. The guard sums process RSS; no per-PID sample was retained, so inherited/shared page double-counting is a supported inference, not a measured child allocation breakdown.

## Scoped repair and limits

The Rust native linker now reads global and undefined symbols from ELF relocatable objects in-process with its existing `object` dependency. Global names retain nm-style sorted order; undefined results include weak references. Malformed ELF parsing fails closed. Archives and non-ELF formats still use the existing external tool path, including its type-letter and symbol-order behavior.

Two focused compiler unit tests passed under a 6 GiB host cap with two build jobs: parity against `nm -g` for a real object with a weak undefined symbol, and rejection of a truncated ELF header while retaining archive fallback. Log: `/home/yoon/dev/simple-rust-link-symbol-rss-evidence-20261005/cargo-focused.log`. These tests do not establish that a new Stage 2 binary links under the FreeBSD cap.

The planned same-cap in-process FreeBSD probe was not run: its standalone Cargo setup selected vendored `object` 0.37.3, while the compiler uses 0.36.7, and dependency resolution stopped before compilation. The failure log is `/home/yoon/dev/simple-rss-spawn-probe-20261005/inprocess-build.log`; the feature's three-cycle limit prevents another attempt in this session.

Remaining external subprocesses include archive symbol scans, C stub/runtime compilation, and the final linker. Their RSS behavior under the large parent is unmeasured. Rebuild and qualify the corrected producer and complete FreeBSD Phase 2 before claiming the RSS failure resolved or running downstream six-product tests.
