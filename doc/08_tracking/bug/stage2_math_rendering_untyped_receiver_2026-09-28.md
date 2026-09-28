# Stage 2 rejects untyped math rendering receiver

Status: OPEN. This blocks a current-main Stage 2 candidate independently of the dynlib lifetime owner HIR failure.

On Windows MSVC at `e465b19cc00a706c487d788e1830cfa9ce91c001`, the admitted Rust seed compiled 1,043 files and rejected `src/lib/nogc_sync_mut/src/math/rendering.spl` during LLVM code generation: `cannot resolve method call to_latex: receiver is a builtin type but to_latex is neither a known runtime method nor a resolvable user definition`. The helper takes an untyped `expr` and calls `to_latex`, `to_mathml`, `to_text`, and `to_lean`; no Simple implementation of those methods was found in the local math module. Full evidence: `D:/dev/simple-windows-bootstrap-20260927/build/bootstrap/windows-linux-20260927/windows/logs/x86_64-pc-windows-msvc/stage2-native-build.log`.

A separate narrow native build reported this same source blocker earlier in `adaptive_map_nil_payload_key_presence_2026-09-27.md`. Fix the rendering contract with a concrete supported receiver or trait, add a focused native compilation test, then rerun Stage 2. Do not remove its public exports without an API decision.
