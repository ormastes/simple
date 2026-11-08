# Stage2 native-build: unresolved symbol 'byte_len'

READY FOR OPUS REVIEW. Severity P1. Status: open (verification-pending for none).

Repro (Windows, seed = release/1.0.0 c4a6c6ac91f + #7857):
  seed.exe native-build --target x86_64-pc-windows-gnu --backend llvm --runtime-bundle core-c-bootstrap --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/cli/bootstrap_main.spl -o out.exe
Observed: link retry logs 'Unresolved symbol preview: byte_len' (a bare str method name emitted as a call target); stage2 #4 earlier failed on 80 files with 'cannot resolve str.byte_len' when the seed lacked b7402b5e486 dispatch.
Expected: str.byte_len dispatches to the string runtime; no free symbol byte_len.
Workaround: WA-s2n8/9 stub generation hides it (stub aborts if called). Evidence: C:/dev/p3new/stage2new/build4.log.err.
Needed: find the call site lowering str.byte_len to a bare symbol; add repro spec + similar-method tests.

## 2026-11-09 root cause and fix (fix-implemented-verification-pending)

Root cause is in the Rust seed's LLVM backend, not in the Simple compiler
(stage2 is built BY the seed with `--backend llvm`). The seed's MIR emits a
BARE `byte_len` (`MethodCallStatic { func_name: "byte_len" }` / `Call {
target: "byte_len" }`) for `.byte_len()` on a receiver whose static type it
did not pin. Two LLVM gates only recognised the owner-qualified spelling:

- `codegen/llvm/functions.rs`: `text_byte_len = resolved_text_runtime_method(func_name) == Some("rt_string_len")`
  requires an `owner.method` form, so the `"byte_len" if text_byte_len` table arm never fired for the bare leaf.
- `codegen/llvm/functions/calls.rs`: the `bare_rt_redirect` table had no `byte_len` arm.

Before #7873 the bare leaf on an erased receiver was suffix-matched to any
same-leaf user method; #7873 correctly fails that closed, so the call now falls
through to an undefined `byte_len` extern. Cranelift (`codegen/instr/calls.rs`)
already maps the bare leaf to `rt_string_len`; LLVM did not match it. No user
`fn byte_len` exists anywhere under `src/`, so the leaf is unambiguous.

Fix: both LLVM routes map a bare `byte_len` to `rt_string_len` (one-arg byte
ABI) under the existing guards: no arguments; receiver STRING/ANY/UNKNOWN; a
proven non-text receiver is a semantic error.

Repro/prevention: `bare_byte_len_dispatches_to_text_byte_abi_for_text_and_erased_receivers`
(`codegen/llvm/functions.rs`). Red: probe IR contained `declare i64 @byte_len(i64)`.
Green: `call i64 @rt_string_len(i64 ...)`. Native verification = stage2 relink
with a seed rebuilt from the fix.
