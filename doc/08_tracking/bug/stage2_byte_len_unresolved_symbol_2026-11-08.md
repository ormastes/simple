# Stage2 native-build: unresolved symbol 'byte_len'

READY FOR OPUS REVIEW. Severity P1. Status: open (verification-pending for none).

Repro (Windows, seed = release/1.0.0 c4a6c6ac91f + #7857):
  seed.exe native-build --target x86_64-pc-windows-gnu --backend llvm --runtime-bundle core-c-bootstrap --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/cli/bootstrap_main.spl -o out.exe
Observed: link retry logs 'Unresolved symbol preview: byte_len' (a bare str method name emitted as a call target); stage2 #4 earlier failed on 80 files with 'cannot resolve str.byte_len' when the seed lacked b7402b5e486 dispatch.
Expected: str.byte_len dispatches to the string runtime; no free symbol byte_len.
Workaround: WA-s2n8/9 stub generation hides it (stub aborts if called). Evidence: C:/dev/p3new/stage2new/build4.log.err.
Needed: find the call site lowering str.byte_len to a bare symbol; add repro spec + similar-method tests.
