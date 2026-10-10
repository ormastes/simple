# Item 5 JIT owner closure continuation (2026-10-10)

The compiler interpreter imported the application JIT facade, while that facade implemented an in-process fallback using compiler driver modules. The implementation now lives at `src/compiler/95.interp/execution/jit_sffi.spl`; `src/app/io/jit_sffi.spl` re-exports it for existing clients. The backend boundary allowlist and its owner-path test follow the implementation.

The widened kernel closure checker moved from **2237 classified, 3 K0→P, 0 K1→P, 10 kernel→app/OS, 0 unresolved** to **2238 classified, 3 K0→P, 0 K1→P, 9 kernel→app/OS, 0 unresolved**. Both runs remain FAIL because other forbidden edges remain. Receipts: `build/mini_builds/item5_kernel_closure_{current,jit_owner}_20261010/`.

A no-stub Stage 2 LLVM/core-C probe imports the app compatibility export and compiler owner. Its first build lacked `src/plugins` in the source set and failed on an unresolved VHDL import. The corrected build parsed all 1009 files; HIR terminal receipts for the moved owner, app export, and probe passed. The aggregate build stopped with 12 other failed HIR modules before native linking (`build/mini_builds/item5_jit_owner_native_probe_fullsources_20261010/`). The probe did not run. This change has **no claimed binary-size, startup, RSS, or demand-load pass**.

Next: resolve the aggregate HIR blockers in the full source closure, run the compatibility probe, and complete the remaining kernel edges and Item 5 provider/size gates.
