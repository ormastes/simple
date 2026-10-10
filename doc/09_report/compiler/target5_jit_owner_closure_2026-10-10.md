# Item 5 JIT owner closure continuation (2026-10-10)

The compiler interpreter imported the application JIT facade, while that facade implemented an in-process fallback using compiler driver modules. The implementation now lives at `src/compiler/95.interp/execution/jit_sffi.spl`; `src/app/io/jit_sffi.spl` re-exports it for existing clients. The backend boundary allowlist and its owner-path test follow the implementation.

The widened kernel closure checker moved from **2237 classified, 3 K0→P, 0 K1→P, 10 kernel→app/OS, 0 unresolved** to **2238 classified, 3 K0→P, 0 K1→P, 9 kernel→app/OS, 0 unresolved**. Both runs remain FAIL because other forbidden edges remain. Receipts: `build/mini_builds/item5_kernel_closure_{current,jit_owner}_20261010/`.

A no-stub Stage 2 LLVM/core-C probe imports the app compatibility export and compiler owner. Its first build lacked `src/plugins` in the source set and failed on an unresolved VHDL import. The corrected build parsed all 1009 files; HIR terminal receipts for the moved owner, app export, and probe passed. The aggregate build stopped with 12 other failed HIR modules before native linking (`build/mini_builds/item5_jit_owner_native_probe_fullsources_20261010/`). The probe did not run. This change has **no claimed binary-size, startup, RSS, or demand-load pass**.

Next: resolve the aggregate HIR blockers in the full source closure, run the compatibility probe, and complete the remaining kernel edges and Item 5 provider/size gates.

## Bounded diagnostic continuation

Pure-Simple Stage 2 candidate `4188084e40682302038ec51ebeb51181403320d71804ec383d5472890bee9a8d` passed parent sanity/provenance, but the outer compiler tests again stopped at the unsupplied MC/DC waiver. The third no-stub JIT fixture build reproduced 12 failed HIR modules with 42 existing `[hir-fatal]` diagnostics, grouped under `ImplBlock`, `MirType`, `SymbolId`, and `MirSignature`. The edited owner, app export, and fixture HIR receipts passed, but no executable was linked. See `doc/08_tracking/bug/item5_jit_probe_hir_type_closure_2026-10-10.md`. The verification cap is exhausted for this lane in this session.
