# Admit the current Rust dependency-cache owner

Status: focused Cranelift cache regression PASS; full bootstrap qualification pending.

The canonical Stage2 source-refresh path pinned native_project/mod.rs SHA256
67ffbc45c28f92d2e7112840c07f3c2b63095ceaf1c51b0b627d1523682d40f0.
The current source is 5e566362d85041b93f3ae9a8e11733f099adfdebc3dd04172c7b7aafc9cb7f37.
Independent review of the complete difference found target-selection propagation
and imported method-default fingerprint additions; module content and global
dependencies remain unconditional key inputs. Update only the exact reviewed
owner pin. Unknown owners still fail closed. Producer equality, runtime/tool
identity, writer exclusion and immutable transition records remain required.

The existing real Rust source-refresh regression assumed LLVM, unavailable in
the installed admitted Cranelift seed. Add explicit fixture backend selection,
defaulting to LLVM, allowing only LLVM/Cranelift and binding the selected backend
in both command and cache context.

Actual execution on 2026-10-12 with seed SHA256
18f2d4094f07b3192b66b1a5ae2160e5983340a8155d81514ea3f8c5972f1349:
ordinary changed-source reuse refused; body change compiled 1/cached 1; cross-module
layout change compiled 2/cached 0; archive bytes changed. Exit 0. Evidence:
/root/item5-cache-admission-regression-cl-20261012, including command, logs and
resource watchdog receipt. The preceding LLVM-only attempt exited 1 before
compilation and is retained at /root/item5-cache-admission-regression-20261012.

This is a bootstrap-only cache regression, not Phase2/Phase3 or runtime admission.
The failed full-build evidence and its 1290 durable objects remain untouched.
Any later source refresh must archive predecessor component snapshots, retain
the old outer attempt receipts, and let the compiler validate all object keys.
No fresh full bootstrap was launched after the prior three-cycle stop.
