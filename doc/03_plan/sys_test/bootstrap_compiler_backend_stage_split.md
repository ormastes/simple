<!-- codex-design -->
# Bootstrap compiler/backend stage split system-test plan

1. Stage 2 selects Cranelift and emits a valid compiler receipt.
2. Stage 3 selects LLVM and binds the exact Stage-2 receipt.
3. Stage 4 reports zero compiler files and links exact Stage-3 archives.
4. Mutated source, interface, archive, runtime ABI, and receipt hashes fail
   before tool compilation.
5. Tooling-only and audit-full CLIs pass identical essential-tool and behavior gates.
6. Migration stays fail-fast until the prerequisite legacy PASS receipt exists.
