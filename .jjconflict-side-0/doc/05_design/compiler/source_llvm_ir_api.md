# Source-to-LLVM IR detail design

<!-- codex-design -->

## API

`CompilerSourceLlvmIrResult` contains:

- `module_names: [text]`
- `module_irs: [text]`
- `entry_module_name: text`
- `target_triple: text`
- `bare_metal: bool`
- `error: text`
- `exit_code: i64`

The arrays have equal length on success and are empty on failure. Convenience
methods expose success and module count without copying either array.

## Pipeline

1. Validate and normalize the explicit target triple and policy.
2. Create AOT/LLVM driver options for the single entry source.
3. Load and parse the source closure.
4. Lower/typecheck HIR and monomorphize.
5. Lower every loaded HIR module to MIR using the explicit target context;
   bootstrap skip/fabrication shortcuts are disabled for this path.
6. Run borrow, async, optimization, AOP, and debug passes.
7. Allocate result arrays to `sources.len()` and translate each MIR module with
   the same explicit target scalars. The requested entry is resolved by
   physical source identity; discovery order is not treated as authority.
8. Reject missing modules or empty emitted IR and return no partial success.

## CLI materialization

Every unit receives a deterministic index plus sanitized-module suffix.
Object/link modes invoke `llc` once per unit and pass the complete object array
to the linker. `llvm-ir` and `object` with an explicit single output reject
multi-unit results. Linked outputs require a source-owned `_start`; the facade
never invents an entry wrapper.

## Contract coverage

Two fixture programs have distinct constants. The contract requires
successful, exact-triple IR, each authored constant, unequal IR text, and no
stub marker. An additional case covers bare-metal policy mismatch.
