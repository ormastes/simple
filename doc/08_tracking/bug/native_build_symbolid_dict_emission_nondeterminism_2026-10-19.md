# Nondeterministic native output: Dict<SymbolId, _> emission order follows key addresses

- Status: fixed (compiler emission sites sort canonically)
- Severity: P1 — breaks every hash-pinned artifact re-verification, including
  the stage-3/4 planner admission receipt flow
- Found: 2026-10-19, release_phase3, x86_64-unknown-linux-gnu, LLVM lane

## Symptom

Building the planner twice with the admitted stage-2 compiler, identical
source, identical cache directory:

```
$ sha256sum planner1 planner2   # four runs, four distinct binaries
5ef10ce0… planner3   a07989bc… planner4
```

`nm` shows the module's own functions (`planner_reason_allowed`,
`planner_sha256_allowed`, `planner_file_write`, `planner_arg_value`) laid out
in a different order per run. The stage-4 planner receipt pins
`planner_sha256`; any rebuild (e.g. a second `produce-…-v2.shs` invocation
sharing the admission scope) changes the bytes and the next
`bootstrap-from-scratch.sh --bootstrap-receipt=…` run dies with
`bootstrap-policy-error: planner-admission-v2-unbound`.

## Root cause

`rt_core_dict_hash` (src/runtime/runtime_native.c) hashes string keys by
content (FNV-1a) and integer keys by value, but falls back to the raw pointer
word `(uint64_t)k` for any other heap key. `SymbolId` is a heap struct, so
`Dict<SymbolId, _>` slot order — and therefore `.values()` iteration order —
follows allocation addresses and ASLR, varying per process.

Two-line demonstration (native, core-c-bootstrap runtime):

```
struct K: id: i64
var d: Dict<K, i64> = {}
... 30 inserts ...
for pair in d: print(pair.0.id)   # different order every run
```

## Fix

Compiler emission sites now iterate module contents in canonical name order:
`mir_module_functions_sorted` / `mir_module_statics_sorted`
(src/compiler/50.mir/mir_instruction_graph.spl, exported through
`compiler.mir.mir_instructions`), used by the LLVM translator
(`_MirToLlvm/core_codegen.spl`, including the statics emission) and the
Cranelift driver (`70.backend/codegen.spl`). Sort key is the function/static
name with the symbol id as tiebreak, matching the existing
`hardware_functions_sorted` precedent in the VHDL lane.

Dict-with-heap-key address hashing itself is unchanged: it is the documented
C-runtime behaviour, and other consumers may still observe per-process order.
Sites whose iteration order leaks into bytes must order explicitly.

## Verification

`src/compiler/bootstrap_admission/` dict-order probe: two stage-2-compiled
binaries printed different iteration orders before the fix; after the stage-2
rebuild with this change, planner rebuilds are byte-identical (see PR
evidence).
