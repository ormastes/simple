# Architecture rules common predicate ownership

The C33 whole-HIR run failed to resolve the bare `predicate` and
`predicate_parser` imports in `src/compiler/70.backend/arch_rules.spl`.
`src/compiler/00.common/__init__.spl` exports their surfaces through
`compiler.common.predicate` and `compiler.common.predicate_parser`.
The backend module now imports those explicit owners, keeping every imported
symbol and all rule behavior unchanged. The parser's own sibling import stays
unchanged. No resolver aliases or additional consumer imports are introduced.

## Frozen failure evidence

- C33 source: `a9646f08c4b3f58712a0b8d6e752c211ebe061dd`.
- Producer SHA-256: `f993254fccf459616d227ffe8bb62ccd6dd18ca4992edf30e7d0c4f25fef14bd`.
- Failing source SHA-256: `cec907f164eac488d79c49308e14eefadbe4c363a268bd4bb15c835c1fbf776c`.
- Evidence directory: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c33-cold-hir-cold-prime-attempt1/`.
- Diagnostics: `c33-six-hir-failures-readonly-triage.json`; canonical log:
  `canonical-whole-phase3/build.log`.
- Five diagnostics identify both missing module surfaces, two unresolved
  `Predicate` types, and unresolved `parse_predicate` at line 160.

## Scope and regression

The repair starts from release `c5c40973968cfbbe4df58e17909de83bc36fea03`.
Search of compiler, plugin and composition sources found the backend facade
reexporting architecture rules, without a separate ARM/RISC-V consumer or
implementation needing another import correction. This is a shared backend
module repair; it does not change target-specific instruction selection.

`test/fixtures/compiler/arch_rules_common_owner/main.spl` constructs predicates
from the common module, stores them in backend `ArchRule` values and retrieves
them through `ArchRulesConfig`. It checks empty/disabled configuration, rule
ordering and metadata, both actions, and positive/cross-negative matching of
ARM and RISC-V instruction-selector module paths. It calls the real predicate
matcher. Target names in the data do not constitute target execution evidence.
The fixture does not claim to exercise architecture-block parsing; preexisting
parser return-type/integration limitations are outside this import repair.

## Validation status: pending native qualification

No compiler construction or native test ran for this patch. Disk constraints
require the coordinated C34 producer before runtime qualification. Next gate:
compile this unchanged fixture with explicit compiler/library/fixture source
roots and its entry closure, private producer/entry/target caches and the
admitted runtime. On ARM require exit 0 and the exact
`arch_rules_common_owner: PASS` output. Then compile an LLVM 18 object with
explicit `--target riscv64-unknown-linux-gnu --emit-object` and verify ELF
machine RISC-V (243). An object is not RISC-V execution. Stop on the first
semantic failure and retain the diagnostics. Whole-HIR confirmation and the
required compiler/library/MCP/SSpec gates remain pending; this report is not a
release PASS.
