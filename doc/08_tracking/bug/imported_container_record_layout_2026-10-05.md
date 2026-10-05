# Selective imports leave record layouts incomplete behind containers

The diagnostic Windows Phase 2 build of source `4cdcac162777388806e27ce99821686335e70c27`
with seed `46174b33357c448534e2a747d626094df6064361aa5d4f139c731baaf451c2d3`
finished with 1,176 compiled modules, zero reused modules and three failures.
Two failures were `ElfSymbol.name` in `linker/elf/tls_relax.spl` and
`smf_group_object_adapter.spl`. The separate `SymbolId.name` failure has another
owner. The build exited 1, with an enforced RSS peak of 3,350,780 KiB,
quiescence verified and no observer errors; it did not produce an executable.

Both ELF consumers selectively import `ElfObject`. Its `symbols: [ElfSymbol]`
field refers to a sibling declaration which is not explicitly imported.
The Rust bootstrap import loader creates placeholders for all sibling types,
but its transitive registration pass only inspects direct struct/enum fields.
It does not traverse the array element, leaving `ElfSymbol` incomplete.
The compilation closure contains three distinct `ElfSymbol` declarations;
`name` is at slot 6 in the parser and slot 0 in the other two. Selecting a
layout by bare spelling or common field name would therefore be incorrect.

The repair follows container TypeId edges in the existing transitive pass,
with a visited set for recursive graphs. Definitions are still registered
from the current imported declaration file. Global layout ambiguity checks,
unknown-field rejection, import selection and the existing ten-pass bound
remain in effect. No consumer import workaround or arbitrary field offset
is introduced.

Six focused Rust regressions cover selective array and nested-array imports,
dictionary values, optional array payloads, recursive record/container graphs,
and rejection of an undeclared field. Positive selective-import cases supply
conflicting global layouts and assert the actual HIR field slot and declaring
module identity. These checks and a rebuilt bootstrap producer are pending
execution at this checkpoint. Native qualification is not claimed.

Evidence: `runtime/windows-restart-20261004/p2-next4cdcac-cranelift80/`;
terminal log SHA-256 `85c9ea5af709de5225c2a1fe539bece9c497cb05042936e0b08a900f442f88be`.
The failed packet and compiled object cache remain unchanged.
