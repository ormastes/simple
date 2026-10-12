# Native callable assert resolves to incompatible libc symbol

Status: repair authored; structural and native tests UNEXECUTED.

The retained separate_methods native probe returned 111 through the trait
call, then crashed in libc __assert: the Simple bool argument 1 was treated
as a char pointer. The strict native linker generated an assert compatibility
alias because __assert matched its suffix despite having no Simple owner.
Evidence: /root/simple-block-next-regression-zpqdp5cv/separate_methods/diagnosis.
Probe SHA256: 5f22557b44c40032a813b29885c78dafc66d9b7a6b725afd7588f00fd3a56ea1.

Reject reserved platform suffix targets and empty module-owner matches.
Normalize only unshadowed one-positional-argument statement calls assert(x)
to the existing HIR Assert / MIR ContractCheck owner. Preserve declared and
imported callable owners, local-context bindings, other arities, named args,
and expression contexts. No new runtime ABI or libc wrapper.

Required native gates: true fixture sentinel and exit 0 (condition called
exactly once); false fixture controlled assertion failure, nonzero exit, no
SIGSEGV and no unreachable sentinel; declared assert(false) executes its own
function and emits the global-shadow sentinel. Rebuild and run the original
separate_methods fixture unchanged as well. Rust structural tests cover
true/false HIR assertion ownership, declared callable shadowing and reserved
suffix refusal; existing module-owner positive and ambiguity tests remain.

Bare val assert bindings are currently unsupported parser grammar (Assert
keyword, no identifier allowance); no native local-shadow claim is made.
The existing ctx.lookup exclusion remains defensive for valid AST contexts.
No test PASS, Phase3 qualification, or release admission is claimed.
