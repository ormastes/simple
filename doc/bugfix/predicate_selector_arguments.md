# Predicate selector argument append

C34's native architecture-rules fixture stopped in HIR with unresolved
`args_push` at `src/compiler/00.common/predicate_parser.spl:80` and `:93`.
Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c34-native-arch-rules-attempt1/arm/build.log`;
the coordinated C34 source is identified by prefix `20a932`.

The tokenizer declares `args: [text]`. It appends a trimmed, nonempty argument
at a comma with depth zero and at the selector's closing parenthesis. There
is no predicate-parser helper named `args_push`. Both calls now use the normal
array operation `args = args.push(current.trim())`, consistent with the
tokenizer's existing `tokens = tokens.push(...)` calls. Argument order,
whitespace trimming, empty-argument omission, nested-parenthesis depth and
nested-comma preservation are unchanged. No private helper is imported from
another compiler subsystem.

The native fixture `test/fixtures/compiler/predicate_selector_arguments/main.spl`
checks both append sites with two-argument import/depend selectors, preserves
a call signature containing two nested parenthesis levels and inner commas,
checks omission of whitespace-only arguments, and checks the public parser's
ordered `Selector.Import` payload. It uses the production tokenizer/parser.

Native validation is pending a coordinated changed-source producer. No build
or unchanged failed fixture rerun was performed for this patch. Next gate is
ARM compilation/execution with exit zero and exact output
`predicate_selector_arguments: PASS`, followed by a genuine explicitly targeted
LLVM 18 RISC-V object check (ELF machine 243). The existing architecture-rules
fixture should then be qualified with the same changed-source producer and
isolated caches. Stop on the first semantic failure. The parser's preexisting
`text` signatures on Result-returning functions are not corrected here; any
new diagnostic must be retained as a separate proven failure. This source
repair does not assert parser readiness or release verification PASS.
