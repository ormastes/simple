# Nominal generic arguments bypass declaration defaults and arity

Status: source candidate and parsed regressions independently approved;
executable owner qualification pending. No canonical type-identity,
compiler, bootstrap, or test-suite PASS is claimed.

## Defect and semantic owner

At release base `12905eac283ce8676dabaca1767fb01fc5307f1c`,
`HirLowering.lower_named_symbol_kind` normalizes aliases through their parser
parameter templates, declaration owner/scope, and earlier actual arguments.
Normal nominal symbols immediately return `Named(symbol, supplied_arguments)`.
Thus a parsed `struct Box<T = i64>` lowers `Box` with zero actual arguments
and `Box<i64>` with one, although both designate the same instantiation.
Excess arguments and missing required arguments also escape this owner.

`HirSymbol.generic_param_count` is callable metadata; its default zero cannot
authorize nominal arity. Completed HIR declarations arrive too late for
forward/self field references. Early authoritative parser declaration facts
are needed before field/signature lowering.

## Repair

Append a defaulted, SymbolId-keyed nominal declaration registry to
`HirLowering`, retaining parser parameters, declaration module, and scope.
Publish local class/struct/enum/trait facts and empty bitfield parameters in
the declaration pass; publish imported composite/enum/trait facts when their
canonical symbols are registered. Imported owner-default dependencies use the
existing dependency owner. `begin_module` drops all nominal facts alongside
alias facts before transient reclamation and SymbolId reuse.

Aliases and nominal applications now share `lower_named_symbol_kind`'s arity,
default substitution, cycle detection, and saved/restored declaration frame.
Fully supplied nominal arguments keep their existing HIR values after arity
validation. Missing defaults are evaluated using earlier actuals and the
defining module/scope, preserving consumer shadows and ownership checks.
Nominal applications retain their nominal symbol; aliases retain expansion.
Missing defaults that name their own or a later formal are rejected before
name resolution: a module-level decoy or legacy single-letter Any fallback
must not turn an unavailable binder into a concrete descriptor. Earlier
actuals remain available; explicit actuals do not evaluate unused defaults.
Constructor inference and explicit owner receivers still use their existing
separate paths; no backend adapter or callable-arity workaround is introduced.

## Parsed regressions and parser dependency

`test/01_unit/compiler/hir/nominal_generic_arguments_spec.spl` contains 15
authored scenarios: parsed struct/class defaults, dependent defaults and
overrides, four invalid arities, forward fields, explicit self parameters,
generic constructor inference, lexical shadowing, imported owner defaults
under differing SymbolId allocation, alias/nested-default composition,
recursive defaults, module reset, and local/imported enum defaults.
Self/forward formal defaults also test module decoys and explicit overrides,
with the same rule exercised through a parsed generic alias.
They inspect actual parser parameter facts and resulting HIR arguments,
declaration IDs, diagnostics, and restored scopes/bindings. No manually
injected defaults substitute for parsed-source evidence.

The canonical `_ParserDecls/fn_struct_decls.spl` rich parameter parser and
flat bridge preserve struct/class defaults. The legacy
`core/parser_decls_fn.spl` is not authority for current grammar. Enum default
transport is a separate Sol MIR repair: this lane's two real parsed enum
cases require its canonical parser/bridge change to land first. This lane
does not change frontend files or claim enum transport is already qualified.
The parsed generic-alias guard also requires the independently landed alias
parser/bridge repair, PR #7581; this worktree's original base predates it.
Packaging must retain both parser prerequisites before landing the HIR tests.

## Qualification and limits

No admitted source-matched self-hosted runtime is available or invoked here;
all 15 owner scenarios remain unexecuted. A seed fallback is not used.
Source review and whitespace checks cannot establish canonical completion.
Runtime owner tests, compiler/lib/MCP checks and applicable core/native smoke
remain required once an admitted producer exists. Active bootstrap sources,
caches, and live jobs are untouched.

Independent reviewer `/root/astra_linker_final` approved the seven-path source
candidate and authored scenarios with no remaining blocking/P0/P1 findings.
Review corrected an initially misplaced registry field, an invalid assertion
about completed binder metadata lifetime, and default-formal shadow capture.
The approval is source-only and does not qualify exact descriptors, compiler
execution, native code, or producer admission.

No new grammar, enum parser transport, bound satisfaction, generic constructor
inference algorithm, or backend identity adapter is implemented by this patch.
The registry lookup is O(1). Normalization visits the declaration's parameters
and active expansion stack; each missing default's parser dependency walk is
compared with its current/later formal names. No repository scan or subprocess
is introduced on the type-lowering path.
