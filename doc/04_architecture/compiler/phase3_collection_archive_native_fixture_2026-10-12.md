# Nonempty collection archive lifecycle fixture

The `collection` selector of `hir-body-typecheck-lease-native.shs` requires
20 positive native checks. It uses the existing launcher's exact admitted
producer/runtime-capsule verification, source/fixture/variant snapshots, private
cache owner, fixed 5,859,375 KiB cap and 600-second compile bound. No producer is
available for this source yet; these checks are authored and statically inspected,
not compiled or executed.

The fixture parses and lowers complete physical function declarations, retaining
their actual SymbolTable ownership and source spans. It installs the explicit
typed/resolved bodies from existing map-filter and canonical loop test cases:
a map-filter chain with real lambda argument bodies, and a fresh array followed
by a for/append loop with a literal mapping. Fresh local identities come from
the actual SymbolTable allocator. These are diagnostic HIR fixtures, not claims
that the archive adapter itself performs method resolution or callback analysis.

Registry SDN rows use real `hir_abi_function_digest_v1` values and actual function
SymbolIds, receiver/arity, source paths and backend. The registry evidence text
explicitly identifies fixture content rather than production optimization
admission. The same actual parsed/bound registry feeds retained analysis and
archived capture/replay. Matching metadata does not invent callback purity,
alias, escape or profitability proofs.

Positive assertions require exactly two nonempty plans: one maximal three-node
source/map/filter chain and one two-node source/map canonical loop. The callback
lambda literal 43 and mapped loop literal 17 are read while leases live. A full
operand/origin codec observation includes original source expressions, call
arguments and spans, complete original loop block/loop/mapped expression and
the induction/accumulator/append identities. Its digest must match retained
analysis before and after a second-scope 4,096-string churn. Only scalar/text
observations are promoted; complete plans and expressions never leave the lease.

Controls reject inactive and paused replay, preserve an occupied parent scope,
reject changed registry source, plans count, binding signature, backend and
complete body descriptor, and exercise actual retained/archive route switching
and failed reconfiguration. A later physical module has a real stored archive
and complete declaration whose ABI differs from the requested bound operation.
Registry content binding succeeds, then actual typed signature validation fails
in the second module. Both published analysis maps must remain empty despite
the first module's nonempty capture.

This depends on root collection adapter `a7b8b4c` and the actual borrowed reader
`411f2c4`, based on source8 `e87569c98f8a3304841dbb00f881a5612ff78c08`.
Static guard/diff/shell/count checks do not qualify native ownership, source
closure admission, the full archived route or the full CLI RSS requirement.
