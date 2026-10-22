# Conditional impl queues an unproved generic bound then reports success

Source-confirmed: solve_trait_bound previously constructed TypeParam from a HirSymbol (current constructor expects text), added an obligation, and returned Ok. solve_obligation cached parent success; solve_all iterated pending obligations then cleared them. Missing concrete child proofs could therefore disappear. Existing matches_type also failed actual Named binder representation and did not reconcile repeated assignments.

External repair derives declared impl binder assignments during candidate selection, recursively proves children before parent success, and detects active cycles. Adjacent same-path cache poisoning fixed: associated-query failures/successes no longer write unconstrained predicate cache. Public APIs and declaration-level ambiguity policy retained.

Nine real API scenarios authored before qualification, UNRUN. No compiler or test run launched. Full HM generic bound integration, associated generic substitution, runtime cost and broader generics remain open. This packet does not alter completed historic campaigns.

Revision2 addresses independent source finding SOLVER-CLOSURE-001: whole binder self-validation dropped binder/table authority, allowing unresolved Box<T> through blanket conditions. The new regression also uses an unrelated real TypeParam row; valid Box<i64> remains accepted. Source correction only, execution pending.
