# Windows external SPipe alias pending policy omission

Status: OPEN

Corrected checkout diagnostic38171850248 passed the former placeholder blocker then failed on domain_expert. Six tracked doc aliases resolve inside the external SPipe gitlink absent from nonrecursive checkout. Add exact path and target pairs only; production predicate accepts all six and rejects changed targets and arbitrary pending paths. Complete native materialization remains unexecuted.
