# Bootstrap planner admission v2 contract

The focused contract constructs a structurally complete but shell-forged body
without executing the planner. The public verifier rejects it because no
non-circular admitted producer exists.

Negative cases reject a duplicate field, an arbitrary target, a reason that is
not valid for the selected stage, an unbound cache key, post-capture planner
mutation, a symlinked evidence path, and an authorization receipt that does not
bind the admitted parent, runtime, source closure, and planner hashes.

This is negative contract evidence only. It does not claim that a planner
binary was built, smoked, admitted, run, or published.
