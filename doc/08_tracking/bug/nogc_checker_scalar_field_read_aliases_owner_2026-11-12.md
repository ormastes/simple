# nogc checker: scalar copy of a field read is treated as the owner (false NOGC-OWN-002)

- Status: open
- Area: src/compiler/35.semantics/param_effects/infer.spl (caller-side local scan)
- Repro: test/01_unit/compiler/semantics/param_effects/nogc_contract_behaviour_gaps_spec.spl
  ("accepts a local whose transfer is its last use")

```
fn caller2(xs: [Node]) -> i64:
    val b = Node(v: 2)
    val keep = b.v      # i64 copy
    ps(xs, b)           # b consumed (last use of b)
    keep                # flagged NOGC-OWN-002 "used again after it was consumed"
```

Observed: `NOGC-OWN-002 ... :22: class local is used or consumed again after it was consumed`
(line 22 = `keep`). Expected: no diagnostic; `keep` is a scalar value, not an alias of `b`.
Mutation-family impact: "move replaced by copy" negative twin cannot get an accepting twin.
