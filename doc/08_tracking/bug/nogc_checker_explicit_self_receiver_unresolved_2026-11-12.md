# nogc checker: method with explicit `self: &T` consuming receiver is not resolved (NOGC-AMB-004, no NOGC-OWN-003)

- Status: open
- Area: src/compiler/35.semantics/param_effects/infer.spl `_receiver_offset` / `_summary_for_method`
- Repro: test/01_unit/compiler/semantics/param_effects/nogc_contract_behaviour_gaps_spec.spl (REQ-MEM-3-6)

```
impl Node:
    fn into_next(self: &Node) -> &Node:
        self
fn drop_it(n: &Node):
    n.into_next()        # expected NOGC-OWN-003 (discarded new owner)
```

Observed: `NOGC-AMB-004 ... receiver passed to `into_next` without a checked non-retaining or
consuming contract` for both the discarding and the rebinding (`val m = n.into_next(); m`) form;
the rebinding form also reports line 0. `_receiver_offset` returns 0, so the receiver summary is
never consulted and NOGC-OWN-003 (`_scan_discarded_expr`) is unreachable from source.
Either the consuming-receiver spelling differs (then the plan §3.6 example needs the real one) or
same-module impl methods are missing from `ctx.method_ids`. Hand to a Fable fix lane.
