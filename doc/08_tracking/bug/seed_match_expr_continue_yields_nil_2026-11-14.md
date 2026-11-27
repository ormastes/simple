# Seed interpreter: `continue` inside a `val x = match` arm yields nil and does not continue

Status: verification-pending (workaround applied; seed fix not done)
Found by: lane nodeattr, baseline of `data_schema_resolver_v2_spec` (24/25 -> 25/25)

## Repro
```
for k in [1]:
    val x = match o:        # o = None
        case Some(v): v
        case None:
            out.push("none")
            continue
    out.push("after {x}")   # runs, x is nil
```
Seed-tip prints `none,after nil`; expected `none`. A statement-level `match` with
`continue` and `return` in a `val x = match` arm (`case None: return "ret"`) work.

## Impact
`data_schema_sdn_common_v1.spl` (SDN decode of `attributes`, `tree`, `view`) fell through
with nil and raised `method is_dict not found on type nil`.

## Workaround (tagged SEED-WORKAROUND in source)
Statement-level `match` assigning a `var`, with `continue` in the failing arm.

## Neighbouring pattern to grep
Any other `val x = match ...:` whose arm ends in `continue`/`break` (generalisation spec TBD).
