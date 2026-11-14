# Seed: bare list-literal tail expression after a `match` val is parsed as an index

Date: 2026-11-14
Status: open (workaround applied by lane xrayfg; verification-pending once the seed is fixed)

`val r = match x:` with a `case _: ""` last arm, followed by a function-tail list
literal `["p=" + r, "q=" + r]`, fails in the seed (`seed-attr`, `seed-tip`) with
`Unexpected token: expected RBracket, found Comma`: the `[` is taken as a subscript of the
preceding arm value. It fails identically with the list on one line, so it is not a
multi-line-continuation problem. Repro: two-arm match then a bare list tail.

Hit at release/1.0.0 `cda4d2d059a`: `target_profile_identity_fields_v1` in
`src/compiler/00.common/driver_compile_options.spl` (introduced by PR #9219), which made every
pure-Simple compile under the seed fail at module load. Workaround (tagged `SEED WORKAROUND
(xrayfg)`): bind the list to `val fields` and return `fields`. Fix belongs in the seed parser;
add a spec that a bare list tail after a match-bound val parses.
