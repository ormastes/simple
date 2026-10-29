# Darwin strict descendant authority

Source: `test/03_system/check/sosix_darwin_strict_tree_authority_spec.spl`.

The native checker runs six adversarial process-tree fixtures: `setsid`,
`setpgid`, and double fork, each after leader exit and group kill. Every escaped
descendant responds after group retirement, cannot be reaped by the observer,
and is retired through a pipe with kernel exit notification. The checker also
confirms Darwin rejects recursive kqueue tracking. A bounded Seatbelt probe
reports whether process creation denial is available.

The strict checker exits 78 because no OS-enforced all-descendant owner is
installed. SSpec requires that failure plus every escape marker. Passing this
spec verifies honest refusal, not strict containment or V4 capability.

Native check passed on Darwin 25.5.0. P1 diagnostic SSpec: one test executed and
passed with no skips or drops. P2 release qualification remains outstanding.
