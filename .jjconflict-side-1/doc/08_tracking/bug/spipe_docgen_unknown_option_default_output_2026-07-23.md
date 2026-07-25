# spipe-docgen ignored unknown options and wrote default output — 2026-07-23

- **Impact:** a misspelled output option could report success while generating
  into canonical `doc/06_spec` instead of the requested isolated directory.
- **Root cause:** the pure-Simple argument loop discarded unrecognized
  dash-prefixed arguments.
- **Fix:** reject every unrecognized option before filesystem generation.
- **Regression:** `spipe_docgen_scenario_body_spec.spl` pins `--outpt` to a
  nonzero exit with no default generated manual. The temporary seed runner
  reported `no examples executed`; run this unchanged scenario with the next
  admitted pure-Simple runner before crediting runtime qualification.
