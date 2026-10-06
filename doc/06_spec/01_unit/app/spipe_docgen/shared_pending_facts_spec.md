# Docgen shared lexical facts preserve pending ownership

Source: `test/01_unit/app/spipe_docgen/shared_pending_facts_spec.spl`.

1. Count a source with one conditional placeholder and one unconditional placeholder. Expect one active scenario, zero skipped scenarios, and one pending scenario.
2. Compute canonical CoreLexer continuation facts for a scenario containing a column-zero multiline fixture followed by `pass_todo`. Expect the scenario to remain pending; an invalid negative scenario index remains false.

Phase1 qualification: the first case passed once in the original two-case run. The second initially failed, exposing the closing-fixture toggle defect, then passed in a selected one-case run after the owner repair. No unchanged green case was rerun. Seed-hosted evidence does not qualify a pure compiler.
