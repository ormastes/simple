# Open-ended Range MIR condition

Executable: `test/01_unit/compiler/mir/open_range_cfg_spec.spl`.

The two cases construct real HIR endpoints and invoke production `MirLowering.lower_for_range`, then inspect the generated `for_range_cond` terminator. An absent endpoint must produce `Goto` into the body; a present endpoint must retain `If` for the bound comparison. This checks actual generated MIR, rather than testing an implementation text search.

Evidence: Phase1 seed diagnostic, declared2 executed2 passed2 failed0 skipped0 dropped0. Parser-to-module harness attempts failed before this owner-level harness; retained logs document them. No self-hosted execution is claimed.

Native fixture: `test/fixtures/bootstrap/open_range_break.spl` uses the parser-accepted parenthesized `(1..)` form, breaks at 3, and must print `6`. Native compilation/execution remains pending. The bare `for i in 1..:` form currently fails parsing.
