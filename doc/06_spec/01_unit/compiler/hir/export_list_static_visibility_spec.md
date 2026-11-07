# Export-list module-static visibility

Status: **UNEXECUTED — source-prepared manual, not generated runtime evidence.**
No docgen, SSpec runner, or broad qualification completed for this revision.
Two native helper compilation attempts failed before producing an executable;
zero diagnostic assertions ran. Historical mutable-only results do not establish
this repair.

Executable source: `test/01_unit/compiler/hir/export_list_static_visibility_spec.spl`.
Audience: compiler engineers reviewing HIR visibility and ABI/interface digest
consistency. Parse real source and invoke actual ordinary module lowering or
bootstrap parser-constant recovery. Missing constants, lowering errors, or a
bootstrap policy that did not activate reject the new contract observations.

| Scenario | Required observation | State |
|---|---|---|
| Exported private mutable state | Public visibility | UNEXECUTED |
| Lifted mutable interface identity | is_public true | UNEXECUTED |
| Nonexported mutable state | Private visibility | UNEXECUTED |
| Exported immutable literal | Remains private inline | UNEXECUTED |
| Explicit scoped mutable state | Remains scoped | UNEXECUTED |
| Ordinary exported array/runtime expression | Public and digest-public for both | UNEXECUTED |
| Bootstrap-recovered array/runtime expression/mutable state | Public and digest-public for all three | UNEXECUTED |
| Direct bootstrap lower_module before outer recovery | Same public storage, private array/literal and scoped controls | UNEXECUTED |
| Three driver arithmetic budgets and plain literal | Private and digest-private in both paths; guaranteed shared literal folding | UNEXECUTED |
| Unexported array/runtime expression/arithmetic/mutable state | Private and digest-private in both paths | UNEXECUTED |
| Explicit scoped array/runtime expression, even exported | Remains scoped in both paths | UNEXECUTED |

There are eleven declared scenarios. Loop-expanded observations are not executed
assertion counts. The environment-setting helper restores prior SIMPLE_BOOTSTRAP
presence/value before assertions; these specs must not race another in-process
mutator of that environment key.

The three literal arithmetic forms are 128, 512, and 16 times 1024 times 1024;
they intentionally preserve the latest MIR inline path. The exported array has
the ten reverse-reference family labels. A nonfoldable expression references
mutable private state. This distinguishes actual runtime storage from literal
values without weakening private or scoped visibility.

Native shared-classifier evidence, when available, validates only that helper.
It does not replace these real lowering paths, imported static/accessor linkage,
cache/interface identity, or broad compiler/MCP qualification. A private literal
is not sufficient negative proof of imported-static rejection. Generated-manual
review remains pending a capable source-matched runner; no PASS is implied here.
