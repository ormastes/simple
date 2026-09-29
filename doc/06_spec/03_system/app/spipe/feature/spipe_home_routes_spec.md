# SPipe home deployment routes

Authored manual for `test/03_system/app/spipe/feature/spipe_home_routes_spec.spl`.
Requirements: REQ-001, REQ-002, REQ-007 in the local-knowledge architecture.

1. Create isolated core and project fixtures and run setup. A temporary HOME
   contains a minimal core delegate; real user files and remote services are untouched.
2. Verify default routes and repeat setup. `~/spipe/common` resolves to
   `~/.spipe`; project `.spipe/common` points through the private route.
3. Preserve conflicting private content and reject shared roots. Setup fails
   without deleting private bytes or invoking the delegate again.
4. Resolve explicit roots containing spaces and account for every scenario.
   `SPIPE_HOME` and `SPIPE_WORKSPACE` override separate roots; five scenario
   markers and zero process exit status are required.

Shell execution evidence: Linux fixture passed. SSpec execution/docgen is
pending an approved self-hosted runtime; this manual is authored, not generated
PASS evidence. Windows PowerShell and full core installation remain separate
verification obligations.

Migration guard fixture: run the shell contract with `--migration-only`. Four
cases reject before writing any routes: legacy core in the private root,
private root under core, core under private root, and nesting through a symlink.
Linux migration guard execution passed; these cases supplement the five
routing cases above.

## Literal home launch paths

Launch `sh test/03_system/app/spipe/feature/spipe_home_routes_contract_test.shs --placeholder-only`.
Two cases cover `{home}` prefixes with a space-containing user home and literal
shell-looking characters in a workspace name. The wrapper expands the leading
token without evaluating command substitution. SSpec includes both assertions;
its runtime execution remains pending an approved self-hosted runtime. The two
new shell cases passed on Linux (`placeholder_scenarios=2`).
