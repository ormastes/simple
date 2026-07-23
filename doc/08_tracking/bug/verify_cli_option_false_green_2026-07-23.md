# `simple verify` option false-green

**Status:** source fixed; focused bootstrap contract pending.

`simple verify --typo` previously forwarded the unknown option to the quality
worker. The worker ignored dash-prefixed arguments it did not recognize, then
fell back to changed-file discovery. In a clean checkout this produced empty
PASS reports and exit zero; malformed `--files` could also silently select a
different scope.

`app.verify.options.verify_option_error` now validates the public grammar
before dispatch. Unknown, bare, empty, duplicate, and conflicting scope options
return exit 2 before the worker can write a report. Status, list, check, and
regenerate reject argument tails; help is valid only by itself. The focused contract covers rejected and
accepted forms, including the pre-report-write boundary. Fresh Stage 4 runtime
evidence remains pending.

`--all` also previously retained changed-file discovery for the MCP/LSP tooling
gate, allowing a clean checkout to skip that gate while reporting full-project
scope. It now enumerates Git-tracked project files for that report; test-quality
verification already uses its dedicated full-scan path. The all-scope contract
uses synthetic changed/tracked inputs to prove the selection cannot regress to
the changed-file set.
