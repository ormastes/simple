# `simple spec-gen` flattens mirror paths and silently drops most specs

- **Date:** 2026-08-18
- **Status:** OPEN
- **Component:** `src/app/spec_gen/main.spl`
- **Severity:** medium — produces wrong-path docs and under-reports coverage as success

## Summary

`bin/simple spec-gen` is not usable for generating `doc/06_spec/` mirrors. It has
two independent defects. The working generator for this job is
`bin/simple spipe-docgen`, which mirrors `test/` paths correctly and extracts
full scenario content.

## Defect 1 — output path is relative to the search argument, not the repo `test/` root

`spec_relative_dir(file_path, search_root)` (`src/app/spec_gen/main.spl:108`)
strips the *user-supplied* search path, then joins the remainder onto the
hard-coded `SPEC_DIR = "doc/06_spec"`. Any scoped invocation therefore writes to
the wrong place. `.claude/rules/structure.md` requires `doc/06_spec` to mirror
`test/` paths.

Exact command and observed result:

```
$ cd /mnt/data/worktrees/office-mirrors
$ bin/simple spec-gen test/01_unit/app/office
Generated 36 spec documents in doc/06_spec/

$ git status --short
?? doc/06_spec/calc_cli_spec.md
?? doc/06_spec/calc_session_host_isolation_spec.md
?? doc/06_spec/counter_route_spec.md
?? doc/06_spec/erp_bridge_spec.md
?? doc/06_spec/grid_render_spec.md
?? doc/06_spec/office_suite_spec.md
?? doc/06_spec/publisher/
...
```

Expected `doc/06_spec/01_unit/app/office/<name>_spec.md`; actual is a flat dump
into the `doc/06_spec/` root. Only an unscoped `spec-gen test` would land the
right paths, which makes the `[path]` argument documented in `--help`
unusable for its obvious purpose.

## Defect 2 — 129 of 165 specs silently dropped, and the run still reports success

`extract_spec_doc` (`main.spl:33`) only recognises the bare block forms
`describe "..."`, `context "..."`, `it "..."` / `test "..."`. It does not match
the parenthesised call form that is widespread in this tree, e.g.
`test/01_unit/app/office/sheets/validation_spec.spl:6`:

```
    it("accepts member in allowed list"):
```

When nothing is extracted, `main.spl:170` does `if doc.trim() == "": continue`
— the file is skipped with no diagnostic. Against the 165 office specs the run
above emitted 36 documents and exited 0 with the cheerful line
`Generated 36 spec documents`, never mentioning the 129 it dropped.

For comparison, on the same tree `spipe-docgen` reports
`DONE Generated 151 docs (151 complete, 0 stubs)`.

## Expected

1. Mirror paths resolved against the repo `test/` root regardless of the scope
   argument.
2. Parenthesised `describe(...)` / `context(...)` / `it(...)` forms recognised.
3. A skipped spec is reported (count at minimum), and a run that skipped files
   must not present itself as an unqualified success.

## Workaround

Use `bin/simple spipe-docgen <spec files>... --output doc/06_spec --no-index`.
