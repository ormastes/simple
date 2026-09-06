---
name: md-tldr
description: "Create or update concise TLDR companion Markdown files for long repo documents, especially doc/04_architecture/*.md. Use same-directory naming: xxxxx.md -> xxxxx_tldr.md."
---

# Markdown TLDR Companion

Use this skill when asked to create, update, audit, or standardize "too long; did
not read" Markdown companion files.

## Naming

- Put the TLDR beside the source document.
- Name it with the same base plus `_tldr.md`.
- Examples:
  - `doc/04_architecture/simpleos_launch_modes.md` -> `doc/04_architecture/simpleos_launch_modes_tldr.md`
  - `doc/04_architecture/README.md` -> `doc/04_architecture/README_tldr.md`
  - `doc/04_architecture/format/smf_specification.md` -> `doc/04_architecture/format/smf_specification_tldr.md`
- Never create `*_tldr_tldr.md`.

## Scope

For `doc/04_architecture/`, create or update a TLDR when the source doc is long,
dense, or frequently referenced. Do not move existing architecture files unless
the user explicitly asks for a migration.

Generated/manual SPipe docs stay under `doc/06_spec/`; executable SPipe specs
stay under `test/`. Do not put `_spec.spl` files in `doc/06_spec`.

## Format

Keep the TLDR to one screen. Prefer this shape:

```markdown
# <Source Title> — TLDR

<One short paragraph: what the source doc is for.>

## Core Shape

- <main structure or decision>
- <key boundary or rule>
- <main risk or tradeoff>

## Operational Notes

- startup: <only if relevant>
- hot path: <only if relevant>
- cache/index: <only if relevant>
- invalidation: <only if relevant>
- perf/RSS: <only if relevant>

## Open Next

- [source path](relative/path.md)
- [code path](relative/source.spl)
- [test/spec/report path](relative/path)
```

Drop empty sections. Use concrete repo paths. Summarize; do not duplicate the
source document.

## Workflow

1. Read the source doc headings and the sections needed to understand the
   decision, boundaries, startup/hot paths, cache/index strategy, invalidation,
   evidence, and related paths.
2. Check nearby docs, SPipe-generated docs, tool code, and scripts only when the
   source doc points to them or the user asks for them.
3. Create or patch the TLDR with `apply_patch`.
4. If working in `doc/04_architecture/`, make sure `README.md` links or policy
   remains consistent with TLDR naming.
