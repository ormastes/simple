# sspec docgen emits a raw source dump instead of a scenario manual

- Filed: 2026-08-24
- Component: `src/app/sspec_maintain/documentize.spl` (canonical SPipe docgen)
- Status: OPEN
- Severity: caps every spec's documentization score at 91/100

## Symptom

`bin/simple run src/app/sspec_maintain/main.spl documentize <spec>` writes the
`doc/06_spec` mirror by copying scenario bodies verbatim. Three consequences,
each of which the scorer then charges back against the spec that fed it:

| rule | deduction | what the manual actually shows |
|---|---|---|
| `SSDOC-EVD-002` | -15 | `step("Create session \"main\" at index 0")` rendered as literal source, not as an ordered operator step |
| `SSDOC-MNT-008` | -20 | no Traceability section, although `# @req` bindings are present in the source |
| `SSDOC-MNT-004` (latent) | -10 | internal `# @manual: primary` and `# @req` tags leak into reader-facing output |

## Evidence

`test/01_unit/os/smux_spec.spl` and
`test/01_unit/os/smux/smux_dashboard_spec.spl` were authored up to
`narrative=100 structure=100 oracle=100`, every declared requirement bound, all
lifecycle links resolving to real files. Both still score exactly **91/100**,
and every remaining point is one of the rows above — i.e. the ceiling is the
generator, not the spec.

Reproduce:

```sh
bin/simple run src/app/sspec_maintain/main.spl documentize test/01_unit/os/smux_spec.spl
grep -n 'step("' doc/06_spec/01_unit/os/smux_spec.md   # literal source, not rendered steps
grep -n '@req\|@manual' doc/06_spec/01_unit/os/smux_spec.md  # internal tags in reader output
rm -rf .simple/cache/sspec-maintain
bin/simple run src/app/sspec_maintain/main.spl scan test/01_unit/os/smux_spec.spl
```

## Why this matters

The stated purpose of Modern SSpec is a scenario-based manual usable without
opening its source spec (`llm-caret-messaging` AC-10). A mirror that reprints
the source is that requirement's exact failure mode: it is readable only by
someone who could already read the spec.

## Fix sketch

In `documentize.spl`, render `step(...)` calls as an ordered list under a
"Primary workflow" heading, emit a Traceability section from the `@req`
bindings the analyzer already extracts (`source_facts.spl` collects them for
`SSDOC-TRC-003`), and strip `@manual`/`@req`/`@tag` lines from reader output
rather than passing them through.

## Related authoring gotcha (not a defect, but a trap)

`SSDOC-ORA-003` accepts a `# oracle:` marker only on the **same line** as the
assertion (`source_facts.spl:319-321` tests `line_lower.contains("# oracle:")`
against the assertion line itself). A marker on the preceding line — the form
the tool's own `improve` advice reads as natural — parses as an ordinary
comment and silently does nothing. Both specs above lost 30 points to this
before the markers were moved inline.
