# Warm SCV inventory silently omits untracked Unicode sources

- Date: 2026-09-21
- Severity: P1 (incomplete compiler source authority)
- Status: fix implemented; Git command regression passed; Simple integration execution pending
- Owner: `src/app/compiler_entrypoint/inventory_events.spl`

After cold initialization, create `src/한글/소스.spl` or
`src/한글/simple.sdn` in a checkout with Git's default `core.quotePath=true`.
Warm refresh uses `git ls-files --others --exclude-standard`, which C-quotes
the Unicode paths. The inventory filter checks the literal `.spl` or
`/simple.sdn` suffix; a quoted path ends with a quote and is silently skipped.
Cold initialization and diff already pass `-c core.quotePath=false`, so the
same source can be discovered during cold initialization but missed later.

## Change

Pass `-c core.quotePath=false` for warm untracked enumeration too. Preserve
the existing source-root pathspecs and non-source filtering. This change does
not address filenames containing control characters that Git still quotes.

## Evidence

On macOS, a temporary real Git repository explicitly configured with
`core.quotePath=true` contained the two Unicode files above and `readme.md`.
A focused check extracted the actual warm argument array from production
source. The old command admitted **0/2** source identities; the patched
command admitted **2/2** with their exact UTF-8 identities. The Markdown file
remained excluded. The working env/process facade guard passed.

`test/02_integration/app/compiler_inventory_unicode_untracked_spec.spl`
creates a tracked baseline, performs production cold initialization, adds
the Unicode source and manifest, then runs production warm refresh and checks
the published inventory identities and content digests. Its execution is
pending a verified self-hosted runtime; the available `bin/simple` points to
the Rust seed and was not used as a fallback.
