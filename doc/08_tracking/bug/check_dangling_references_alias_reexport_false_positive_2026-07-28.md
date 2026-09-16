# `check-dangling-references.shs` reports false SYMBOL findings for alias re-exports

**Status:** OPEN
**Found:** 2026-07-28 (dangling-reference triage, `src/os/**` scope)
**Area:** `scripts/check/check-dangling-references.shs`
**Severity:** low — false positives only, no missed defects. But it inflates the
finding count and costs triage time, and it can mask real findings behind noise.

**Related:** `dangling_reference_checker_symlink_and_untracked_blind_spots_2026-07-28.md`
records two *other* false-positive classes in the same checker (providers behind
symlinked source trees, and providers that exist but are untracked). This is a
**third, independent class** — the provider is tracked and indexed, but it
supplies the name via an alias re-export that the index pass drops.

## Finding

The checker's own header documents the limitation:

```
# * Aliased imports (`use m.{A as B}`) are skipped entirely.
```

Skipping aliased imports at the **call site** is correct. But the index pass
also fails to register the alias as a **definition**, so a symbol that a module
legitimately provides via `export use ... {X as Y}` is reported as
"declared in no src file" at every consumer.

## Concrete false positive (5 findings in `src/os/**`)

`src/lib/nogc_sync_mut/fs_driver/nvfs_hosted_driver.spl:9`:

```simple
export use nogc_sync_mut.fs_driver.nvfs_posix_driver.{NvfsPosixDriver as NvfsHostedDriver}
```

`NvfsPosixDriver` is really declared (`src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl:32`,
plus `src/lib/nogc_sync_mut/fs/nvfs_posix/posix_driver.spl:24` and
`src/os/services/nvfs/posix/fs_driver_impl.spl:36`), and
`src/lib/nogc_async_mut/fs_driver/nvfs_hosted_driver.spl:7` re-exports the alias
onward. The name `NvfsHostedDriver` resolves correctly at every consumer.

The checker nevertheless emits 5 findings of the form:

```
SYMBOL: imported name `NvfsHostedDriver` is declared in no src file
```

`grep -rlE '^\s*(pub )?(struct|class|...)\s+NvfsHostedDriver'` over `src/`
returns nothing (correct — it is only ever produced by the alias), while
`grep -rlE 'as\s+NvfsHostedDriver\s*[},]'` finds the re-export.

## Suggested fix

In the pass-1 index (`index.awk`), when a line matches
`use <mod>.{ ... <Name> as <Alias> ... }`, emit `D <Alias>` — the alias is a
definition contributed by the re-exporting file, exactly as `export use` of a
plain name is. The pass-2 call-site skip for aliased imports can stay as is.

## Impact on the current counts

Of the 83 findings under `src/os/**` + `src/unit/**` as of 2026-07-28, **5 are
this false positive** (all `NvfsHostedDriver`). Real remaining findings: 78.
