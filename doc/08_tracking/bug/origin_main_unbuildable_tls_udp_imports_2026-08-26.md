# origin/main unbuildable: unresolved rt_tls_*/rt_io_udp_* imports (2026-08-26)

## Symptom

`cargo build --release --bin simple` on pristine `origin/main` (`25e60be7aaf`,
clean `git worktree add --detach`) fails in the runtime crate:

```
error[E0432]: unresolved imports `net::rt_tls_client_config_add_root_cert`, ...
              (23 rt_tls_* symbols)
error[E0432]: unresolved imports `value::rt_io_udp_bind`, ... (11 rt_io_udp_* symbols)
error[E0432]: unresolved imports `value::rt_tls_client_read_checked`, ... (3)
```

37 symbols are still `pub use`-re-exported while their definitions are gone —
the exact shape `check-runtime-api-regression-push.shs` exists to block ("still
re-exported in lib.rs (unbuildable)"). Suspect window: the `fix(sffi): ...`
series landing 2026-08-25 23:xx UTC (`7ff184b9847` "remove ambiguous TLS reads"
touched `runtime/src/lib.rs`; `4edef8fab8e` "snapshot current development
state" is a whole-tree snapshot and the likely clobber), pushed without the
guard (no marker for this content in the seed-green store).

Third occurrence of this incident class this month
(`origin_main_unbuildable_rust_seed_2026-08-11.md`,
`origin_main_unbuildable_cowenv_e0308_2026-08-25.md`).

## Impact

No seed can be built from origin/main, so directory-mode `simple test --json`
cannot be verified on a pristine tree; the deployed host seed (built from
`d813ea19dd9`+fix) predates this and keeps working. Separately, that older
seed rejects the stdlib's new `@always_inline` decorator (`file_exists`), so
pristine-tree runs need a seed built AFTER the decorator landed — which this
break prevents. Both must clear before a CI-reproducible sweep.

## Fix

Not attempted here — the symbols belong to another session's in-flight net/TLS
work and restoring them blindly risks reverting a deliberate removal. Owner
should either restore the definitions or drop the re-exports, then run
`sh scripts/check/check-seed-builds-push.shs` and land through the guard.

Found during the simply whole-earth dashboard sweep
(`.spipe/simply_showcase/state.md`).
