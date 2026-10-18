# Item 4 generator repair candidate

Date: 2026-10-18. Base `release_phase3`:
`3ca2b121b8a85e1a0eaa79157f9a40d11492ee7f`.
STATUS: BLOCKED (runtime execution and generated manual outstanding).

## Implementation

`src/app/linker_gen/main.spl` selects hexadecimal digits from text literals,
removing the character-code conversion implicated in the open nonzero-address
bug. It now emits `(NOLOAD)` for the already-parsed `nobits` section type.
No compiler, library, runtime, public schema or boot-layout owner was changed.

The existing system spec retains its zero and 1 MiB formatting assertions and
adds alphabetic digits, nibble boundaries, maximum nonnegative `i64`, full
nonzero-origin rendering, and explicit-address fixed-size NOLOAD output.
The ordinary text-section assertion checks an explicit address and excludes a
NOLOAD qualifier through the exact expected header substring. Existing KEEP
and boundary-symbol scenarios remain present. Requirements: REQ-LNK-018/019/022.

## Ownership and runtime boundary

Isolated branch/worktree: `work/item4-generator-20261018`,
`C:/dev/simple-item4-generator-20261018`. Shared checkout inspection found
402 dirty entries; none were incorporated. Concurrent Item 2/7 processes and
an authority compile from `C:/dev/p4c2plan/run-authority-cycle2r1.shs` were
observed. No duplicate compiler/bootstrap build was started.

No deployed runner was present in the inspected shared `bin/release` directory.
The active authority launcher uses a Stage 2 producer, not a general SPipe
runner. This absence blocks execution; it does not justify Rust-seed fallback
or claiming Stage 4 evidence. Implementation compatibility is Unknown;
bootstrap_required=false for this private application repair. Once available,
use the admitted application/test closure with isolated output/cache. No
global cache cleaning or producer rebuild is part of this repair.

## Required acceptance before ready/merge

1. Record runtime path, hash, stage, provenance and supported commands.
2. Run `test/03_system/feature/app/linker_gen_spec.spl` once against this source.
3. Run `spipe-docgen` for that spec with `--output doc/06_spec --no-index`;
   require zero stubs and inspect the resulting scenario manual.
4. Link an actual generated board script and inspect its addresses, section
   allocation and KEEP behavior. Renderer assertions alone do not prove this.
5. Complete scope guards and exact-head review; read PR comments before merge.

The generated manual is explicitly marked stale pending regeneration. The
formatting bug remains OPEN. This candidate must remain a draft until required
evidence exists; it does not establish full Item 4 or Phase3 PASS. Sidecars:
N/A; final review by Item 4 owner. No release tag or publication.

Static checks on the candidate: staged whitespace PASS; numbered-artifact and
direct-env-runtime guards PASS in both working and staged modes; tracked
executable specs under `doc/06_spec` = 0. The knowledge-selection receipt
records no exact registered feature and the longest-prefix `src/app` layer.
These structural results do not establish executable correctness. General
SPipe execution, generated-manual freshness and real link inspection remain
blocking. No verify PASS is issued.
