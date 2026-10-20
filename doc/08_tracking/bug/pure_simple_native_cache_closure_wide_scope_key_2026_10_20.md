# Pure-Simple native-build object cache is keyed on the whole source closure

- Status: OPEN
- Date: 2026-10-20
- Related: the seed object-cache keying lane (Opus) fixes the same symptom on
  the Rust seed's native_project path; this record is the pure-Simple twin.
- Blocks: "recompile only affected objects and relink" for compiler
  rebuilds done with a pure-Simple (Stage 2/3) compiler, and therefore the
  self-hosted rebuild route (Stage 3 rebuilding Stage 3).

## Observation

- `.claude/rules/bootstrap.md` ("Layer 2", 2026-08-08): the pure-Simple
  driver hashes the entire loaded source closure into `cache_scope_root`, so
  editing any one file changes the scope directory and drops reuse to 0
  for every module (measured 3/3 reused unchanged, 0/3 after a one-line edit).
- Same symptom on the seed path today: relinking the r14 Stage 2 after a
  two-file change (83ff46b0bc4) reported `compiled=1367 reused=0` both
  against the read-only admitted cache and against a writable copy
  (`scratchpad/cache14w`, 1645 objects): 285 s and 196 s for a full
  recompile instead of a relink.

## Expected

Per-module keys over the module's own source plus its imported interface
digests (`action_key.spl:interface_digest_of` already exists), so an edit
recompiles the edited module and its dependents only.
