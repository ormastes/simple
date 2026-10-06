# Bootstrap Cargo manifest discovery process overhead

Windows Phase1 attempt 3 (`5f6d8b1453be721b9399107bc66ad56f794ebf1e`, collector
21520) reached fingerprint startup after successful receipt verification.
Its compiler input list held 43416 files. List completion to hash-record
completion took approximately 8.8 seconds; the hashing helper already supports
bounded parallel workers and batches hash commands with xargs.

Dependency discovery then walked 903 Cargo manifests, starting a separate
dirname, awk, and pipeline shell for each. The manifests totaled 2402147 bytes.
An immutable Git-object capture of that source epoch reproduced extraction
in 96.336 seconds. A single streaming awk parser took 0.850 seconds and emitted
exactly the same 2271 bytes: 58 ordered originating-directory/dependency pairs.
This measures extraction under concurrent host load, not total bootstrap speed.

The parser now processes the manifest list in one invocation, resets dependency
section state for each file, and streams ordered pairs to a private temporary
file. It retains only the current line and origin, preserving literal quoted
path text, duplicate records and parser grammar. It checks file-read and close
errors; the caller does not consume partial output after parser failure. The
existing dependency existence, canonical containment, and symlink checks are
unchanged. No content hash, worker allocation, security receipt, tool binding,
or source pre/post/commit authority checks change.

Fourteen distinct host cases passed: spaces, per-file state reset, duplicates,
root manifests, supported/excluded sections, missing and partially readable
input lists, literal invalid paths, CRLF input, valid contained dependencies,
escaping/missing dependencies, and streaming memory. Eightfold captured input
increased awk peak RSS from 10244096 to 10362880 bytes, below the 8MiB regression
allowance. The first CRLF assertion incorrectly expected zero pairs based on
regex inspection; actual Git-for-Windows awk text input strips CR, so both old
and new parsers emitted the same valid dependency. The expectation was corrected
and only that failed case rerun. This is not a demonstrated CRLF production bug.

Run `scripts/check/check-bootstrap-cargo-path-batch.py` with the candidate
authority script, a new output directory, and optionally an immutable captured
manifest root for the memory check. The test executes extracted production
helpers and the original containment block without running bootstrap or a
compiler. Cases continue independently on failures. Full bootstrap using this
source repair remains UNRUN; the active build/source/cache were not modified.

Content-based parse-result caching may later use verified manifest digest plus
parser recipe/schema. HEAD or mtime alone must not substitute for current
manifest membership, dependency filesystem checks, or source/tool authority.
This repair introduces no persistent cache and no new algorithm choice.
