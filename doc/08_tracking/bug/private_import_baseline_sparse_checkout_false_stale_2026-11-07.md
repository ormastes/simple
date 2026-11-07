# Sparse required-gate checkout misclassified valid private-import sources

Status: source repair proposed; exact-head Astra and CI admission required.

The private-import baseline contains 20,194 existing entries. Required Gates
checks out a sparse source subset; its cone rules omit 17,445 entries across
3,070 files. The old scanner treated every physically absent source as stale,
producing exactly that false-stale count. The first reported ERP functions
still exist as private definitions in the pinned Git source. Baseline contents
are unchanged and have no CR bytes; regeneration or exclusions are unjustified.

The scanner now requires Python3 and Git, as declared in the real gate manifest.
It reads present working-tree source normally and consults indexed blobs only
for missing SKIP_WORKTREE paths. An actual full-checkout deletion remains stale;
an indexed public promotion is stale even before commit. Read failures return
ERROR 2. Existing private/export parsing and removal-only ratchet remain intact.
Physical records split only on newline, so Unicode separators inside a source
line or baseline entry cannot manufacture declarations or extra records.

The existing seven controls and two cone-checkout controls retain their prior
PASS. Six additional controls passed once without replaying them: staged sparse
promotion, Git read failure, real tracked deletion, Python read failure, and
U+2028 within source and baseline records. No full global baseline rerun is
claimed by that focused evidence.

One cat-file process avoids one subprocess per source, but is not a single
network-fetch guarantee. A blob:none promisor checkout may lazily fetch many
blobs; existing gate/job timeouts remain in force. Source bodies are cached
for classification, so memory scales with all referenced source bytes.

The separate printf/head publisher remains unchanged and may still emit a
broken-pipe diagnostic for a large genuinely stale list. This repair changes
no SDK/LSP/compiler source, permits no new private imports, adds no baseline
exemptions, and does not authorize merging over a genuine required-gate failure.

The first corrected CI scan exposed a separate base-handoff defect: the pinned
base manifest invoked this gate without --base, while the workflow fetched
commits by SHA and created no origin/release/1.0.0 ref. Explicit --base now wins;
otherwise the actual workflow BASE_SHA is accepted only as a fetched valid
commit. No implicit HEAD substitution is used. Future manifest commands pass
the runner's {base} explicitly. Unknown commits, missing objects and read errors
remain ERROR; introducing-change skip requires a real commit with confirmed
absence of the baseline path. Focused base-provenance and actual depth2/no-ref
controls passed without replaying prior green source controls.
