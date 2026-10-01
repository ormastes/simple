# Dirty ordinary alias owner decision

Evidence captured 2026-09-10 (DESKTOP-VMF96U6 checkout). These nine paths are
tracked at HEAD as mode `120000`, but their worktree leaves are ordinary files
whose bytes differ from the canonical target. No path was copied, moved,
removed, or edited during this inventory. Hashes are SHA-256; timestamps are
the current ordinary-leaf `LastWriteTime`.

| Path | HEAD target bytes/path | Current leaf hash / size / type | Canonical target hash / size / status | Last modified | Diff summary |
|---|---|---|---|---|---|
| `.claude/commands/release.md` | `../skills/release.md` | `50ec9991da2ffe385a2fcb56918e61975bec7fa2250e48fcdb556d1ed46ea62e` / 1298 / ordinary file | `03ba9c81f08e225ad6b61ba40bcc36afeee07c9a3ba7f8eff5b7e935aac7e3b0` / 3172 / present | `2026-09-02T17:36:45.9000405+09:00` | leaf/canonical hash and size differ |
| `.claude/commands/repo_and_pull_req.md` | `../skills/repo_and_pull_req.md` | `17c1cedf808e2fee35ca1a0cf07f5813e2f97d25e09a30f4059f8d42f8b3f6f0` / 6983 / ordinary file | `8beebcf480503b9680c6063636e4071e0b0d3227e7d4acd41ddfabc210797aab` / 7539 / present | `2026-09-02T17:36:45.9020406+09:00` | leaf/canonical hash and size differ |
| `.claude/commands/spipe.md` | `../skills/spipe.md` | `bc57f8399c206e0f80d305b397ceba8e7f746db4a21f9930a9e53322d3f9f7e8` / 149178 / ordinary file | `74d33f5bafbdd4951ca66962f6f7f3e4d160a2b47d6373369edfec998cf2f518` / 186646 / present | `2026-09-06T14:00:21.8140133+09:00` | leaf/canonical hash and size differ |
| `.codex/commands/release.md` | `../skills/release/SKILL.md` | `2a4e140881bc4a4e502473c88b4e3411b263e7e9553cffcb1d9a95ab59a3540b` / 4261 / ordinary file | `244ee7edb3f8c60ff2abd14def672a1bdb08d2bc1b4295fa788afe2d1415c1ba` / 4764 / present | `2026-09-02T17:36:45.9605429+09:00` | leaf/canonical hash and size differ |
| `.codex/commands/research.md` | `../skills/research/SKILL.md` | `5fb2b4da718efa3c6013848f2723e904927eff9e35ab577187f6331c430c5221` / 4403 / ordinary file | `4b6a8c1deef082e070bce2121436b7cb0fb9acb47e0154bffccfbbfc594115a2` / 4954 / present | `2026-09-02T17:36:45.9615418+09:00` | leaf/canonical hash and size differ |
| `.codex/commands/sp_dev.md` | `../skills/sp_dev/SKILL.md` | `3bad34c25a4ffd796d432805c255f8500499ea4dc70075f6ec1caf426be1de63` / 62626 / ordinary file | `61c7521857db77cc9c95fad15326c3a045c88bddf9f168f052db3e05850082a5` / 84317 / present | `2026-09-02T17:36:45.9666105+09:00` | leaf/canonical hash and size differ |
| `examples/05_stdlib/spipe/.codex/commands/dev.md` | `../skills/dev/SKILL.md` | `299e0cd5653f7141ecb19280c3b0b260c4375225000eafe4db9e044114a493f1` / 595 / ordinary file | `77a04772b1d89a6a7231b4921ea049ea6a68e9b2932fd6bf82a196d98fff4563` / 908 / present | `2026-09-02T17:37:30.5635550+09:00` | leaf/canonical hash and size differ |
| `examples/05_stdlib/spipe/.codex/commands/sp_dev.md` | `../skills/sp_dev/SKILL.md` | `2bb93b0abff35a96341d839cc38ddceb4b8b7b46df6d5675b85b006e2097f4e2` / 539 / ordinary file | `3a8c9535baf11a753cf552c7976ed25ce8793efbfa36c2f9feef9481b2c55666` / 1254 / present | `2026-09-02T17:37:30.5716646+09:00` | leaf/canonical hash and size differ |
| `src/app/lint/main.spl` | `../../compiler/90.tools/lint/main.spl` | `32f71c2bc5ef38842a0b714c0ecc2b8c9d689ef71e3426cbc627fc74bf3f14e5` / 2316 / ordinary file | `4560042baf5860765a60ea9d4e356b039b9b93e77f7cede12b149bea9da79b53` / 2374 / present | `2026-09-06T14:03:24.5569576+09:00` | leaf/canonical hash and size differ |

## Ownership/process evidence

Read-only attribution was repeated on 2026-09-10. The only live agent lineage
found was OpenAI Codex (`node.exe` PID 5100 -> `codex.exe` PID 13352 ->
`codex-code-mode-host.exe` PID 8856), started 2026-09-09 19:43–19:44. No live
Claude or Gemini process was present. That Codex lineage started after every
ordinary leaf's recorded modification time, so it is not evidence that the
current session created any of the nine leaves. Its own transient PowerShell
inspection child was likewise excluded from ownership attribution.

The first eight leaves form two tight 2026-09-02 clusters: the six root
`.claude/commands` / `.codex/commands` leaves at 17:36:45.900–17:36:45.966 and
the two example-tree leaves at 17:37:30.563–17:37:30.571. Their shared timing,
ordinary-file representation of HEAD mode-120000 entries, and cross-tool
layout are consistent with one Windows checkout/copy/materialization operation
under `core.symlinks=false`. Historical Claude session metadata contains many
later references to these command paths, but path mentions are not write
receipts; no retained tool call was found that uniquely binds the leaf bytes to
a Claude, Codex, or Gemini session. Attribute these eight to an unknown prior
Windows checkout/tooling operation, not to an individual agent.

`src/app/lint/main.spl` was modified later, at 2026-09-06 14:03:24, and its
bytes differ from the canonical lint target. Claude session archives reference
that path in multiple parent/subagent sessions, but the matches include reads,
searches, and generated context as well as potential edits. No unique
content-hash-bearing write receipt connects this exact leaf to one session, so
its likely origin is a prior lint/Windows checkout lane but its owner remains
unattributed.

No currently live agent process predates or overlaps the nine modification
timestamps, and the available process/session metadata provides no reliable
evidence that any leaf is currently open for writing or actively owned.
Windows process enumeration does not itself prove absence of an open file
handle, so the correct status is **no current owner/open handle evidenced**, not
"proved unowned." All nine therefore still require explicit owner selection
before backup, merge, discard, or alias restoration.

## Independent content review

Independent blob/history review now classifies all nine ordinary leaves as
stale historical snapshots or snapshots that conflict with newer canonical
target policy/API text. Six were directly classified from retained patch and
history evidence. Three earlier proposals that could have been read as target
merge candidates were corrected to **no merge** after comparison with the
newer target owners. Across all nine paths, the safe target-merge hunk set is
empty: copying any leaf hunk into its target would either add no unique work or
restore superseded/conflicting content.

Retain `.spipe/windows_full_bootstrap_toolchain_suite/dirty_alias_patches/`
in full as recovery evidence, including the six direct patch artifacts, the
proposal/diff records, and `recommendation.md`. These artifacts support the
no-merge conclusion; they are not authorization to overwrite the live leaves.

## Exact restore plan (approval required)

Immediately before any action, revalidate all nine leaf hashes against the
table above and repeat the active-owner/open-write check. Any drift or newly
identified owner stops the operation for a fresh decision. If every value is
unchanged and the owner explicitly approves destructive replacement:

1. preserve the proposal/diff artifacts above as independently readable
   recovery evidence;
2. replace each ordinary leaf with its exact HEAD mode-120000 placeholder bytes
   (the target text in the second table column), using a path-scoped
   `apply_patch` operation or the equivalently scoped mechanical restore owner;
3. run the canonical Windows materializer over those restored placeholders and
   verify every alias resolves to the recorded canonical target; and
4. run the actual 116-link schema-v2 producer and retain its hash-bound receipt
   before allowing the Git-state consumer or Stage 2 admission to proceed.

Replacing the nine ordinary leaves discards their live worktree bytes even
though recovery artifacts exist. That is destructive and still requires
explicit owner approval. No leaf or target restoration, merge, discard, or
materialization is authorized by this review or plan.
