# Lane FVT — §21.3 formal layer: TUF update security + OCI import safety

Status: DONE (2026-07-27). Gate GREEN: `cd src/verification/os_enforcement && lake build` exit 0; `#print axioms` on every new theorem shows only `propext`/`Quot.sound` (same axiom profile as the existing eight modules) — NO `sorryAx`, no `sorry` anywhere.

## Files
- `src/verification/os_enforcement/OsEnforcement/TufUpdate.lean` (new) — 11 theorems, namespace `OsEnforcement.Tuf`
- `src/verification/os_enforcement/OsEnforcement/OciImport.lean` (new) — 13 theorems (+2 helper lemmas counted), namespace `OsEnforcement.Oci`
- `src/verification/os_enforcement/OsEnforcement.lean` — registered both imports (lakefile needed no change; the lib root pulls them in)

## Models (source of truth)
- `src/os/services/update/tuf_metadata.spl` → `Tuf.verifyUpdate`: fail-closed pipeline in .spl order (trusted-keys → threshold → freshness → rollback → snapshot consistency), Outcome inductive mirrors the TUF_* reason codes; `countValidAux` mirrors the seen-list distinct-signer count.
- `src/os/services/container/oci_import.spl` → `Oci.importCheckedEx`: digest → hooks → unpack bounds → per-mount loop (traversal/host-bind/device), keeps the `check_traversal` toggle; on accept, produced caps = `capsIntersectIsolated` (ceiling intersection, host-net stripped).

## TufUpdate theorems
- T1 `accepted_no_rollback` — accepted ⇒ no role version below current (all 4 roles); `rollback_rejected` corollary.
- T2 `accepted_fresh` / `expired_rejected` — accepted ⇒ now ≤ every expires_at; expired metadata never accepted (freeze defense).
- T3 `accepted_thresholds`, `accepted_keys_trusted`, `untrusted_signer_rejected`, `no_single_key_compromise` — accepted ⇒ ≥threshold DISTINCT signers all in root's trusted set; with threshold ≥ 2 a single compromised key (any number of replayed sigs) can never yield acceptance (via `countValidAux_le_one_of_single`).
- T4 `accepted_snapshot_consistent` / `snapshot_mismatch_rejected` — snapshot-inconsistent targets is never accepted (anti mix-and-match).

## OciImport theorems
- O1 `accepted_no_traversal` / `accepted_no_dotdot` — accepted ⇒ no mount dest contains a `..` component (DOTDOT sentinel in the normalized List-Nat path model).
- O2 `accepted_digest_present` — require_digest ⇒ accepted has non-empty digest. NOTE: the .spl adapter checks digest PRESENCE only (per-layer content-hash match happens at unpack time, outside this edge adapter), so the "every layer digest matched" wording from the task was adapted to what the code actually enforces.
- O3 `check_enable_monotone` + `deny_wins` — enabling the traversal check only shrinks the accept set; an image rejected by the check-light pipeline is never accepted by the stricter one (rejection monotone / deny-wins).
- O4 `accepted_isolated_net` — produced caps never contain a raw host-net token.
- O5 `accepted_caps_bounded` — every produced cap ∈ requested ∩ ceiling (no amplification).
- Plus (b)/(c)/(d)/(e): `accepted_no_raw_host_mount`, `accepted_no_unauthorized_device`, `accepted_no_hooks`, `accepted_unpack_bounded`; extraction lemmas `acceptedEx_checks`, `mountCheck_none_of_mountsCheck_none`.

## Model simplifications (all faithfulness-preserving)
- Key-ids / cap tokens / path components as Nat atoms (only equality used in the .spl).
- Role loops unrolled over the four fixed roles (the .spl iterates a 4-element list).
- OciConfig fields the checks never read (image_ref, root_path, entrypoint, env, uid, gid, mem_budget) elided; they carry no authority and pass through to ContainerSpec untouched.
- Nested namespaces `OsEnforcement.Tuf` / `OsEnforcement.Oci` used (flat namespace already holds `Policy`, `DOTDOT`, `deny_wins`, `has`, ...).

## Blocked rows
None — no theorem dropped, none vacuous.
