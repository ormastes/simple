# FV2 nanoda closed Nat-literal gap

## Status

Open independent-checker capability gap. The Gate 4 runner remains fail closed.

## Evidence

`run-fv2-simpleos-independent-replay.shs` builds and exports all seven exact
vertical-slice roots. With nanoda's native Nat/String extensions disabled:

- `ActorChannel.GreenCloseExact.close_drain_refinement_bundle` independently
  passes (48 checked declarations);
- capability rights, scheduler completion, shared unmap, process wait, process
  queue, and DBFS commit are rejected at their first `#ELN` primitive Nat
  literal.

The retained partial manifest is
`build/verification/simpleos-independent-replay/rejected-partial.sdn`. It is
diagnostic evidence only and cannot promote Gate 4.

This is not an axiom failure and must not be hidden by enabling
`nat_extension=true`: FV2's closed lane deliberately excludes nanoda's native
Nat/String kernel extensions from its trusted base. The checker therefore
cannot currently replay Lean roots whose kernel terms contain primitive Nat
literals, including BitVec widths and indices.

## Measured exporter boundary

The retained format-v2 exports were inspected against the pinned tool manifest
on 2026-08-13.  `lean4export` and `nanoda_bin` match that manifest's SHA-256
identities.  The closed checker rejects the first `#ELN` row before theorem
checking; this is therefore a format/checker capability boundary, not an axiom
or theorem failure.

| Root | `#ELN` rows | Largest literal |
|---|---:|---:|
| `KernelCapabilities.rights_allow9_sound` | 6 | 100000000 |
| `KernelScheduler.complete_refinement_bundle` | 19 | 1114112 |
| `MemoryCapabilities.SharedUnmapExact.shared_unmap_refinement_bundle` | 4 | 8 |
| `ProcessLifecycle.ProcessWaitExact.process_wait_refinement_bundle` | 3 | 2 |
| `ActorChannel.ProcessQueueExact.process_queue_refinement_bundle` | 51 | 4294967296 |
| `DbStorage.TxnCommitExact.commit_refinement_bundle` | 3 | 2 |

The accepted close/drain root has no `#ELN` row.  In particular, converting
literals to a unary `Nat.succ` chain is not a safe workaround: the process
queue closure alone would require billions of generated constructor nodes. Any
normalizer must preserve Lean's literal semantics and use bounded binary
sharing, with an independently checked correctness argument and explicit
resource limits.

## Required closure

Choose and review one sound route:

1. certificate-checked literal normalization from Lean primitive literals to
   ordinary inductive/kernel terms with size-safe binary sharing;
2. an independently reviewed checker implementation whose primitive-literal
   rules are admitted explicitly into a bounded TCB profile, never the closed
   profile; or
3. another independent checker supporting Lean 4.33 primitive literals without
   an untracked native extension.

Until then, the six roots remain `model_proven`/replay-rejected rather than
`artifact_verified`.
