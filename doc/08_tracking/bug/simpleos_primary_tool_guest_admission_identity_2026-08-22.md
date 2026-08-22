# SimpleOS primary-tool guest admission identity is missing

## Status

Open — blocks an authenticated `/bin/simplebox` filesystem-launch adapter.

## Reproducer

The host image builder validates and stages a target SimpleBox artifact. A
launcher adapter then needs guest-verifiable proof that the mounted executable
is that admitted artifact before spending loader authority. A process-local
token registry cannot provide this: the host builder and booted SimpleOS guest
do not share registry memory, so the guest rejects every legitimate token.

Caller-provided receipt fields, receipt IDs, transcripts, digests, or booleans
are not substitutes. Even when scheduler evidence later binds the executed
image digest, those values do not authenticate installer provenance.

## Required fix

Implement one of these owner-preserving boundaries:

1. Persist a signed or MAC-authenticated executable admission receipt in the
   image, verify it in guest loader scope after mount, and mint a guest-local
   one-shot authority bound to canonical path, target, image digest, admission
   ID, and filesystem generations; or
2. Run the executable admission owner in the guest after mount and issue that
   same guest-local authority directly from independently reread bytes.

The launcher may then consume the identity before the existing loader token,
execute through the architecture adapter, and consume scheduler command
evidence V2 on every terminal path. Generic `/bin/simplebox` and alias launch
must remain exit 126 without both authorities.

## Acceptance evidence

- A lifecycle test builds an image in one process, boots a fresh guest/process,
  and successfully verifies/mints from persisted admission evidence.
- Forged, stale, wrong-target, wrong-path, wrong-generation, replayed, and
  substituted-digest receipts fail before loader authority is spent.
- `/bin/simplebox echo hello` yields exact path/argv/digest, exit 0, `hello\n`,
  empty stderr, and non-truncated scheduler evidence.
- Nonzero exit and every post-delivery mismatch consume/discard the bounded
  scheduler row; replay fails.
- Generic SimpleBox aliases remain blocked with exit 126.

## Performance and memory

Guest verification must be one bounded receipt verification plus one bounded
artifact hash, not a full-tree scan or repeated file reread. Launch lookup and
token consumption must be O(1); scheduler command comparison remains linear in
the bounded argv/output evidence. Record same-run timing and peak RSS/allocation
evidence when an admitted self-hosted Simple runtime becomes available.
