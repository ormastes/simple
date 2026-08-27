# Theme Service Notification Contract

## Status

Fail-fast. A theme change cannot notify its numeric IPC subscribers until the
service owns or receives a real send-capable transport.

## Manual evidence

1. Select a valid alias and resolve one immutable package snapshot.
2. Install that exact snapshot through the canonical WM theme owner.
3. Observe one monotonic revision increment.
4. Observe every subscribed destination receive the same canonical theme ID,
   source fingerprint, material fingerprint, and revision.
5. Reject invalid packages without changing snapshot or revision.
6. Surface delivery failures explicitly.

The executable system contract remains red until these steps use production
IPC wiring. An in-memory counter, silent queue, or invented callback does not
satisfy the contract.
