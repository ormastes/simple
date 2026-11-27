# Darwin conservative UID process-record barrier

Source: `test/03_system/check/sosix_darwin_uid_process_barrier_spec.spl`.

Native live-process, retained-zombie, and unobserved session-descendant fixtures must block the
UID/unique-id observation until reaped. Older unrelated zombies are excluded.
Non-`SZOMB` exit transitions, snapshot resizing, permission errors, post-snapshot reaping, and deadline expiry
must preserve truthful absence semantics.

This component does not advertise generic reap or V4 authority. Trusted root
identity, immutable UID, admission closure, and zero live coalition tasks remain
integration prerequisites. Unrelated newer UID processes, including live ones,
conservatively block.

Validation: native-backed P1 diagnostic SSpec 1/1 passed, no skips or drops,
on Darwin 25.5.0. This is not P2 release qualification.
