# Windows runner diagnostic exceeded its memory cap

The older admitted self-hosted producer `17d1a40abc390c08c05cec3ba13db41eb12ee5709126c6636fe974f753f7e5ac` attempted the full `src/app/test_runner_new/main.spl` closure against frozen source `d9325632b89ac99840b899bfd30eb6e620ad52a2`. Stub fallback and bootstrap delegation were disabled, with one frontend worker and one code-generation thread.

The actual HIR worker lowered 254 of 254 modules and stored their archives. The complete process group subsequently exceeded the unchanged 5,859,375 KiB enforced RSS limit, reaching 6,011,456 KiB. The watchdog returned 88 and confirmed quiescence. No runner executable was produced; no behavior assertions ran. This is a failure of the older producer diagnostic, not evidence that the new source fixes were compiled or exercised.

Exact argv, source identity, immutable logs, and terminal process/RSS receipts are retained in `C:/dev/simple-phase3-bootstrap-evidence/runner-check-20261012`. A new producer containing the fixes, full runner build, and discriminating green/red/zero-example behavior tests remain required. The separate older-producer Hello object/link/run check passed and does not qualify the runner or latest Phase 3 compiler.
