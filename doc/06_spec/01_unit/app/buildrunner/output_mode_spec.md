# BuildRunner retained output permissions

Executable specification: `test/01_unit/app/buildrunner/output_mode_spec.spl`.

On POSIX hosts, publication authenticates retained and destination bytes before
restoring the retained artifact's ordinary permissions. Windows records this
POSIX-only fixture as pending; production Windows permission behavior is unchanged.

| Case | Required result |
| --- | --- |
| Matching bytes lose execute bits | Read-only comparison refuses drift without mutation; publication restores mode and the Hello shell fixture executes with exact output |
| Nonexecutable retained output gains execute bits | Publication restores the nonexecutable mode |
| Destination content differs | Publication refuses it without changing its mode |
| Destination is a symlink | Publication refuses it without changing the linked file |
| Output parent symlink escapes the output root | Publication refuses before creating a missing directory in the external tree |
| Nested output directories do not yet exist | Publication creates parents inside the output root and publishes the admitted bytes |

The companion `bootstrap_builder/output_root_spec.spl` covers read-only CLI
verification, cache repair, and local reuse of an SSH attempt's collected
snapshot. Its synthetic receipts are unit fixtures, not native process evidence.
