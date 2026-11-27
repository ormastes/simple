# smux primary V4 dispatch

Source: `test/01_unit/os/apps/smux/runtime_primary_dispatch_v4_spec.spl`.
Status: **NOT_RUN**. Manually authored companion, not generated execution evidence.

Four scenarios call the actual in-process dispatcher at its unconfigured default:
accept the 4096-byte total frame boundary and refuse 4097; authenticate all V4
verbs before payload parsing; report explicit unavailable planning and false
input/geometry/interactive capabilities; preserve exact V3 discovery bytes and
service configuration revision. Frame admission is tested without a TCP socket.

Configured plan/prepare/bind, pane adoption, polling, native cleanup, and
live/recovered settlement are **NOT_COVERED**. No fake Host root is installed.
