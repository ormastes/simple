# Host external content ownership

Status: rendering overwrite fixed; remote application presentation remains RED.

## Root cause

`HostCompositor.requires_external_web_frame()` inferred BrowserRenderer ownership
from `owner_port > 0`. A validated GUI or pixel `WmContentFrame` therefore
remained eligible for a later Web frame overwrite.

## Fix

Hosted windows now carry one scalar `content_owner`. Creation assigns local
Web, remote Web, or browser ownership. Validated GUI/pixel frame admission
changes that owner, lifecycle mutations preserve it, and releasing the frame
restores the creation default. BrowserRenderer eligibility now depends only on
the scalar owner.

The no-stub pure-Simple Stage-2 owner probe linked and exited `0`. The real
host-compositor closure also compiled into an archive with zero failures.

## Remaining gate

The hosted remote client transport still has no deployed native server poll,
and the window protocol has no pixel-present command. External GUI/pixel input
also has no remote event receiver. In-process frame admission is therefore not
remote-application proof; add the scalar host bridge and bounded present slot
before claiming that lane live.
