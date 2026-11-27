# Native history task ownership

- Implementation owner: `jj_change_impl`, isolated `/tmp/simple-scv-jj-work`.
- Independent guide: `jj_guide`; reviews graph semantics, error admission,
  compatibility, fixtures, and manual boundaries.
- Merge owner: parent session; implementation lane commits but does not push.
- Final reviewer: parent-selected highest-capability review before landing.
- Lower-model sidecar lanes: N/A for this bounded history-owner change.
- Runtime qualification: NOT_RUN until an admitted pure-Simple runtime exists;
  neither static checks nor guide review replace native test evidence.
