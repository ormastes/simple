# Installed Linux workspace profile manual

Status: **AUTHORED_NOT_RUN**. No runtime, build, bootstrap or engine campaign.

The mirrored executable spec checks canonical exact 13-key metadata, fixed XFS
quota request derivation, rejected unknown/version/noncanonical records, path
traversal, invalid quota granularity and policy digests, host/state overlap,
and digest changes for guest mapping and permissions.

These bytes are installed metadata only. Provenance requires the actual
`LinuxMachinePolicyOwnerV1.read_workspace_profile_v1` fixed-child reader for
`/etc/simple/container/workspace-profile.sdn`. An ordinary successful decoder
cannot supply that provenance or a native storage/launch capability. Non-XFS
filesystems and unproven hard-limit enforcement have no fallback in this profile.
Exact native quota/workspace identity still requires a live storage lease.

The source-only tests confer no positive quota, workspace exclusivity, capacity,
supervisor/inventory, container isolation or mount execution qualification.
