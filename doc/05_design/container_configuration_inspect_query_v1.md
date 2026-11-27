# Common fixed query DATA

This is a separate source extraction after the accepted input producer/Host
restriction pair. Their immutable snapshots remain unchanged. The new common
leaf lets lower IO select trusted configuration query DATA without importing
async owners, parsers or capture code. It owns no executable capability,
environment, process, writer, permit, native export or cleanup lifecycle.

`ContainerConfigurationInspectKindV1` has exactly six cases: ConfigurationBefore,
ConfigurationImage, ConfigurationAfter, InputConfigurationBefore,
InputConfigurationImage and InputConfigurationAfter.
`container_configuration_inspect_command_v1(kind, expected, windows,
observed_image_id="")` returns bounded fixed RuntimeCommand DATA. Non-image cases
require an empty observed image ID and a full container ID; image cases require
a full bare or sha256-prefixed image/config ID. Repository references, shortened
IDs, options and raw templates/argv are not accepted as an image ID. Existing
accepted ID bytes are preserved in argv rather than silently normalized.

The Before/After cases intentionally emit identical commands, with the existing
operation names configuration-container or input-configuration-container. The
real owner's closed stage distinguishes before from after. Both image cases emit
the existing configuration-image query. Existing async factory signatures become
thin forwarders and retain the exact operation, program, template and argv bytes.
Native JSON parsing, three-capture stability, image correspondence, mandatory
input booleans and canonical outer digest stay in their existing async owners.

The builder validates syntax, not observation provenance or authority. The real
fresh owner must retain its original writer/permit/native identity and obtain
observed_image_id only from its first actual private container parse. It must
check complete actual capture, terminal state and retirement through the real
command owner, then capture the exact image and same container. No caller DATA,
boolean, stage selector or returned RuntimeCommand can supply that proof. Lower
IO reuses this enum or a complete explicit closed mapping; it must not maintain
an independent template or offer a generic raw-format execution path.

This source extraction alone neither installs the fresh consumer nor changes
the currently documented unsupported status. Only the separately reviewed and
landed same-owner composition may do so. No Argv activation, stdin EOF or tested
engine support follows from these DATA builders.

Four pure source scenarios are AUTHORED_NOT_RUN. The existing qualification cap
remains exhausted at six; no additional native/compiler/runtime campaign runs.
The prior input producer required one source-only parentheses correction; this
separate delta does not reset that history or imply a native result. Actual
integration preimages and independent Astra review are required before freeze.
