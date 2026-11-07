# Windows Container stream detail design

The first source slice is `windows_managed_stream_owner_v2`: a portable wrapper
selects Windows-only launch, policy and byte-I/O modules. The existing PTY owner
retains all Job/process/pipe/event/attribute/file/CNG/allocation identities in its
nonreused generation-checked slots. Legacy integer PTY calls reject managed
slots. Raw stdout and stderr are deliberately merged; this is not a TTY or a
claim of separate output channels.

Admission validates exact CPU quantization and host prerequisites, pins and
hashes at most 256 MiB of the helper image, checks the launch clock during the
bounded hash loop, builds typed argv and a replacement environment, and creates
private pipes with an explicit inherited HANDLE_LIST. It configures and reads
back Job aggregate memory and hard CPU limits before suspended process creation.
After Job assignment, parent child-only pipe ends close before the final clock
check and resume. Failed admissions return their cleanup lease.

Writes accept one bounded prefix into retained OVERLAPPED storage; zero means
backpressure. Ambiguous completion disables further submission to prevent replay.
Reads expose bounded bytes to one logical reader. Collection requires observed
leader exit, exact Job emptiness, completed pending I/O and drained output or an
explicit cancellation. A cancellation request is not a terminal receipt. Failed
native releases retain their exact identities for cleanup; historical failures
are not rewritten into successful qualification.

The next provider slice uses these raw pipes solely for a pinned private Engine
broker. Its API1.48 wire codec bounds headers, control bodies and Docker mux
frames; internal templates and birth receipts remain SDN. Native Engine IDs are
observed values. Requested exec User and observed container Config.User are
separate from an unavailable Windows exec-token observation. Required native
pipe, private-root persistence and authenticated ongoing input/resize consumers
must be connected before advertising terminal support.
