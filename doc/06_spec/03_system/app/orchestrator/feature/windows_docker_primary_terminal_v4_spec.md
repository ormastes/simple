# Windows explicit primary terminal request v4

Status: **SOURCE-ONLY NOT_RUN**. No compiler, build, specification, native
Windows process, Docker create/start/attach or terminal resize was executed.

Typed WindowsDockerRequestV1 now includes terminal_tty and stdin_open, both
default false. A request with either true uses canonical SDN version4 with both
required boolean fields terminalTty/stdinOpen. Working directory and mounts keep
their existing optional/required semantics. Versions1/2/3 retain their original
encode and semantic-digest branches when both new fields are false. Explicit
false fields do not smuggle flags into an older schema. Version4 with both false,
duplicate/missing/mistyped fields, downgrade and digest mutation are rejected.
Unknown-version tests now use version5.

The version4 digest binds both typed booleans in addition to all existing
policy/request/cwd/mount data. Actual Docker create adds --tty only for
terminal_tty and --interactive only for stdin_open. All existing false-default
create commands and inspection formats retain their previous shape. The
portable request/resource projection remains unchanged; broker must derive
primary TTY/stdin mode from this decoded retained request, never a caller's
independent stream intent. Exec TTY remains a separate request.

Explicit terminal requests append actual Config.Tty, OpenStdin, StdinOnce and
AttachStdin to the exact scoped native-object inspection. Expected values are
terminal_tty, stdin_open, stdin_open and stdin_open respectively. Such requests
also verify actual zero/one mount count, including hidden image mounts. Create,
start and exact recovery all use these actual metadata checks before success.

[Official Docker CLI opts.go](https://github.com/docker/cli/blob/master/cli/command/container/opts.go)
sets AttachStdin when interactive is requested, maps stdin/tty flags to OpenStdin
and Tty, then sets StdinOnce when both OpenStdin and AttachStdin are true. No
attach-option override is emitted by this provider.
[Docker Engine API1.48](https://docs.docker.com/reference/api/engine/version/v1.48/)
defines StdinOnce as closing stdin after the first attached client disconnects.
This source therefore does not promise persistent stdin across an Engine attach
disconnection. A retained private broker may maintain its own Engine connection;
that separate lifetime must be qualified, and client UI detach must not be
confused with Engine stdin EOF or process termination. No host ConPTY is used.

Authored scenarios cover all three nondefault flag combinations, version1/2/3
selection with false defaults, version4 plus mounts, strict record mutations,
flag-dependent digests, actual create/start confirmation and actual terminal
mismatch. Failed confirmation keeps the exact candidate unknown until matching
scoped recovery; mutated retained flags refuse recovery or duplicate create
without more commands. Cursor assertions are authored contract checks only, not
observed pass counts or Windows qualification.

An early concern about empty CLI command inheritance was corrected: official
[CLI entrypoint documentation](https://github.com/docker/cli/blob/master/docs/reference/run.md)
states --entrypoint clears image CMD. No semantic rewrite was made on that
assumption. Actual Engine request/TTY/stdin, live primary resize, birth receipt
persistence and end-to-end interactive effects still require their separate
real-owner integration and native tests.
