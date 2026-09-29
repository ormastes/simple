# Hosted SOSIX TCP compatibility boundary

Manual authored from the executable spec; execution and generated evidence
are pending a source-qualified pure-Simple runner.

1. Bind and listen on an ephemeral loopback socket, then inspect its local address.
2. Connect through TcpStream with a one-second timeout; accept through SOSIX
   with a one-second timeout.
3. Set one-second read timeouts, send `request` plus newline through the public
   descriptor helper, read the first byte through SOSIX's nullable byte route,
   and read the remaining line through its text route.
4. Observe the server's peer address, send `reply` plus newline through SOSIX,
   require a six-byte write and the exact reply on the client, then shut down
   the server's write half and observe an empty byte array for client EOF.
5. Close all three descriptors before asserting the exchange results.
6. Check public invalid-descriptor close/write guards, nullable SOSIX byte
   read and peer-address failures, and the boolean shutdown failure result.

The test fails if the host provider cannot bind, connect, accept or install read
timeouts. This is hosted synchronous acceptance only. SimpleOS transport,
asynchronous completion, native byte-read ABI qualification and object-code
alias qualification require separate evidence.
