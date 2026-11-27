# DBD checked TLS sender

Source: [dbd_checked_send_spec.spl](../../../../../../test/01_unit/os/apps/dbd/dbd_checked_send_spec.spl).
Requirement: REQ-TLS-CHECKED-SEAL-003.

Status: **AUTHORED_UNRUN**. These two prevention scenarios were authored after
implementation; they are not evidence of test-first RED/GREEN.

1. Supply an invalid server key to the actual sender. Expect TransportFailed,
   failed TLS state and unchanged sequence zero.
2. Seal with valid traffic keys and send to descriptor -1. Expect actual
   transport failure with sequence one: encryption has consumed the nonce,
   so failed or partial transport must never roll that sequence back.

The tests use the actual DBD sender and transport interface, without a stub
provider. They have not run. Descriptor -1 checks error/state outcomes; it does
not measure syscall absence. The early Err return before the write call is
source-reviewed only. Instrumented actual-provider/socket evidence is still
required to establish no write on encryption failure.
