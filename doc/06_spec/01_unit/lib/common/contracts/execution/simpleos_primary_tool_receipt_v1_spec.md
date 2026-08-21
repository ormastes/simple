# Authenticated primary tool receipt

The receipt gate admits no tool merely because its Simple source exists.

- Missing signatures are rejected.
- Expired receipts and excessive validity windows are rejected before use.
- A receipt signed for a key other than the loader-configured trust root is rejected.
- Successful cryptographic verification is input to loader admission, not a process-launch token.
