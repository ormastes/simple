# SimpleOS WM Visible-Display Boot-Ladder Contract

This manual verifies the evidence wrapper’s observation order without building
SimpleOS or launching QEMU.

## Scenario: classify serial-log states

1. Run the bounded boot-ladder self-test:

   ```sh
   sh scripts/check/check-simpleos-wm-visible-display-evidence.shs --self-test
   ```

2. Confirm the output reports `pass` for absent-log classification,
   marker-absent classification, complete-ladder classification, and ordering.
3. An absent file must report `serial-log-not-created-at-check-time`.
4. An existing file missing a rung must instead report
   `marker-absent-in-existing-serial-log`.

The self-test uses temporary serial fixtures only. It does not invoke the
compiler, QEMU, a browser, or framebuffer capture.

## Scenario: preserve production ordering

1. Start from the persistent-QEMU path.
2. Wait for the shared renderer’s serial-marker set.
3. Evaluate the UEFI ladder with observation
   `serial-markers-established`.
4. Continue with the same live QEMU process into QMP screendump and pixel
   validation.
5. If the marker wait fails, quiesce QEMU first, then evaluate with observation
   `failure-after-qemu-quiescence`.

This ordering prevents a newly created QMP socket from being mistaken for
serial-log readiness while preserving fail-closed capture behavior.
