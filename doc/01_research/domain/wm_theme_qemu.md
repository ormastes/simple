<!-- codex-research -->
# WM theme + QEMU domain research

QEMU's QMP `input-send-event` supports keyboard, pointer-button, and pointer
motion events, including device-targeted routing. It is appropriate for
automated diagnostic correlation, but it cannot prove a physical Cocoa-window
interaction. The project therefore keeps QMP evidence separate from the manual
visible-window acceptance row.

QMP also exposes monitor operations used by the existing wrappers for
framebuffer extraction. A valid theme test must bind a captured framebuffer to
the guest boot/session and to the observed input receipt; a host-side CSS parse
or source-order assertion is insufficient.

Sources: [QEMU QMP reference — input-send-event](https://www.qemu.org/docs/master/interop/qemu-qmp-ref.html), [QMP specification](https://www.qemu.org/docs/master/interop/qmp-spec.html).
