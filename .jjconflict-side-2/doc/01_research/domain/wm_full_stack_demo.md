<!-- codex-research -->
# WM Full-Stack Demo — Domain Research

Date: 2026-07-29

## Window and Input Semantics

GLFW reports physical key transitions through key callbacks and Unicode
committed text through character callbacks. These must remain separate so a
shortcut such as Ctrl+C does not also insert `c`.

GLFW logical window size and framebuffer pixel size can differ. CPU-rendered
pixels must be sized and staged using framebuffer dimensions; content scale is
an independent UI/text metric. GLFW does not provide a CPU-pixel presentation
API, so the reference adapter needs a retained graphics resource and pixel
upload path.

Sources:

- <https://www.glfw.org/docs/latest/input>
- <https://www.glfw.org/docs/latest/window.html>

SDL3 likewise requires draining `SDL_PollEvent`, explicitly starting text input,
and using pixel rather than logical dimensions for raster backing stores.
SDL2 has the same one-event-per-poll/drain rule and separate committed-text
events.

Sources:

- <https://wiki.libsdl.org/SDL3/SDL_PollEvent>
- <https://wiki.libsdl.org/SDL3/SDL_TextInputEvent>
- <https://wiki.libsdl.org/SDL3/SDL_GetWindowSizeInPixels>
- <https://wiki.libsdl.org/SDL2/SDL_PollEvent>
- <https://wiki.libsdl.org/SDL2/Tutorials-TextInput>

## Audio Semantics

Miniaudio delivers interleaved PCM asynchronously through the device callback.
The callback writes all channels for each frame and must not start, stop, or
uninitialize the device. Control operations therefore need a synchronized
command/handle owner outside the callback.

SDL3 audio streams are suitable as a final device/conversion queue behind a
shared mixer: `SDL_PutAudioStreamData` copies input PCM, while
`SDL_OpenAudioDeviceStream` supports callback or explicit queueing and starts
paused.

Sources:

- <https://miniaud.io/docs/manual/index.html>
- <https://wiki.libsdl.org/SDL3/SDL_AudioStream>
- <https://wiki.libsdl.org/SDL3/SDL_OpenAudioDeviceStream>

## QEMU HDA

QEMU's documented Q35 graphical configuration uses `ich9-intel-hda` plus an
`hda-duplex` codec connected to an `-audiodev`. This is the reference virtual
hardware row for later guest PCI/BAR/DMA/IRQ evidence.

Sources:

- <https://gitlab.com/qemu-project/qemu/-/blob/d9a4282c4b690e45d25c2b933f318bb41eeb271d/docs/config/q35-virtio-graphical.cfg>
- <https://www.qemu.org/docs/master/system/qemu-manpage.html>

## UNO Q Processor Ownership

Arduino documents the QRB2210 as the quad Cortex-A53 Linux/Debian MPU with
Adreno graphics and the STM32U585 as the Cortex-M33 real-time MCU. The intended
split is high-level Linux services on the MPU and deterministic peripheral
control on the MCU, connected through RPC.

A desktop SimpleOS result must therefore boot and run on QRB2210/AArch64. The
STM32U585 lane may later serve as a coprocessor but cannot satisfy the desktop
gate.

Sources:

- <https://docs.arduino.cc/hardware/uno-q/>
- <https://docs.arduino.cc/resources/datasheets/ABX00162-datasheet.pdf>
- <https://www.st.com/en/microcontrollers-microprocessors/stm32u585ai.html>

The public board material found here exposes display/audio connectors but does
not unambiguously assign every signal to one processor. Board schematics and
the vendor SDK remain required before claiming direct driver ownership.
