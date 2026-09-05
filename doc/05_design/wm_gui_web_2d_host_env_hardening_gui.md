# WM/GUI/Web/2D Evidence Capture Design

No new product GUI is added. The existing hosted WM window is the tested UI.

```text
+----------------------------------------------------------+
| Hosted Simple WM                             [ _ ][ □ ][x]|
| +------------------------------------------------------+ |
| | <input id="name">                                   | |
| | [ Apply ]                                            | |
| | state: input/click callback changes visible pixels   | |
| +------------------------------------------------------+ |
+----------------------------------------------------------+
        pointer/text
             |
             v
  receipt.env + framebuffer.argb + window.png + optional .rdc
```

The live fixture exposes stable semantic IDs and flat ARGB colors so pointer,
text mutation, state change, and exact readback can be correlated without
image tolerance.
