# Enabling Vulkan in Electron (Desktop) vs Tauri v2 (Android)

**Date:** 2026-06-16
**Domain:** ui / render_path
**Status:** Research — exact methods and settings for both frameworks

Related: [`gui_web_2d_render_optimization_2026-06-16.md`](gui_web_2d_render_optimization_2026-06-16.md)

---

## Summary

The approach is **completely different** between the two frameworks. Electron
gives you direct control over Chromium; Tauri on Android forces you to rely on
the Android operating system. For Electron, inject `app.commandLine` switches in
the main process. For Tauri Android, trust the OS — modern Android forces Vulkan
(via Skia) automatically, and there is no config-file switch to override it.

---

## 1. Electron (Desktop): full Vulkan enable method

Because you bundle Chromium yourself in Electron, you have full access to its
internal command-line switches. Apply these settings in your **Main Process**
(`main.js` / `main.ts`) **before** the app is ready.

```javascript
const { app } = require('electron');

// 1. Enable the Vulkan feature flag
app.commandLine.appendSwitch('enable-features', 'Vulkan');

// 2. Force the graphics backend to use Vulkan
app.commandLine.appendSwitch('use-vulkan');

// 3. (Optional but recommended) Force ANGLE to translate WebGL via Vulkan
app.commandLine.appendSwitch('use-angle', 'vulkan');

// 4. (Optional) If using WebGPU, enable it to utilize the Vulkan backend
app.commandLine.appendSwitch('enable-unsafe-webgpu');

app.whenReady().then(() => {
  // Create your BrowserWindow here
});
```

**Important Linux note:** If targeting Linux via Electron, Wayland windowing can
sometimes interfere with Vulkan. You may also need to conditionally append
`--ozone-platform=wayland` depending on the user's desktop environment.

---

## 2. Tauri v2 (Android): the "hands-off" method

For Tauri v2 on Android, **you cannot pass Chrome command-line flags to force
Vulkan.**

Google intentionally prevents developers from passing raw Chromium flags (like
`--use-vulkan`) to the Android System WebView in production apps, to prevent
breaking system stability or bypassing security. There is **no** setting in
`tauri.conf.json` or native Kotlin code that will force it.

### It is automatic (on modern devices)

You usually don't need to turn it on. Starting around Android 10, Google
integrated a rendering engine called **Skia**. On modern Android devices with
capable hardware, the Android System OS automatically defaults the WebView to use
the **Skia Vulkan backend**.

- If the device supports it and the drivers are stable, **Tauri is already using
  Vulkan.**
- If the phone is older or has buggy Vulkan drivers, Android automatically falls
  back to OpenGL ES. You cannot override this OS-level decision.

### How to verify what Android is doing

While you can't force it, you can check what the WebView is using during
development:

1. Run your Tauri app on an Android device via `tauri android dev`.
2. Open desktop Google Chrome and navigate to `chrome://inspect/#devices`.
3. Find your Tauri app under the connected Android device and click **Inspect**.
4. In the DevTools console, evaluate rendering performance and check whether
   hardware acceleration is utilizing Vulkan under the hood.

---

## Takeaway for Simple

- **Desktop / bundled-Chromium lane:** Simple's own Engine2D/Vulkan backend (and
  any Electron-style host) can deterministically force Vulkan via command-line
  switches — matching the explicit-control model in the render-optimization
  research.
- **System-WebView lane (Android):** treat Vulkan as an OS-controlled,
  best-effort acceleration; design the render path to behave identically whether
  the WebView resolves to Vulkan or OpenGL ES, and verify via `chrome://inspect`
  rather than assuming a switch took effect.
