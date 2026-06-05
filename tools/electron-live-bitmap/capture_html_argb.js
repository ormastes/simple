#!/usr/bin/env node
"use strict";
// Capture arbitrary HTML through real Chromium and export ARGB pixel buffer.
//
// Usage:
//   ELECTRON_CAPTURE_HTML=path.html \
//   ELECTRON_CAPTURE_WIDTH=320 \
//   ELECTRON_CAPTURE_HEIGHT=240 \
//   ELECTRON_CAPTURE_OUTPUT=build/pixel_compare/captured.json \
//   ELECTRON_CAPTURE_AUDIT_SELECTORS="#app,.widget-panel" \
//   ELECTRON_CAPTURE_AUDIT_OUTPUT=build/pixel_compare/audit.json \
//   ELECTRON_CAPTURE_MEDIA_FEATURES="prefers-contrast=more" \
//   ELECTRON_CAPTURE_FAIL_ON_AUDIT=1 \
//   xvfb-run --auto-servernum electron --no-sandbox --disable-gpu capture_html_argb.js

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const htmlPath = process.env.ELECTRON_CAPTURE_HTML || "";
const width = Number(process.env.ELECTRON_CAPTURE_WIDTH || 320);
const height = Number(process.env.ELECTRON_CAPTURE_HEIGHT || 240);
const outputPath = process.env.ELECTRON_CAPTURE_OUTPUT || "build/pixel_compare/captured.json";
const settleMs = Number(process.env.ELECTRON_CAPTURE_SETTLE_MS || 1500);
const auditSelectors = (process.env.ELECTRON_CAPTURE_AUDIT_SELECTORS || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);
const auditOutputPath = process.env.ELECTRON_CAPTURE_AUDIT_OUTPUT || "";
const contrastMinX100 = Number(process.env.ELECTRON_CAPTURE_CONTRAST_MIN_X100 || 450);
const touchMinPx = Number(process.env.ELECTRON_CAPTURE_TOUCH_MIN_PX || 44);
const failOnAudit = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_FAIL_ON_AUDIT || "");
const emulatedMediaFeatures = parseMediaFeatures(process.env.ELECTRON_CAPTURE_MEDIA_FEATURES || "");

function parseMediaFeatures(value) {
  return String(value || "")
    .split(",")
    .map(part => part.trim())
    .filter(Boolean)
    .map(part => {
      const eq = part.indexOf("=");
      if (eq < 1) return null;
      const name = part.slice(0, eq).trim();
      const featureValue = part.slice(eq + 1).trim();
      if (!name || !featureValue) return null;
      return { name, value: featureValue };
    })
    .filter(Boolean);
}

async function applyEmulatedMediaFeatures(win, features) {
  if (!features.length) return;
  const dbg = win.webContents.debugger;
  if (!dbg.isAttached()) dbg.attach("1.3");
  await dbg.sendCommand("Emulation.setEmulatedMedia", { features });
}

function bitmapToLogicalArgb(image) {
  const size = image.getSize();
  const native = image.toBitmap({ scaleFactor: 1 });
  const nw = size.width;
  const nh = size.height;
  if (nw === width && nh === height) {
    const pixels = new Uint32Array(width * height);
    for (let i = 0; i < width * height; i++) {
      const off = i * 4;
      const b = native[off];
      const g = native[off + 1];
      const r = native[off + 2];
      const a = native[off + 3];
      pixels[i] = ((a << 24) | (r << 16) | (g << 8) | b) >>> 0;
    }
    return { pixels, nativeWidth: nw, nativeHeight: nh, downsampled: false };
  }
  const sx = Math.round(nw / width);
  const sy = Math.round(nh / height);
  const pixels = new Uint32Array(width * height);
  for (let ly = 0; ly < height; ly++) {
    for (let lx = 0; lx < width; lx++) {
      let rSum = 0, gSum = 0, bSum = 0, aSum = 0, n = 0;
      for (let dy = 0; dy < sy; dy++) {
        for (let dx = 0; dx < sx; dx++) {
          const nx = lx * sx + dx;
          const ny = ly * sy + dy;
          if (nx < nw && ny < nh) {
            const off = (ny * nw + nx) * 4;
            bSum += native[off];
            gSum += native[off + 1];
            rSum += native[off + 2];
            aSum += native[off + 3];
            n++;
          }
        }
      }
      const r = Math.round(rSum / n);
      const g = Math.round(gSum / n);
      const b = Math.round(bSum / n);
      const a = Math.round(aSum / n);
      pixels[ly * width + lx] = ((a << 24) | (r << 16) | (g << 8) | b) >>> 0;
    }
  }
  return { pixels, nativeWidth: nw, nativeHeight: nh, downsampled: true };
}

async function collectAudit(win, selectors, mediaFeatures) {
  if (!selectors.length) return null;
  return win.webContents.executeJavaScript(`
    (() => {
      const selectors = ${JSON.stringify(selectors)};
      const mediaFeatures = ${JSON.stringify(mediaFeatures)};
      const contrastMinX100 = ${JSON.stringify(contrastMinX100)};
      const touchMinPx = ${JSON.stringify(touchMinPx)};
      const viewport = { width: window.innerWidth, height: window.innerHeight };
      const items = [];
      const entries = [];
      const rootStyle = window.getComputedStyle(document.documentElement);
      const mediaPreferenceResults = mediaFeatures.map(feature => {
        const query = "(" + feature.name + ": " + feature.value + ")";
        return {
          name: feature.name,
          value: feature.value,
          query,
          matches: window.matchMedia(query).matches
        };
      });
      const rootQualityTokens = {
        contrastPolicy: rootStyle.getPropertyValue("--ui-contrast-policy").trim(),
        text: rootStyle.getPropertyValue("--ui-text").trim(),
        dim: rootStyle.getPropertyValue("--ui-dim").trim(),
        accent: rootStyle.getPropertyValue("--ui-accent").trim(),
        glassOpacityFloorX100: rootStyle.getPropertyValue("--ui-glass-opacity-floor-x100").trim(),
        windowAlphaX100: rootStyle.getPropertyValue("--ui-window-alpha-x100").trim(),
        commandAlphaX100: rootStyle.getPropertyValue("--ui-command-alpha-x100").trim(),
        taskbarAlphaX100: rootStyle.getPropertyValue("--ui-taskbar-alpha-x100").trim(),
        widgetAlphaX100: rootStyle.getPropertyValue("--ui-widget-alpha-x100").trim(),
        motionOpenMs: rootStyle.getPropertyValue("--ui-motion-open-ms").trim(),
        motionCloseMs: rootStyle.getPropertyValue("--ui-motion-close-ms").trim(),
        motionMinimizeMs: rootStyle.getPropertyValue("--ui-motion-minimize-ms").trim(),
        wallpaperMotionMs: rootStyle.getPropertyValue("--ui-wallpaper-motion-ms").trim(),
        backdropDurationMs: rootStyle.getPropertyValue("--ui-backdrop-duration-ms").trim(),
        wallpaperState: rootStyle.getPropertyValue("--ui-wallpaper-state").trim()
      };
      function parseRgb(value) {
        const match = String(value || "").match(/rgba?\\((\\d+),\\s*(\\d+),\\s*(\\d+)(?:,\\s*([0-9.]+))?\\)/);
        if (!match) return null;
        return {
          r: Number(match[1]),
          g: Number(match[2]),
          b: Number(match[3]),
          a: match[4] === undefined ? 1 : Number(match[4])
        };
      }
      function luminance(c) {
        function channel(v) {
          const s = v / 255;
          return s <= 0.03928 ? s / 12.92 : Math.pow((s + 0.055) / 1.055, 2.4);
        }
        return 0.2126 * channel(c.r) + 0.7152 * channel(c.g) + 0.0722 * channel(c.b);
      }
      function composite(fg, bg) {
        if (!fg) return bg;
        if (!bg) return fg;
        const a = fg.a + bg.a * (1 - fg.a);
        if (a <= 0) return { r: 0, g: 0, b: 0, a: 0 };
        return {
          r: Math.round((fg.r * fg.a + bg.r * bg.a * (1 - fg.a)) / a),
          g: Math.round((fg.g * fg.a + bg.g * bg.a * (1 - fg.a)) / a),
          b: Math.round((fg.b * fg.a + bg.b * bg.a * (1 - fg.a)) / a),
          a
        };
      }
      function effectiveBackground(el, style) {
        let bg = parseRgb(style.backgroundColor);
        let parent = el.parentElement;
        while ((!bg || bg.a < 1) && parent) {
          const parentBg = parseRgb(window.getComputedStyle(parent).backgroundColor);
          if (parentBg && parentBg.a > 0) bg = composite(bg || { r: 0, g: 0, b: 0, a: 0 }, parentBg);
          parent = parent.parentElement;
        }
        if (!bg || bg.a < 1) bg = composite(bg || { r: 0, g: 0, b: 0, a: 0 }, parseRgb(window.getComputedStyle(document.body).backgroundColor) || { r: 10, g: 10, b: 15, a: 1 });
        return bg;
      }
      function contrastRatioX100(fg, bg) {
        if (!fg || !bg || fg.a === 0 || bg.a === 0) return null;
        const a = luminance(fg);
        const b = luminance(bg);
        const hi = Math.max(a, b);
        const lo = Math.min(a, b);
        return Math.round(((hi + 0.05) / (lo + 0.05)) * 100);
      }
      function isInteractive(el) {
        const tag = el.tagName.toLowerCase();
        const role = String(el.getAttribute("role") || "");
        return tag === "button" || tag === "input" || tag === "select" || tag === "textarea" ||
          role === "button" || role === "option" || role === "menuitem" || el.hasAttribute("tabindex");
      }
      function rectOf(el) {
        const r = el.getBoundingClientRect();
        return {
          left: Math.round(r.left),
          top: Math.round(r.top),
          right: Math.round(r.right),
          bottom: Math.round(r.bottom),
          width: Math.round(r.width),
          height: Math.round(r.height)
        };
      }
      function intersectsRect(a, b) {
        const left = Math.max(a.left, b.left);
        const top = Math.max(a.top, b.top);
        const right = Math.min(a.right, b.right);
        const bottom = Math.min(a.bottom, b.bottom);
        return {
          left,
          top,
          right,
          bottom,
          width: Math.max(0, right - left),
          height: Math.max(0, bottom - top)
        };
      }
      function clipsOverflow(style) {
        const clips = value => value === "hidden" || value === "auto" || value === "scroll" || value === "clip";
        return clips(style.overflowX) || clips(style.overflowY);
      }
      function visibleRectOf(el, rect) {
        let visible = intersectsRect(rect, { left: 0, top: 0, right: viewport.width, bottom: viewport.height });
        let parent = el.parentElement;
        while (visible.width > 0 && visible.height > 0 && parent && parent !== document.documentElement) {
          const parentStyle = window.getComputedStyle(parent);
          if (clipsOverflow(parentStyle)) visible = intersectsRect(visible, rectOf(parent));
          parent = parent.parentElement;
        }
        return visible;
      }
      function overlaps(a, b) {
        return a.left < b.right && a.right > b.left && a.top < b.bottom && a.bottom > b.top;
      }
      function containsElement(a, b) {
        return a !== b && a.contains(b);
      }
      function hasClass(item, name) {
        return String(item.className || "").split(/\\s+/).includes(name);
      }
      function isOverlay(item) {
        return hasClass(item, "wm-command-palette") ||
          hasClass(item, "wm-effect-controls") ||
          hasClass(item, "wm-quality-inspector");
      }
      function isOverlayContent(item) {
        return isOverlay(item) ||
          hasClass(item, "wm-command-item") ||
          hasClass(item, "wm-effect-control") ||
          hasClass(item, "wm-command-palette-input") ||
          hasClass(item, "wm-title-input");
      }
      function isWindowChrome(item) {
        return hasClass(item, "wm-window") ||
          hasClass(item, "wm-titlebar") ||
          hasClass(item, "wm-taskbar-item") ||
          hasClass(item, "wm-btn-close") ||
          hasClass(item, "wm-btn-minimize") ||
          hasClass(item, "wm-btn-maximize");
      }
      function allowedOverlayOverlap(a, b) {
        if (a.selector === "#wm-desktop" && hasClass(b, "wm-taskbar-item")) return true;
        if (b.selector === "#wm-desktop" && hasClass(a, "wm-taskbar-item")) return true;
        return (isOverlayContent(a) && isWindowChrome(b)) || (isOverlayContent(b) && isWindowChrome(a));
      }
      function isTextClipped(el, style) {
        const overflowedX = el.scrollWidth > el.clientWidth + 1;
        const overflowedY = el.scrollHeight > el.clientHeight + 1;
        if (!overflowedX && !overflowedY) return false;
        const visibleOrScrollable = value => value === "visible" || value === "auto" || value === "scroll";
        if ((overflowedX && visibleOrScrollable(style.overflowX)) || (overflowedY && visibleOrScrollable(style.overflowY))) return false;
        if (style.textOverflow === "ellipsis") return false;
        return Array.from(el.childNodes).some(node => node.nodeType === Node.TEXT_NODE && node.textContent.trim().length > 0) ||
          (el.children.length === 0 && String(el.textContent || "").trim().length > 0);
      }
      for (const selector of selectors) {
        const nodes = Array.from(document.querySelectorAll(selector));
        nodes.slice(0, 12).forEach((el, index) => {
          const style = window.getComputedStyle(el);
          const rawRect = rectOf(el);
          const rect = visibleRectOf(el, rawRect);
          if (rect.width <= 0 || rect.height <= 0) return;
          const effectiveBg = effectiveBackground(el, style);
          const contrastX100 = contrastRatioX100(parseRgb(style.color), effectiveBg);
          const interactive = isInteractive(el);
          const item = {
            selector,
            index,
            tag: el.tagName.toLowerCase(),
            className: String(el.className || ""),
            rect,
            rawRect,
            display: style.display,
            position: style.position,
            opacity: style.opacity,
            transform: style.transform,
            borderRadius: style.borderRadius,
            backgroundColor: style.backgroundColor,
            effectiveBackgroundColor: effectiveBg ? "rgba(" + effectiveBg.r + ", " + effectiveBg.g + ", " + effectiveBg.b + ", " + effectiveBg.a + ")" : "",
            color: style.color,
            overflowX: style.overflowX,
            overflowY: style.overflowY,
            contrastX100,
            contrastOk: contrastX100 === null ? null : contrastX100 >= contrastMinX100,
            interactive,
            touchOk: interactive ? rect.height >= touchMinPx && rect.width >= touchMinPx : null,
            clipped: isTextClipped(el, style)
          };
          items.push(item);
          entries.push({ el, item });
        });
      }
      const overlapPairs = [];
      const containedOverlapPairs = [];
      const allowedOverlayOverlapPairs = [];
      const unexpectedOverlapPairs = [];
      for (let i = 0; i < items.length; i++) {
        for (let j = i + 1; j < items.length; j++) {
          if (overlaps(items[i].rect, items[j].rect)) {
            const pair = {
              a: items[i].selector + "[" + items[i].index + "]",
              b: items[j].selector + "[" + items[j].index + "]"
            };
            overlapPairs.push(pair);
            if (containsElement(entries[i].el, entries[j].el) || containsElement(entries[j].el, entries[i].el)) {
              containedOverlapPairs.push(pair);
            } else if (allowedOverlayOverlap(items[i], items[j])) {
              allowedOverlayOverlapPairs.push(pair);
            } else {
              unexpectedOverlapPairs.push(pair);
            }
          }
        }
      }
      const clippedCount = items.filter(item => item.clipped).length;
      const unexpectedOverlapCount = unexpectedOverlapPairs.length;
      const contrastChecked = items.filter(item => item.contrastX100 !== null).length;
      const contrastFailures = items.filter(item => item.contrastOk === false).length;
      const touchChecked = items.filter(item => item.interactive).length;
      const touchFailures = items.filter(item => item.touchOk === false).length;
      const failureReasons = [];
      if (unexpectedOverlapCount > 0) failureReasons.push("unexpected-overlap");
      if (clippedCount > 0) failureReasons.push("text-clipping");
      if (contrastFailures > 0) failureReasons.push("contrast");
      if (touchFailures > 0) failureReasons.push("touch-target");
      const mediaPreferenceFailures = [];
      mediaPreferenceResults.forEach(result => {
        if (!result.matches) mediaPreferenceFailures.push(result.name + "=" + result.value + ":no-match");
        if ((result.name === "prefers-contrast" && result.value === "more") ||
            (result.name === "forced-colors" && result.value === "active")) {
          if (rootQualityTokens.contrastPolicy !== "os-high") {
            mediaPreferenceFailures.push(result.name + "=" + result.value + ":contrast-policy-" + rootQualityTokens.contrastPolicy);
          }
        }
        if (result.name === "prefers-reduced-motion" && result.value === "reduce") {
          if (rootQualityTokens.motionOpenMs !== "0" ||
              rootQualityTokens.motionCloseMs !== "0" ||
              rootQualityTokens.motionMinimizeMs !== "0") {
            mediaPreferenceFailures.push("prefers-reduced-motion=reduce:lifecycle-motion-" +
              rootQualityTokens.motionOpenMs + "-" +
              rootQualityTokens.motionCloseMs + "-" +
              rootQualityTokens.motionMinimizeMs);
          }
          if (rootQualityTokens.wallpaperMotionMs !== "0" ||
              rootQualityTokens.backdropDurationMs !== "0" ||
              rootQualityTokens.wallpaperState !== "wallpaper_static") {
            mediaPreferenceFailures.push("prefers-reduced-motion=reduce:backdrop-motion-" +
              rootQualityTokens.wallpaperMotionMs + "-" +
              rootQualityTokens.backdropDurationMs + "-" +
              rootQualityTokens.wallpaperState);
          }
        }
      });
      if (mediaPreferenceFailures.length > 0) failureReasons.push("media-preference");
      return {
        producer: "electron-chromium-dom-audit",
        viewport,
        selectors,
        emulatedMediaFeatures: mediaFeatures,
        mediaPreferenceResults,
        rootQualityTokens,
        thresholds: {
          contrastMinX100,
          touchMinPx
        },
        items,
        overlapPairs,
        containedOverlapPairs,
        allowedOverlayOverlapPairs,
        unexpectedOverlapPairs,
        clippedCount,
        unexpectedOverlapCount,
        contrastChecked,
        contrastFailures,
        touchChecked,
        touchFailures,
        mediaPreferenceFailures,
        failureReasons,
        pass: failureReasons.length === 0
      };
    })()
  `);
}

async function main() {
  if (!htmlPath) {
    console.error("ELECTRON_CAPTURE_HTML is required");
    process.exit(1);
  }

  await app.whenReady();
  const win = new BrowserWindow({
    show: false,
    useContentSize: true,
    width,
    height,
    backgroundColor: "#ffffff",
    webPreferences: {
      offscreen: false,
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  win.setContentSize(width, height);

  const absHtml = path.resolve(htmlPath);
  await win.loadFile(absHtml);
  await applyEmulatedMediaFeatures(win, emulatedMediaFeatures);
  await new Promise(r => setTimeout(r, settleMs));

  const audit = await collectAudit(win, auditSelectors, emulatedMediaFeatures);
  const image = await win.capturePage({ x: 0, y: 0, width, height });
  const result = bitmapToLogicalArgb(image);

  const payload = {
    width,
    height,
    format: "argb-u32",
    producer: "electron-chromium-capture",
    nativeWidth: result.nativeWidth,
    nativeHeight: result.nativeHeight,
    downsampled: result.downsampled,
    pixels: Array.from(result.pixels, v => v >>> 0),
  };
  if (audit) payload.audit = audit;

  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, JSON.stringify(payload));
  if (audit && auditOutputPath) {
    fs.mkdirSync(path.dirname(auditOutputPath), { recursive: true });
    fs.writeFileSync(auditOutputPath, JSON.stringify(audit, null, 2));
  }
  console.log("captured=" + outputPath);
  console.log("size=" + width + "x" + height);
  console.log("native=" + result.nativeWidth + "x" + result.nativeHeight);
  console.log("downsampled=" + result.downsampled);
  console.log("pixels=" + result.pixels.length);
  if (audit) {
    console.log("audit_items=" + audit.items.length);
    console.log("audit_overlaps=" + audit.overlapPairs.length);
    console.log("audit_contained_overlaps=" + audit.containedOverlapPairs.length);
    console.log("audit_allowed_overlaps=" + audit.allowedOverlayOverlapPairs.length);
    console.log("audit_unexpected_overlaps=" + audit.unexpectedOverlapCount);
    console.log("audit_clipped=" + audit.clippedCount);
    console.log("audit_contrast_checked=" + audit.contrastChecked);
    console.log("audit_contrast_failures=" + audit.contrastFailures);
    console.log("audit_touch_checked=" + audit.touchChecked);
    console.log("audit_touch_failures=" + audit.touchFailures);
    console.log("audit_media_features=" + audit.emulatedMediaFeatures.map(feature => feature.name + "=" + feature.value).join(","));
    console.log("audit_media_preference_failures=" + audit.mediaPreferenceFailures.join(","));
    console.log("audit_pass=" + audit.pass);
    console.log("audit_failure_reasons=" + audit.failureReasons.join(","));
    console.log("audit_fail_on_audit=" + failOnAudit);
    if (auditOutputPath) console.log("audit=" + auditOutputPath);
    if (failOnAudit && !audit.pass) {
      console.error("audit_failed=" + audit.failureReasons.join(","));
      process.exitCode = 2;
      app.exit(2);
      return;
    }
  }

  app.quit();
}

main().catch(e => {
  console.error(e);
  process.exit(1);
});
