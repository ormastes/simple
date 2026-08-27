#!/usr/bin/env node
const fs = require('fs');
const zlib = require('zlib');

// UHD 8K RGBA scanlines occupy 132,714,720 bytes. Keep enough headroom for
// PNG/zlib framing while bounding every screenshot-controlled allocation.
const MAX_SCREENSHOT_COMPRESSED_BYTES = 160 * 1024 * 1024;
const MAX_SCREENSHOT_INFLATED_BYTES = 160 * 1024 * 1024;

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function emit(key, value) {
  console.log(`${key}=${clean(value)}`);
}

function decimalIntegerText(value) {
  if (typeof value === 'bigint') return value.toString();
  if (typeof value === 'string' && /^[0-9]+$/.test(value.trim())) return value.trim();
  return null;
}

function integerNumberAtLeast(value, min) {
  return typeof value === 'number' && Number.isInteger(value) && value >= min;
}

function finiteNumberGreaterThan(value, min) {
  return typeof value === 'number' && Number.isFinite(value) && value > min;
}

function finiteNumberAtMost(value, max) {
  return typeof value === 'number' && Number.isFinite(value) && value <= max;
}

function jsonIntegerTextOrBlank(value) {
  return typeof value === 'number' && Number.isInteger(value) ? String(value) : '';
}

function jsonNumberTextOrBlank(value) {
  return typeof value === 'number' && Number.isFinite(value) ? String(value) : '';
}

function jsonBoolTextOrBlank(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return '';
}

function textSample(value) {
  return typeof value === 'string' ? value : '';
}

function versionText(value) {
  return typeof value === 'string' && /^[0-9]+(?:\.[0-9]+)*$/.test(value);
}

function proofSourceArtifact(marker) {
  const [filePath, symbol] = marker.split(':');
  let stat;
  try {
    stat = fs.lstatSync(filePath);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  if (stat.isSymbolicLink()) return { status: 'symlink', size: '', actualSize: '' };
  if (!stat.isFile()) return { status: 'not-regular', size: '', actualSize: '' };
  const actualSize = String(stat.size);
  if (stat.nlink > 1) return { status: 'hardlink', size: actualSize, actualSize };
  if (stat.size <= 0) return { status: 'empty', size: '0', actualSize: '0' };
  let source = '';
  try {
    source = fs.readFileSync(filePath, 'utf8');
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  if (!source.includes(`function ${symbol}`) || !source.includes(`proof_source: '${marker}'`)) {
    return { status: 'symbol-missing', size: actualSize, actualSize };
  }
  return { status: 'pass', size: actualSize, actualSize };
}

function pngCrc32(bytes) {
  if (typeof zlib.crc32 === 'function') return zlib.crc32(bytes) >>> 0;
  let crc = 0xffffffff;
  for (const byte of bytes) {
    crc ^= byte;
    for (let bit = 0; bit < 8; bit += 1) {
      crc = (crc >>> 1) ^ (crc & 1 ? 0xedb88320 : 0);
    }
  }
  return (crc ^ 0xffffffff) >>> 0;
}

function pngArtifact(filePath, expectedSize, expectedWidth, expectedHeight) {
  if (typeof filePath !== 'string' || filePath.length === 0) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  let stat;
  try {
    stat = fs.lstatSync(filePath);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  if (stat.isSymbolicLink()) return { status: 'symlink', size: '', actualSize: '' };
  if (!stat.isFile()) return { status: 'not-regular', size: '', actualSize: '' };
  const actualSize = String(stat.size);
  if (stat.nlink > 1) return { status: 'hardlink', size: actualSize, actualSize };
  if (stat.size <= 8) return { status: 'empty', size: actualSize, actualSize };
  if (stat.size > MAX_SCREENSHOT_COMPRESSED_BYTES) {
    return { status: 'too-large', size: actualSize, actualSize };
  }
  const expectedSizeText = jsonIntegerTextOrBlank(expectedSize);
  if (expectedSizeText && expectedSizeText !== actualSize) {
    return { status: 'size-mismatch', size: expectedSizeText, actualSize };
  }
  const largestExpectedPayload = (expectedWidth * 4 + 1) * expectedHeight;
  if (
    !Number.isSafeInteger(largestExpectedPayload) ||
    largestExpectedPayload < 1 ||
    largestExpectedPayload > MAX_SCREENSHOT_INFLATED_BYTES
  ) {
    return { status: 'invalid-payload', size: actualSize, actualSize };
  }
  let bytes;
  try {
    bytes = fs.readFileSync(filePath);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  const pngSignature = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
  if (bytes.length < 8 || !bytes.subarray(0, 8).equals(pngSignature)) {
    return { status: 'not-png', size: actualSize, actualSize };
  }
  try {
    let position = 8;
    let width = 0;
    let height = 0;
    let bytesPerPixel = 0;
    let sawHeader = false;
    let sawData = false;
    let dataClosed = false;
    let sawEnd = false;
    const imageData = [];
    let imageDataBytes = 0;
    while (position < bytes.length) {
      if (bytes.length - position < 12) throw new Error('truncated chunk');
      const length = bytes.readUInt32BE(position);
      const end = position + 12 + length;
      if (end > bytes.length) throw new Error('chunk out of bounds');
      const typeBytes = bytes.subarray(position + 4, position + 8);
      const type = typeBytes.toString('ascii');
      const data = bytes.subarray(position + 8, position + 8 + length);
      if (
        (typeBytes[0] & 0x20) === 0 &&
        pngCrc32(Buffer.concat([typeBytes, data])) !== bytes.readUInt32BE(position + 8 + length)
      ) {
        throw new Error('critical chunk crc mismatch');
      }
      if (!sawHeader && type !== 'IHDR') throw new Error('IHDR must be first');
      if (type === 'IHDR') {
        if (sawHeader || length !== 13) throw new Error('invalid IHDR');
        width = data.readUInt32BE(0);
        height = data.readUInt32BE(4);
        if (width !== expectedWidth || height !== expectedHeight) {
          return { status: 'dimensions-mismatch', size: actualSize, actualSize };
        }
        if (
          width < 1 || height < 1 || data[8] !== 8 ||
          (data[9] !== 2 && data[9] !== 6) ||
          data[10] !== 0 || data[11] !== 0 || data[12] !== 0
        ) {
          throw new Error('unsupported IHDR');
        }
        bytesPerPixel = data[9] === 6 ? 4 : 3;
        sawHeader = true;
      } else if (type === 'IDAT') {
        if (!sawHeader || dataClosed || sawEnd) throw new Error('invalid IDAT order');
        if (length > MAX_SCREENSHOT_COMPRESSED_BYTES - imageDataBytes) {
          throw new Error('compressed PNG too large');
        }
        imageDataBytes += length;
        imageData.push(data);
        if (length > 0) sawData = true;
      } else if (type === 'IEND') {
        if (!sawData || length !== 0 || end !== bytes.length) throw new Error('invalid IEND');
        sawEnd = true;
      } else {
        if (sawData) dataClosed = true;
        if ((typeBytes[0] & 0x20) === 0 && type !== 'PLTE') throw new Error('unknown critical chunk');
        if (type === 'PLTE' && sawData) throw new Error('invalid PLTE order');
      }
      position = end;
      if (sawEnd) break;
    }
    if (!sawHeader || !sawData || !sawEnd || position !== bytes.length) {
      throw new Error('incomplete PNG');
    }
    const stride = width * bytesPerPixel;
    const expectedInflatedSize = (stride + 1) * height;
    if (
      !Number.isSafeInteger(expectedInflatedSize) ||
      expectedInflatedSize < 1 ||
      expectedInflatedSize > MAX_SCREENSHOT_INFLATED_BYTES
    ) {
      throw new Error('inflated PNG too large');
    }
    const inflated = zlib.inflateSync(Buffer.concat(imageData), {
      maxOutputLength: expectedInflatedSize + 1,
    });
    if (inflated.length !== expectedInflatedSize) throw new Error('pixel payload size mismatch');
    let checksum = 0;
    let nonTransparent = 0;
    const distinct = new Set();
    let previous = Buffer.alloc(stride);
    for (let row = 0; row < height; row += 1) {
      const start = row * (stride + 1);
      const filter = inflated[start];
      if (filter > 4) throw new Error('invalid row filter');
      const current = inflated.subarray(start + 1, start + 1 + stride);
      for (let offset = 0; offset < stride; offset += 1) {
        const left = offset >= bytesPerPixel ? current[offset - bytesPerPixel] : 0;
        const above = previous[offset];
        const upperLeft = offset >= bytesPerPixel ? previous[offset - bytesPerPixel] : 0;
        if (filter === 1) current[offset] = (current[offset] + left) & 255;
        else if (filter === 2) current[offset] = (current[offset] + above) & 255;
        else if (filter === 3) current[offset] = (current[offset] + ((left + above) >> 1)) & 255;
        else if (filter === 4) {
          const estimate = left + above - upperLeft;
          const leftDistance = Math.abs(estimate - left);
          const aboveDistance = Math.abs(estimate - above);
          const upperLeftDistance = Math.abs(estimate - upperLeft);
          const paeth = leftDistance <= aboveDistance && leftDistance <= upperLeftDistance
            ? left
            : aboveDistance <= upperLeftDistance ? above : upperLeft;
          current[offset] = (current[offset] + paeth) & 255;
        }
      }
      for (let pixel = 0; pixel < width; pixel += 1) {
        const offset = pixel * bytesPerPixel;
        const red = current[offset];
        const green = current[offset + 1];
        const blue = current[offset + 2];
        const alpha = bytesPerPixel === 4 ? current[offset + 3] : 255;
        const bitmapIndex = (row * width + pixel) * 4;
        checksum = (
          checksum +
          ((red + 1) * 3) +
          ((green + 1) * 5) +
          ((blue + 1) * 7) +
          ((alpha + 1) * 11) +
          bitmapIndex
        ) >>> 0;
        if (alpha !== 0) nonTransparent += 1;
        if (distinct.size < 4096) distinct.add(`${red},${green},${blue},${alpha}`);
      }
      previous = current;
    }
    return {
      status: 'pass',
      size: actualSize,
      actualSize,
      checksum,
      nonTransparent,
      distinctColorCount: distinct.size,
    };
  } catch (_err) {
    return { status: 'invalid-payload', size: actualSize, actualSize };
  }
}

function artifactStatus(artifact) {
  return artifact.status === 'pass' &&
    artifact.size !== '' &&
    artifact.actualSize !== '' &&
    artifact.size === artifact.actualSize
    ? 'pass'
    : 'fail';
}

const [proofPath, widthText, heightText] = process.argv.slice(2);
if (!proofPath || !widthText || !heightText) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'usage-proof-width-height');
  process.exit(1);
}

let proofPathStat;
try {
  proofPathStat = fs.lstatSync(proofPath);
} catch (err) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', `missing-proof-json:${err && err.message ? err.message : err}`);
  emit('electron_live_smoke_proof_symlink_status', 'unknown');
  emit('electron_live_smoke_proof_hardlink_status', 'unknown');
  process.exit(1);
}

if (proofPathStat.isSymbolicLink()) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'proof-json-symlink');
  emit('electron_live_smoke_proof_symlink_status', 'fail');
  emit('electron_live_smoke_proof_hardlink_status', 'unknown');
  process.exit(1);
}

if (!proofPathStat.isFile()) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'proof-json-not-regular');
  emit('electron_live_smoke_proof_symlink_status', 'pass');
  emit('electron_live_smoke_proof_hardlink_status', 'pass');
  process.exit(1);
}

if (proofPathStat.nlink > 1) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'proof-json-hardlink');
  emit('electron_live_smoke_proof_symlink_status', 'pass');
  emit('electron_live_smoke_proof_hardlink_status', 'fail');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const expectedWidthText = decimalIntegerText(widthText);
const expectedHeightText = decimalIntegerText(heightText);
const expectedWidth = expectedWidthText === null ? NaN : Number(expectedWidthText);
const expectedHeight = expectedHeightText === null ? NaN : Number(expectedHeightText);
// HiDPI/Retina captures are physical pixels: a 1280x720 logical window yields a
// 2560x1440 bitmap at scale factor 2. The proof self-reports the scale factor
// measured from the capture; the independently parsed PNG IHDR must still match
// the scaled expectation, so a misreported factor cannot launder a bad capture.
// Absent/invalid factor defaults to 1 (Linux/xvfb behavior unchanged).
const screenshotScaleFactor =
  typeof proof.screenshot_scale_factor === 'number' &&
  Number.isFinite(proof.screenshot_scale_factor) &&
  proof.screenshot_scale_factor >= 1
    ? proof.screenshot_scale_factor
    : 1;
const expectedScreenshotWidth = Math.round(expectedWidth * screenshotScaleFactor);
const expectedScreenshotHeight = Math.round(expectedHeight * screenshotScaleFactor);
const expectedProofSource = 'src/app/ui.electron/bridge.js:electronLiveSmokeProofScript';
const proofSource = proofSourceArtifact(expectedProofSource);
const screenshotArtifact = pngArtifact(
  proof.screenshot_path,
  proof.screenshot_png_size_bytes,
  expectedScreenshotWidth,
  expectedScreenshotHeight
);
const proofSourceArtifactStatus = artifactStatus(proofSource);
const screenshotArtifactStatus = artifactStatus(screenshotArtifact);
const userAgent = textSample(proof.electron_user_agent);
const maxEventTimingMs = 1000;
const maxEventDispatchToPaintMs = 1000;

let reason = 'pass';
if (proof.target !== 'electron') {
  reason = 'unexpected-target';
} else if (proof.surface_id !== 'main') {
  reason = 'unexpected-surface';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'unexpected-proof-source';
} else if (proofSource.status !== 'pass') {
  reason = `unexpected-proof-source-file-${proofSource.status}`;
} else if (proof.browser_engine !== 'chromium') {
  reason = 'unexpected-browser-engine';
} else if (!/Electron\/[0-9]/.test(userAgent) || !/(Chrome|Chromium)\/[0-9]/.test(userAgent)) {
  reason = 'missing-electron-chromium-user-agent';
} else if (!versionText(proof.electron_process_version) || !versionText(proof.chrome_process_version)) {
  reason = 'missing-electron-chromium-process-versions';
} else if (!Number.isInteger(expectedWidth) || expectedWidth < 1 || proof.width !== expectedWidth) {
  reason = 'unexpected-width';
} else if (!Number.isInteger(expectedHeight) || expectedHeight < 1 || proof.height !== expectedHeight) {
  reason = 'unexpected-height';
} else if (!integerNumberAtLeast(proof.body_html_length, 1)) {
  reason = 'missing-render-html';
} else if (!integerNumberAtLeast(proof.css_length, 1)) {
  reason = 'missing-render-css';
} else if (proof.app_element_present !== true) {
  reason = 'missing-app-element';
} else if (!integerNumberAtLeast(proof.body_text_length, 1)) {
  reason = 'missing-rendered-text';
} else if (
  textSample(proof.body_text_sample).length < 1 ||
  !textSample(proof.body_text_sample).includes('Hello World from Web!') ||
  textSample(proof.body_text_sample).length > proof.body_text_length
) {
  reason = 'missing-rendered-text-sample';
} else if (
  proof.performance_now_available !== true ||
  !finiteNumberGreaterThan(proof.performance_now_delta_ms, 0) ||
  !finiteNumberAtMost(proof.performance_now_delta_ms, maxEventTimingMs)
) {
  reason = 'missing-performance-now';
} else if (proof.animation_frame_available !== true || !integerNumberAtLeast(proof.animation_frame_count, 2)) {
  reason = 'missing-animation-frames';
} else if (proof.css_animation_probe !== true) {
  reason = 'missing-css-animation';
} else if (
  proof.event_dispatch_available !== true ||
  !integerNumberAtLeast(proof.event_dispatch_count, 1) ||
  proof.event_dispatch_type !== 'simple-electron-live-smoke-event' ||
  proof.event_dispatch_detail !== 'live-smoke-input' ||
  textSample(proof.event_dispatch_error).length > 0
) {
  reason = 'missing-event-dispatch';
} else if (
  !finiteNumberGreaterThan(proof.event_dispatch_to_paint_ms, 0) ||
  !finiteNumberAtMost(proof.event_dispatch_to_paint_ms, maxEventDispatchToPaintMs)
) {
  reason = 'missing-event-dispatch-to-paint';
} else if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (textSample(proof.screenshot_error).length > 0) {
  reason = 'screenshot-capture-error';
} else if (screenshotArtifact.status !== 'pass') {
  reason = `screenshot-artifact-${screenshotArtifact.status}`;
} else if (proof.screenshot_width !== expectedScreenshotWidth || proof.screenshot_height !== expectedScreenshotHeight) {
  reason = 'screenshot-dimensions-mismatch';
} else if (!integerNumberAtLeast(proof.screenshot_png_size_bytes, 9)) {
  reason = 'screenshot-png-size-missing';
} else if (proof.screenshot_bitmap_byte_count !== expectedScreenshotWidth * expectedScreenshotHeight * 4) {
  reason = 'screenshot-bitmap-size-mismatch';
} else if (!integerNumberAtLeast(proof.screenshot_pixel_checksum, 1)) {
  reason = 'screenshot-pixel-checksum-missing';
} else if (!integerNumberAtLeast(proof.screenshot_nontransparent_pixel_count, 1)) {
  reason = 'screenshot-nontransparent-pixels-missing';
} else if (!integerNumberAtLeast(proof.screenshot_distinct_color_count, 2)) {
  reason = 'screenshot-distinct-colors-missing';
} else if (proof.screenshot_pixel_checksum !== screenshotArtifact.checksum) {
  reason = 'screenshot-artifact-pixel-checksum-mismatch';
} else if (proof.screenshot_nontransparent_pixel_count !== screenshotArtifact.nonTransparent) {
  reason = 'screenshot-artifact-nontransparent-count-mismatch';
} else if (proof.screenshot_distinct_color_count !== screenshotArtifact.distinctColorCount) {
  reason = 'screenshot-artifact-distinct-color-count-mismatch';
}

emit('electron_live_smoke_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_live_smoke_validation_reason', reason);
emit('electron_live_smoke_proof_symlink_status', proofPathStat.isSymbolicLink() ? 'fail' : 'pass');
emit('electron_live_smoke_proof_hardlink_status', proofPathStat.nlink > 1 ? 'fail' : 'pass');
emit('electron_live_smoke_target', proof.target);
emit('electron_live_smoke_surface_id', proof.surface_id);
emit('electron_live_smoke_proof_source', proof.proof_source);
emit('electron_live_smoke_proof_source_file_status', proofSource.status);
emit('electron_live_smoke_proof_source_size_bytes', proofSource.size);
emit('electron_live_smoke_proof_source_actual_size_bytes', proofSource.actualSize);
emit('electron_live_smoke_proof_source_file_reason', proofSource.status);
emit('electron_live_smoke_proof_source_artifact_status', proofSourceArtifactStatus);
emit('electron_live_smoke_browser_engine', proof.browser_engine);
emit('electron_live_smoke_electron_user_agent', proof.electron_user_agent);
emit('electron_live_smoke_electron_process_version', proof.electron_process_version);
emit('electron_live_smoke_chrome_process_version', proof.chrome_process_version);
emit('electron_live_smoke_width', jsonIntegerTextOrBlank(proof.width));
emit('electron_live_smoke_height', jsonIntegerTextOrBlank(proof.height));
emit('electron_live_smoke_body_html_length', jsonIntegerTextOrBlank(proof.body_html_length));
emit('electron_live_smoke_css_length', jsonIntegerTextOrBlank(proof.css_length));
emit('electron_live_smoke_app_element_present', jsonBoolTextOrBlank(proof.app_element_present));
emit('electron_live_smoke_body_text_length', jsonIntegerTextOrBlank(proof.body_text_length));
emit('electron_live_smoke_body_text_sample', proof.body_text_sample);
emit('electron_live_smoke_performance_now_available', jsonBoolTextOrBlank(proof.performance_now_available));
emit('electron_live_smoke_performance_now_delta_ms', jsonNumberTextOrBlank(proof.performance_now_delta_ms));
emit('electron_live_smoke_animation_frame_available', jsonBoolTextOrBlank(proof.animation_frame_available));
emit('electron_live_smoke_animation_frame_count', jsonIntegerTextOrBlank(proof.animation_frame_count));
emit('electron_live_smoke_css_animation_probe', jsonBoolTextOrBlank(proof.css_animation_probe));
emit('electron_live_smoke_event_dispatch_available', jsonBoolTextOrBlank(proof.event_dispatch_available));
emit('electron_live_smoke_event_dispatch_count', jsonIntegerTextOrBlank(proof.event_dispatch_count));
emit('electron_live_smoke_event_dispatch_type', proof.event_dispatch_type);
emit('electron_live_smoke_event_dispatch_detail', proof.event_dispatch_detail);
emit('electron_live_smoke_event_dispatch_error', proof.event_dispatch_error);
emit('electron_live_smoke_event_dispatch_to_paint_ms', jsonNumberTextOrBlank(proof.event_dispatch_to_paint_ms));
emit('electron_live_smoke_screenshot_path', proof.screenshot_path);
emit('electron_live_smoke_screenshot_file_status', screenshotArtifact.status);
emit('electron_live_smoke_screenshot_size_bytes', jsonIntegerTextOrBlank(proof.screenshot_png_size_bytes));
emit('electron_live_smoke_screenshot_actual_size_bytes', screenshotArtifact.actualSize);
emit('electron_live_smoke_screenshot_file_reason', screenshotArtifact.status);
emit('electron_live_smoke_screenshot_artifact_status', screenshotArtifactStatus);
emit('electron_live_smoke_screenshot_width', jsonIntegerTextOrBlank(proof.screenshot_width));
emit('electron_live_smoke_screenshot_height', jsonIntegerTextOrBlank(proof.screenshot_height));
emit('electron_live_smoke_screenshot_scale_factor', jsonNumberTextOrBlank(proof.screenshot_scale_factor));
emit('electron_live_smoke_screenshot_bitmap_byte_count', jsonIntegerTextOrBlank(proof.screenshot_bitmap_byte_count));
emit('electron_live_smoke_screenshot_pixel_checksum', jsonIntegerTextOrBlank(proof.screenshot_pixel_checksum));
emit('electron_live_smoke_screenshot_nontransparent_pixel_count', jsonIntegerTextOrBlank(proof.screenshot_nontransparent_pixel_count));
emit('electron_live_smoke_screenshot_distinct_color_count', jsonIntegerTextOrBlank(proof.screenshot_distinct_color_count));
emit('electron_live_smoke_screenshot_error', proof.screenshot_error);
emit('electron_live_smoke_blur_or_tolerance_used', jsonBoolTextOrBlank(proof.blur_or_tolerance_used));

if (reason !== 'pass') {
  process.exit(1);
}
