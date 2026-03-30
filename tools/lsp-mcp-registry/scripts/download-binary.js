#!/usr/bin/env node
// Postinstall script: downloads the correct platform-specific
// Simple LSP-MCP Server binary from GitHub Releases.

const https = require('https');
const fs = require('fs');
const path = require('path');
const os = require('os');

const pkg = require('../package.json');
const VERSION = pkg.version;
const REPO = 'ormastes/simple';
const BINARY_BASE = 'simple_lsp_mcp_server';

function getTriple() {
  const platform = os.platform();
  const arch = os.arch();

  if (platform === 'linux' && arch === 'x64') return 'x86_64-unknown-linux-gnu';
  if (platform === 'linux' && arch === 'arm64') return 'aarch64-unknown-linux-gnu';
  if (platform === 'darwin' && arch === 'x64') return 'x86_64-apple-darwin';
  if (platform === 'darwin' && arch === 'arm64') return 'aarch64-apple-darwin';
  if (platform === 'win32' && arch === 'x64') return 'x86_64-pc-windows-msvc';
  if (platform === 'freebsd' && arch === 'x64') return 'x86_64-unknown-freebsd';

  console.warn(`Unsupported platform: ${platform}-${arch}`);
  console.warn('You will need to build from source.');
  process.exit(0);
}

function getBinaryName() {
  return os.platform() === 'win32' ? `${BINARY_BASE}.exe` : BINARY_BASE;
}

function download(url, dest) {
  return new Promise((resolve, reject) => {
    const file = fs.createWriteStream(dest);
    https.get(url, (response) => {
      if (response.statusCode === 302 || response.statusCode === 301) {
        file.close();
        fs.unlinkSync(dest);
        return download(response.headers.location, dest).then(resolve).catch(reject);
      }
      if (response.statusCode !== 200) {
        file.close();
        fs.unlinkSync(dest);
        return reject(new Error(`HTTP ${response.statusCode}: ${url}`));
      }
      response.pipe(file);
      file.on('finish', () => { file.close(); resolve(); });
    }).on('error', (err) => {
      file.close();
      if (fs.existsSync(dest)) fs.unlinkSync(dest);
      reject(err);
    });
  });
}

async function main() {
  const triple = getTriple();
  const binaryName = getBinaryName();
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const assetName = `${BINARY_BASE}-${triple}${ext}`;

  const url = `https://github.com/${REPO}/releases/download/v${VERSION}/${assetName}`;
  const nativeDir = path.join(__dirname, '..', 'native');
  const dest = path.join(nativeDir, binaryName);

  if (fs.existsSync(dest)) {
    console.log(`${BINARY_BASE} binary already exists at ${dest}`);
    return;
  }

  console.log(`Downloading ${BINARY_BASE} v${VERSION} for ${triple}...`);
  console.log(`URL: ${url}`);

  fs.mkdirSync(nativeDir, { recursive: true });

  try {
    await download(url, dest);
    if (os.platform() !== 'win32') {
      fs.chmodSync(dest, 0o755);
    }
    console.log(`Installed ${BINARY_BASE} to ${dest}`);
  } catch (err) {
    console.warn(`Warning: Could not download binary: ${err.message}`);
    console.warn('The server will look for the binary in PATH.');
    console.warn('Build from source: https://github.com/ormastes/simple');
  }
}

main().catch((err) => {
  console.warn(`Warning: ${err.message}`);
});
