#!/usr/bin/env node
// Postinstall script: downloads the correct platform-specific
// Simple MCP Server binary from GitHub Releases.

const https = require('https');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { execSync } = require('child_process');

const pkg = require('../package.json');
const VERSION = pkg.version;
const REPO = 'ormastes/simple';

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
  console.warn('You will need to build Simple MCP Server from source.');
  process.exit(0); // Don't fail install on unsupported platforms
}

function getBinaryName() {
  return os.platform() === 'win32' ? 'simple_mcp_server.exe' : 'simple_mcp_server';
}

function download(url, dest) {
  return new Promise((resolve, reject) => {
    const file = fs.createWriteStream(dest);
    https.get(url, (response) => {
      // Follow redirects (GitHub releases use 302)
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
  const assetName = `simple_mcp_server-${triple}${ext}`;

  const url = `https://github.com/${REPO}/releases/download/v${VERSION}/${assetName}`;
  const nativeDir = path.join(__dirname, '..', 'native');
  const dest = path.join(nativeDir, binaryName);

  // Skip if binary already exists
  if (fs.existsSync(dest)) {
    console.log(`Simple MCP Server binary already exists at ${dest}`);
    return;
  }

  console.log(`Downloading Simple MCP Server v${VERSION} for ${triple}...`);
  console.log(`URL: ${url}`);

  fs.mkdirSync(nativeDir, { recursive: true });

  try {
    await download(url, dest);
    // Make executable on Unix
    if (os.platform() !== 'win32') {
      fs.chmodSync(dest, 0o755);
    }
    console.log(`Installed Simple MCP Server to ${dest}`);
  } catch (err) {
    console.warn(`Warning: Could not download binary: ${err.message}`);
    console.warn('The MCP server will look for the binary in PATH.');
    console.warn('Build from source: https://github.com/ormastes/simple');
    // Don't fail the install
  }
}

main().catch((err) => {
  console.warn(`Warning: ${err.message}`);
});
