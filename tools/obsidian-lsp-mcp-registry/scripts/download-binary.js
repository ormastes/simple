#!/usr/bin/env node
// Postinstall script: downloads the correct platform-specific
// Simple bootstrap package (.spk) from GitHub Releases.
// The .spk contains the Simple runtime binary + source tree,
// which is needed to run MCP servers.

const https = require('https');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { execSync } = require('child_process');

const pkg = require('../package.json');
const VERSION = pkg.runtimeVersion || pkg.version;
const REPO = 'ormastes/simple';

function getPlatform() {
  const platform = os.platform();
  const arch = os.arch();

  if (platform === 'linux' && arch === 'x64') return 'linux-x86_64';
  if (platform === 'linux' && arch === 'arm64') return 'linux-aarch64';
  if (platform === 'darwin' && arch === 'x64') return 'darwin-x86_64';
  if (platform === 'darwin' && arch === 'arm64') return 'darwin-arm64';
  if (platform === 'win32' && arch === 'x64') return 'windows-x86_64';
  if (platform === 'win32' && arch === 'arm64') return 'windows-aarch64';
  if (platform === 'freebsd' && arch === 'x64') return 'freebsd-x86_64';

  console.warn(`Unsupported platform: ${platform}-${arch}`);
  console.warn('You will need to build Simple from source.');
  process.exit(0); // Don't fail install on unsupported platforms
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
  const platform = getPlatform();
  const nativeDir = path.join(__dirname, '..', 'native');
  const marker = path.join(nativeDir, '.installed');

  // Skip if already installed
  if (fs.existsSync(marker)) {
    const installed = fs.readFileSync(marker, 'utf8').trim();
    if (installed === `${VERSION}-${platform}`) {
      console.log('Simple runtime already installed.');
      return;
    }
  }

  const assetName = `simple-bootstrap-${VERSION}-${platform}.spk`;
  const url = `https://github.com/${REPO}/releases/download/v${VERSION}/${assetName}`;
  const dest = path.join(nativeDir, assetName);

  console.log(`Downloading Simple runtime v${VERSION} for ${platform}...`);
  console.log(`URL: ${url}`);

  // Clean previous install
  if (fs.existsSync(nativeDir)) {
    fs.rmSync(nativeDir, { recursive: true, force: true });
  }
  fs.mkdirSync(nativeDir, { recursive: true });

  try {
    await download(url, dest);

    // Extract — tar is available on Windows 10+, macOS, Linux
    console.log('Extracting...');
    execSync(`tar xzf "${assetName}"`, { cwd: nativeDir, stdio: 'inherit' });

    // Remove archive after extraction
    fs.unlinkSync(dest);

    // Make binary executable on Unix
    const ext = os.platform() === 'win32' ? '.exe' : '';
    const entries = fs.readdirSync(nativeDir).filter(e => e.startsWith('simple-bootstrap-'));
    if (entries.length > 0) {
      const binary = path.join(nativeDir, entries[0], 'bin', `simple${ext}`);
      if (fs.existsSync(binary) && os.platform() !== 'win32') {
        fs.chmodSync(binary, 0o755);
      }
    }

    fs.writeFileSync(marker, `${VERSION}-${platform}\n`);
    console.log(`Installed Simple runtime to ${nativeDir}`);
  } catch (err) {
    console.warn(`Warning: Could not download runtime: ${err.message}`);
    console.warn('The MCP server will look for "simple" in PATH.');
    console.warn('Build from source: https://github.com/ormastes/simple');
    // Don't fail the install
  }
}

main().catch((err) => {
  console.warn(`Warning: ${err.message}`);
});
