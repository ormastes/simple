#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { launch } = require('../lib/launcher');

// Parse arguments
const args = process.argv.slice(2);
let serverName = null;
let healthCheck = false;
const passthrough = [];

for (const arg of args) {
  if (arg.startsWith('--server=')) {
    serverName = arg.slice(9);
  } else if (arg === '--health-check') {
    healthCheck = true;
  } else if (arg === '--list-servers') {
    const manifest = loadManifest();
    console.log('Available servers:');
    for (const name of Object.keys(manifest.servers)) {
      console.log(`  ${name}`);
    }
    process.exit(0);
  } else if (arg === '--help') {
    console.log('Usage: mcp-launch --server=<name> [--health-check] [-- args...]');
    console.log('       mcp-launch --list-servers');
    console.log('');
    console.log('Environment:');
    console.log('  MCP_LAUNCHER_LOG=debug|info|warn|error  Log level (default: error)');
    console.log('  SIMPLE_BINARY=<path>                    Override runtime binary');
    console.log('  T32_MCP_FRONTEND=full|cold              T32 frontend variant');
    process.exit(0);
  } else if (arg === '--') {
    // Remaining args are passthrough
    continue;
  } else {
    passthrough.push(arg);
  }
}

if (!serverName) {
  // Try to infer server name from argv[1] (symlink name)
  const basename = path.basename(process.argv[1] || '', '.js');
  const nameMap = {
    'simple-mcp-launch': 'simple-mcp',
    'simple-lsp-mcp-launch': 'simple-lsp-mcp',
    't32-mcp-launch': 't32-mcp',
    't32-lsp-mcp-launch': 't32-lsp-mcp'
  };
  serverName = nameMap[basename];
}

if (!serverName) {
  console.error('error: --server=<name> required. Use --list-servers to see available servers.');
  process.exit(1);
}

function loadManifest() {
  const manifestPath = path.join(__dirname, '..', 'servers.json');
  return JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
}

const manifest = loadManifest();
const serverConfig = manifest.servers[serverName];

if (!serverConfig) {
  console.error(`error: unknown server '${serverName}'. Available: ${Object.keys(manifest.servers).join(', ')}`);
  process.exit(1);
}

launch(serverName, serverConfig, { healthCheck, passthrough });
