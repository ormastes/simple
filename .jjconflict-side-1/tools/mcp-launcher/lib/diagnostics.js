'use strict';

const fs = require('fs');
const path = require('path');

class Diagnostics {
  constructor(serverName, repoRoot, opts = {}) {
    this.serverName = serverName;
    this.repoRoot = repoRoot;
    this.level = (opts.level || process.env.MCP_LAUNCHER_LOG || 'error').toLowerCase();
    this.logDir = path.join(repoRoot, '.simple', 'logs');
    this.logFile = path.join(this.logDir, `${serverName.replace(/-/g, '_')}_stderr.log`);
    this._fd = null;
  }

  _ensureLogDir() {
    if (!this._fd) {
      fs.mkdirSync(this.logDir, { recursive: true });
      this._fd = fs.openSync(this.logFile, 'a');
    }
    return this._fd;
  }

  _shouldLog(level) {
    const levels = { error: 0, warn: 1, info: 2, debug: 3 };
    return (levels[level] || 0) <= (levels[this.level] || 0);
  }

  log(level, msg, data) {
    if (!this._shouldLog(level)) return;
    const entry = {
      ts: new Date().toISOString(),
      server: this.serverName,
      level,
      msg,
      ...data
    };
    const line = JSON.stringify(entry) + '\n';
    try {
      fs.writeSync(this._ensureLogDir(), line);
    } catch (_) {
      // Best-effort logging
    }
  }

  error(msg, data) { this.log('error', msg, data); }
  warn(msg, data) { this.log('warn', msg, data); }
  info(msg, data) { this.log('info', msg, data); }
  debug(msg, data) { this.log('debug', msg, data); }

  /** Return the open log fd for child process stderr redirection */
  getLogFd() {
    return this._ensureLogDir();
  }

  close() {
    if (this._fd) {
      fs.closeSync(this._fd);
      this._fd = null;
    }
  }
}

module.exports = { Diagnostics };
