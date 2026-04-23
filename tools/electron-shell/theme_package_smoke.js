#!/usr/bin/env node

const assert = require('assert');
const { loadThemePackage } = require('./theme_package');

process.env.SIMPLE_THEME = 'glass_obsidian_dark';

const pkg = loadThemePackage();
const css = pkg.css;

assert.strictEqual(pkg.requestedId, 'glass_obsidian_dark');
assert.strictEqual(pkg.id, 'aetheric_dark');
assert(css.includes('--app-background-image'), 'CSS is missing app background token');
assert(css.includes('.wm-window'), 'CSS is missing WM window styling');
assert(css.includes('.wm-titlebar'), 'CSS is missing WM titlebar styling');
assert(css.includes('--theme-icon-terminal'), 'CSS is missing terminal icon token');

const marker = '.widget-panel, .widget-card, .widget-dialog';
const count = css.split(marker).length - 1;
assert.strictEqual(count, 1, 'family defaults.css was duplicated');

console.log('Electron theme package smoke passed');
