const fs = require('fs');
const path = require('path');

const repoRoot = path.resolve(__dirname, '..', '..');
const THEME_REGISTRY_PATH = 'config/themes/theme.sdn';
const packageCache = new Map();

const FALLBACK_ICON_ROLES = [
    'terminal', 'browser', 'file_manager', 'finder', 'editor', 'calculator', 'settings', 'generic_app',
    'close', 'minimize', 'maximize', 'restore', 'fullscreen', 'launcher', 'search', 'running_indicator', 'fallback_app', 'fallback_file',
    'back', 'forward', 'refresh', 'home', 'new_window', 'command_palette',
    'folder', 'file', 'document', 'image', 'media', 'archive', 'executable', 'unknown',
    'info', 'success', 'warning', 'error'
];

function readTextIfExists(filePath) {
    try {
        const resolved = resolveRepoPath(filePath);
        if (!resolved || !fs.existsSync(resolved)) return '';
        return fs.readFileSync(resolved, 'utf8');
    } catch {
        return '';
    }
}

function resolveRepoPath(rawPath) {
    if (!rawPath) return '';
    return path.isAbsolute(rawPath) ? rawPath : path.join(repoRoot, rawPath);
}

function stripValue(value) {
    let out = String(value || '').trim();
    if (out.length >= 2 && out.startsWith('"') && out.endsWith('"')) {
        out = out.slice(1, -1);
    }
    return out;
}

function rootValue(sdn, key) {
    const prefix = `${key}:`;
    for (const line of String(sdn || '').split(/\r?\n/)) {
        const trimmed = line.trim();
        if (trimmed.startsWith(prefix)) return stripValue(trimmed.slice(prefix.length));
    }
    return '';
}

function sectionValue(sdn, section, key) {
    let current = '';
    const sectionHeader = `${section}:`;
    const prefix = `${key}:`;
    for (const line of String(sdn || '').split(/\r?\n/)) {
        const trimmed = line.trim();
        if (!trimmed || trimmed.startsWith('#')) continue;
        if (trimmed === sectionHeader) {
            current = section;
            continue;
        }
        if (!line.startsWith(' ') && trimmed.endsWith(':')) {
            current = trimmed.slice(0, -1);
            continue;
        }
        if (current === section && trimmed.startsWith(prefix)) {
            return stripValue(trimmed.slice(prefix.length));
        }
    }
    return '';
}

function sectionItems(sdn, section) {
    const items = [];
    let current = '';
    const sectionHeader = `${section}:`;
    for (const line of String(sdn || '').split(/\r?\n/)) {
        const trimmed = line.trim();
        if (!trimmed || trimmed.startsWith('#')) continue;
        if (trimmed === sectionHeader) {
            current = section;
            continue;
        }
        if (!line.startsWith(' ') && trimmed.endsWith(':')) {
            current = trimmed.slice(0, -1);
            continue;
        }
        if (current === section && trimmed.startsWith('- ')) {
            items.push(stripValue(trimmed.slice(2)));
        }
    }
    return items;
}

function defaultThemeId() {
    return rootValue(readTextIfExists(THEME_REGISTRY_PATH), 'default_theme') || 'aetheric_dark';
}

function resolveThemeAlias(themeId) {
    const requested = themeId || defaultThemeId();
    const registry = readTextIfExists(THEME_REGISTRY_PATH);
    return sectionValue(registry, 'aliases', requested) || requested;
}

function requiredIconRoles(registry) {
    const roles = sectionItems(registry, 'required_icons');
    return roles.length > 0 ? roles : FALLBACK_ICON_ROLES;
}

function iconIdForRole(iconSdn, role) {
    for (const section of ['apps', 'system', 'navigation', 'content', 'status']) {
        const value = sectionValue(iconSdn, section, role);
        if (value) return value;
    }
    return '';
}

function iconsToCss(iconSdn, roles) {
    const lines = [':root {'];
    for (const role of roles) {
        const key = role.replace(/_/g, '-');
        lines.push(`  --theme-icon-${key}: "${iconIdForRole(iconSdn, role)}";`);
        lines.push(`  --theme-icon-${key}-label: "${sectionValue(iconSdn, 'labels', role)}";`);
        lines.push(`  --theme-icon-${key}-color: ${sectionValue(iconSdn, 'colors', role)};`);
        lines.push(`  --theme-icon-${key}-size: "${sectionValue(iconSdn, 'sizes', role)}";`);
    }
    lines.push('}');
    return lines.join('\n');
}

function loadFamilyWidgetCss(widgets, familyDir) {
    const chunks = [readTextIfExists(path.join(familyDir || '', 'defaults.css'))];
    for (const widget of widgets) {
        chunks.push(readTextIfExists(path.join(familyDir || '', `${widget}.css`)));
    }
    return chunks.filter(Boolean).join('\n');
}

function loadThemeWidgetCss(widgets, themeDir) {
    const chunks = [];
    for (const widget of widgets) {
        chunks.push(readTextIfExists(path.join(themeDir || '', `${widget}.css`)));
    }
    return chunks.filter(Boolean).join('\n');
}

function loadThemePackage(themeId = '') {
    const requestedId = themeId || process.env.SIMPLE_THEME || defaultThemeId();
    const resolvedId = resolveThemeAlias(requestedId);
    const cacheKey = `${requestedId}::${resolvedId}`;
    if (packageCache.has(cacheKey)) return packageCache.get(cacheKey);

    const registry = readTextIfExists(THEME_REGISTRY_PATH);
    const themePath = sectionValue(registry, 'themes', resolvedId) || `config/themes/${resolvedId}/theme.sdn`;
    const themeSdn = readTextIfExists(themePath);
    const familyId = rootValue(themeSdn, 'family');
    const familyPath = sectionValue(registry, 'families', familyId) || `config/themes/families/${familyId}/theme.sdn`;
    const familySdn = readTextIfExists(familyPath);
    const requiredWidgets = sectionItems(registry, 'required_widgets');
    const shapeCss = readTextIfExists(rootValue(familySdn, 'shape_css'));
    const familyWidgetCss = loadFamilyWidgetCss(requiredWidgets, rootValue(familySdn, 'widget_css_dir'));
    const baseCss = readTextIfExists(rootValue(themeSdn, 'base_css'));
    const themeWidgetCss = loadThemeWidgetCss(requiredWidgets, rootValue(themeSdn, 'widget_css_dir'));
    const iconSdn = readTextIfExists(rootValue(familySdn, 'icons'));
    const iconCss = iconsToCss(iconSdn, requiredIconRoles(registry));

    const pkg = {
        id: resolvedId,
        requestedId,
        displayName: rootValue(themeSdn, 'display_name') || resolvedId,
        familyId,
        registryPath: THEME_REGISTRY_PATH,
        themePath,
        familyPath,
        shapeCss,
        familyWidgetCss,
        baseCss,
        themeWidgetCss,
        widgetCss: `${familyWidgetCss}\n${themeWidgetCss}`,
        iconCss,
        css: [shapeCss, familyWidgetCss, baseCss, themeWidgetCss, iconCss].filter(Boolean).join('\n') + '\n'
    };
    packageCache.set(cacheKey, pkg);
    return pkg;
}

module.exports = {
    defaultThemeId,
    resolveThemeAlias,
    loadThemePackage,
    _test: {
        rootValue,
        sectionValue,
        sectionItems,
        readTextIfExists,
        packageCache
    }
};
