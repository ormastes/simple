#!/usr/bin/env node

const fs = require('fs');
const os = require('os');
const path = require('path');

const args = process.argv.slice(2);

function valueAfter(flag) {
    const index = args.indexOf(flag);
    return index >= 0 ? args[index + 1] : '';
}

function findPlaywrightPackage() {
    const candidates = [];
    const npxRoot = path.join(os.homedir(), '.npm', '_npx');
    try {
        for (const entry of fs.readdirSync(npxRoot)) {
            candidates.push(path.join(npxRoot, entry, 'node_modules', 'playwright'));
        }
    } catch {
        // fall through to local resolution
    }
    candidates.push(path.join(process.cwd(), 'node_modules', 'playwright'));
    for (const candidate of candidates) {
        if (fs.existsSync(path.join(candidate, 'index.js'))) {
            return candidate;
        }
    }
    throw new Error('Playwright package not found. Run `npx playwright --version` first so the CLI package is cached.');
}

const root = path.resolve(__dirname, '..', '..');
const allSamples = args.includes('--all');
const sample = valueAfter('--sample') || 'site_0_google';
const htmlArg = valueAfter('--html');
const width = Number(valueAfter('--width') || '160');
const height = Number(valueAfter('--height') || '120');
const outArg = valueAfter('--out');

const htmlPath = path.resolve(root, htmlArg || `test/fixtures/famous_site_corpus/${sample}.html`);
const outPath = outArg ? path.resolve(root, outArg) : '';

if (!allSamples && !fs.existsSync(htmlPath)) {
    console.error(`HTML fixture not found: ${htmlPath}`);
    process.exit(2);
}

const { chromium } = require(path.join(findPlaywrightPackage(), 'index.js'));

async function measureSample(browser, sampleId, fixturePath) {
    const page = await browser.newPage({ viewport: { width, height } });
    await page.goto(`file://${fixturePath}`);
    const metrics = await page.evaluate(() => {
        function cleanRect(rect) {
            if (!rect) return null;
            return {
                x: rect.x,
                y: rect.y,
                width: rect.width,
                height: rect.height,
                top: rect.top,
                right: rect.right,
                bottom: rect.bottom,
                left: rect.left
            };
        }

        function textRunsByLine(element) {
            if (!element || !element.firstChild || element.firstChild.nodeType !== Node.TEXT_NODE) {
                return [];
            }
            const node = element.firstChild;
            const text = node.nodeValue || '';
            const tokens = [];
            const re = /\S+/g;
            let match;
            while ((match = re.exec(text)) !== null) {
                const range = document.createRange();
                range.setStart(node, match.index);
                range.setEnd(node, match.index + match[0].length);
                const rect = range.getBoundingClientRect();
                tokens.push({ text: match[0], start: match.index, end: match.index + match[0].length, rect: cleanRect(rect) });
            }
            const lines = [];
            for (const token of tokens) {
                const top = Math.round(token.rect.top);
                let line = lines.find(item => Math.round(item.rect.top) === top);
                if (!line) {
                    line = { text: '', start: token.start, end: token.end, rect: { ...token.rect }, tokens: [] };
                    lines.push(line);
                }
                line.tokens.push(token);
                line.end = token.end;
                line.text = text.slice(line.start, line.end).trim();
                line.rect.left = Math.min(line.rect.left, token.rect.left);
                line.rect.top = Math.min(line.rect.top, token.rect.top);
                line.rect.right = Math.max(line.rect.right, token.rect.right);
                line.rect.bottom = Math.max(line.rect.bottom, token.rect.bottom);
                line.rect.x = line.rect.left;
                line.rect.y = line.rect.top;
                line.rect.width = line.rect.right - line.rect.left;
                line.rect.height = line.rect.bottom - line.rect.top;
            }
            lines.sort((a, b) => a.rect.top - b.rect.top || a.rect.left - b.rect.left);
            return lines.map((line, index) => ({
                index,
                text: line.text,
                start: line.start,
                end: line.end,
                rect: line.rect,
                tokens: line.tokens.map(token => ({ text: token.text, start: token.start, end: token.end, rect: token.rect }))
            }));
        }

        function canvasTextMetrics(lines, fontValue) {
            const canvas = document.createElement('canvas');
            const ctx = canvas.getContext('2d');
            if (!ctx) return [];
            ctx.font = fontValue || '16px serif';
            return lines.map(line => {
                const m = ctx.measureText(line.text);
                return {
                    index: line.index,
                    text: line.text,
                    width: m.width,
                    actualBoundingBoxLeft: m.actualBoundingBoxLeft,
                    actualBoundingBoxRight: m.actualBoundingBoxRight,
                    actualBoundingBoxAscent: m.actualBoundingBoxAscent,
                    actualBoundingBoxDescent: m.actualBoundingBoxDescent,
                    fontBoundingBoxAscent: m.fontBoundingBoxAscent,
                    fontBoundingBoxDescent: m.fontBoundingBoxDescent,
                    emHeightAscent: m.emHeightAscent,
                    emHeightDescent: m.emHeightDescent
                };
            });
        }

        const body = document.body;
        const div = document.querySelector('div');
        const style = div ? getComputedStyle(div) : null;
        const bodyStyle = body ? getComputedStyle(body) : null;
        const range = document.createRange();
        if (div && div.firstChild) {
            range.selectNodeContents(div);
        }
        const textLines = textRunsByLine(div);
        const fontValue = style ? `${style.fontSize} ${style.fontFamily}` : '';
        return {
            title: document.title,
            body: bodyStyle ? {
                marginTop: bodyStyle.marginTop,
                marginRight: bodyStyle.marginRight,
                marginBottom: bodyStyle.marginBottom,
                marginLeft: bodyStyle.marginLeft,
                fontFamily: bodyStyle.fontFamily,
                fontSize: bodyStyle.fontSize,
                lineHeight: bodyStyle.lineHeight
            } : null,
            div: div && style ? {
                text: div.textContent,
                rect: cleanRect(div.getBoundingClientRect()),
                fontFamily: style.fontFamily,
                fontSize: style.fontSize,
                lineHeight: style.lineHeight,
                color: style.color,
                backgroundColor: style.backgroundColor,
                width: style.width,
                height: style.height,
                overflow: style.overflow,
                whiteSpace: style.whiteSpace
            } : null,
            textClientRects: div && div.firstChild
                ? Array.from(range.getClientRects()).map(cleanRect)
                : [],
            textLines,
            canvasTextMetrics: canvasTextMetrics(textLines, fontValue)
        };
    });
    await page.close();

    return JSON.stringify({
        sample: sampleId,
        html: path.relative(root, fixturePath),
        viewport: { width, height },
        metrics
    }, null, 2);
}

function allFixtureSamples() {
    const fixtureDir = path.resolve(root, 'test/fixtures/famous_site_corpus');
    return fs.readdirSync(fixtureDir)
        .filter(name => name.endsWith('.html'))
        .sort()
        .map(name => ({
            id: name.slice(0, -'.html'.length),
            htmlPath: path.join(fixtureDir, name),
            outPath: path.resolve(root, 'test/baselines/famous_site_corpus', name.slice(0, -'.html'.length), 'chrome_metrics.json')
        }));
}

(async () => {
    const browser = await chromium.launch();
    if (allSamples) {
        for (const entry of allFixtureSamples()) {
            const output = await measureSample(browser, entry.id, entry.htmlPath);
            fs.mkdirSync(path.dirname(entry.outPath), { recursive: true });
            fs.writeFileSync(entry.outPath, `${output}\n`);
            console.log(`wrote ${path.relative(root, entry.outPath)}`);
        }
        await browser.close();
        return;
    }

    const output = await measureSample(browser, sample, htmlPath);
    await browser.close();

    if (outPath) {
        fs.mkdirSync(path.dirname(outPath), { recursive: true });
        fs.writeFileSync(outPath, `${output}\n`);
        console.log(`wrote ${outPath}`);
    } else {
        console.log(output);
    }
})().catch(err => {
    console.error(err.stack || err.message || err);
    process.exit(1);
});
