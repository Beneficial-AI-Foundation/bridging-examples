// Optional visual QA. Run only in an environment with permitted browser access.
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { mkdirSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const require = createRequire(import.meta.url);
const { chromium } = require(process.env.ETM_PLAYWRIGHT_MODULE || 'playwright');
const data = JSON.parse(readFileSync(new URL('manifest.json', import.meta.url)));
const output = new URL('../.tools/explorer-qa/', import.meta.url);
mkdirSync(output, { recursive: true });
const browser = await chromium.launch({ headless: true });
try {
  for (const width of [1544, 1024, 390]) {
    const page = await browser.newPage({ viewport: { width, height: 850 } });
    const errors = [], remote = [];
    page.on('pageerror', error => errors.push(error.message));
    page.on('request', request => { if (/^https?:/.test(request.url())) remote.push(request.url()); });
    await page.goto(new URL('site/index.html', import.meta.url).href);
    assert.equal(await page.locator('#focus-declaration').getAttribute('aria-pressed'), 'false');
    for (const example of data.examples) {
      await page.locator('#example-picker').selectOption(example.id);
      assert.equal(await page.locator('.pane').count(), 4);
      for (const stage of ['bridge']) await page.locator(`[data-toggle="${stage}"]`).click();
      if (example.extraction === 'missing') {
        assert.match(await page.locator('#pane-body-aeneas').innerText(), /Not extracted/);
        assert.match(await page.locator('#pane-body-crypto').innerText(), /Coverage unknown/);
      } else {
        for (const item of example.items) {
          await page.locator('#item-picker').selectOption(item.id);
          assert(await page.locator('#pane-body-aeneas .focused').count() > 0);
        }
        await page.locator('#focus-declaration').click();
        assert.equal(await page.locator('#focus-declaration').getAttribute('aria-pressed'), 'true');
        await page.locator('#focus-declaration').click();
      }
      assert(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
      await page.screenshot({ path: fileURLToPath(new URL(`${example.id}-${width}.png`, output)), fullPage: true });
      for (const stage of ['bridge']) await page.locator(`[data-toggle="${stage}"]`).click();
    }
    await page.locator('#example-picker').selectOption('modular-masking');
    for (const stage of ['bridge']) await page.locator(`[data-toggle="${stage}"]`).click();
    const masking = data.examples.find(e => e.id === 'modular-masking');
    const mask = masking.items.find(i => i.id === 'field_mask');
    for (const stage of ['rust', 'aeneas', 'crypto', 'bridge']) {
      await page.locator('#item-picker').selectOption('random_mask');
      const entry = stage === 'rust' || stage === 'aeneas' ? mask[stage]
        : masking.declarations.find(d => d.name === mask[stage][0]);
      if (!entry) continue;
      const panel = page.locator(`#pane-body-${stage}`);
      const code = panel.locator(`[data-line="${entry.selection || entry.start}"] code`);
      await code.scrollIntoViewIfNeeded();
      const scroll = await panel.evaluate(el => ({ top: el.scrollTop, left: el.scrollLeft }));
      await code.click();
      assert.equal(await page.locator('#item-picker').inputValue(), 'field_mask');
      assert.equal(new URL(await page.url()).hash.includes('item=field_mask'), true);
      assert.deepEqual(await page.locator(`#pane-body-${stage}`).evaluate(el =>
        ({ top: el.scrollTop, left: el.scrollLeft })), scroll);
      for (const other of ['rust', 'aeneas', 'crypto', 'bridge']) {
        if (Array.isArray(mask[other]) && !mask[other].length) continue;
        assert(await page.locator(`#pane-body-${other} .focused`).count() > 0);
      }
    }
    for (const stage of ['bridge']) await page.locator(`[data-toggle="${stage}"]`).click();
    if (width > 760) {
      await page.locator('#example-picker').selectOption('commitment');
      const separator = page.locator('[data-resize="rust"]');
      const before = await page.locator('.pane.rust').boundingBox();
      const handle = await separator.boundingBox();
      await page.mouse.move(handle.x + handle.width / 2, handle.y + 150);
      await page.mouse.down();
      await page.mouse.move(handle.x + 90, handle.y + 150);
      await page.mouse.up();
      assert((await page.locator('.pane.rust').boundingBox()).width > before.width);
      await separator.dblclick();
      assert(Math.abs((await page.locator('.pane.rust').boundingBox()).width - before.width) < 2);
    }
    assert.deepEqual(errors, []);
    assert.deepEqual(remote, []);
    await page.close();
  }
  console.log('Visual QA passed; screenshots in .tools/explorer-qa.');
} finally { await browser.close(); }
