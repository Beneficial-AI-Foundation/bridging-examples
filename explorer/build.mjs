// Write the explorer page and its manifest to explorer/site/, or with --check compare the page.
// Run after explorer/export.mjs and explorer/verso.mjs.
import assert from 'node:assert/strict';
import { writeFileSync, existsSync, mkdirSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { discover } from './discover.mjs';
import { read, root } from '../scripts/examples.mjs';
import { renderHtml } from './render.mjs';

/** The page data: the examples, the Lean toolchain and the VCVio references. */
export function buildData() {
  const vcvio = JSON.parse(read('lake-manifest.json')).packages.find(p => p.name === 'VCVio');
  return { defaultExample: null, examples: discover(), lean: read('lean-toolchain').trim(),
    references: vcvio ? ['VCVio/OracleComp/ProbComp.lean', 'VCVio/EvalDist/EvalDistEq.lean',
      'VCVio/OracleComp/QueryTracking/RandomOracle/EagerTable.lean']
      .map(path => ({ path, url: `${vcvio.url.replace(/\.git$/, '')}/blob/${vcvio.rev}/${path}` })) : [] };
}

/** Verso's rendering of the Lean files, where `explorer/verso.mjs` has produced it for the current
 * source. A file without it, or changed since, keeps the explorer's plain rendering. */
export function buildVerso(data) {
  const dir = '.lake/explorer/verso/';
  const present = path => existsSync(resolve(root, dir + path));
  if (!present('assets/highlighting.js')) return null;
  const files = {}, docs = {};
  for (const example of data.examples) for (const file of Object.values(example.files)) {
    const cache = `${file.path.slice(0, -'.lean'.length).replaceAll('/', '.')}.json`;
    if (file.language !== 'lean' || files[file.path] || !present(cache)) continue;
    const rendered = JSON.parse(read(dir + cache));
    if (rendered.sha256 !== file.sha256) continue;
    files[file.path] = rendered.lines;
    Object.assign(docs, rendered.docs);
  }
  if (!Object.keys(files).length) return null;
  const asset = name => read(`${dir}assets/${name}`);
  // Verso binds its hovers once, when the page loads. The explorer redraws its panels, so the
  // start of Verso's script becomes a function that the explorer calls after each draw.
  const start = 'window.onload = async () => {', highlighting = asset('highlighting.js');
  assert(highlighting.includes(start), 'Verso changed how its hover script starts');
  const script = [asset('popper.js'), asset('tippy.js'), asset('marked.js'),
    highlighting.replace(start, 'window.versoInit = async () => {')].join('\n;\n');
  assert(!/<\/script/i.test(script), 'A Verso script would end the inline script early');
  return { files, docs, style: asset('highlighting.css') + asset('tippy-border.css'), script };
}

export const buildHtml = () => { const data = buildData(); return renderHtml(data, buildVerso(data)); };

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const data = buildData(), verso = buildVerso(data);
  const html = renderHtml(data, verso);
  if (process.argv.includes('--check')) assert.equal(read('explorer/site/index.html'), html, 'Explorer is stale');
  else {
    mkdirSync(new URL('site/', import.meta.url), { recursive: true });
    writeFileSync(new URL('site/index.html', import.meta.url), html);
    writeFileSync(new URL('site/manifest.json', import.meta.url), JSON.stringify(data, null, 2) + '\n');
  }
  console.log(`${data.examples.length} examples; extraction, metadata, and source hashes agree.` +
    (verso ? ` Verso renders ${Object.keys(verso.files).length} Lean files.` : ''));
}
