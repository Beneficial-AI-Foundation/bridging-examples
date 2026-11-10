// Render the Lean files shown in the explorer with Verso. SubVerso exports each module (tokens,
// hovers, proof states), Verso turns the export into HTML, and the HTML is cut into source lines.
// The result is cached in .lake/explorer/verso/<Module>.json. A file is rendered again when it,
// a project file it imports, the renderer, or the pinned Verso changes. Run it after
// explorer/export.mjs, which builds the modules.
import { execFileSync, spawn } from 'node:child_process';
import { mkdirSync, writeFileSync, renameSync, existsSync, rmSync } from 'node:fs';
import { resolve, relative } from 'node:path';
import { createHash } from 'node:crypto';
import { examples, root, read, walk } from '../scripts/examples.mjs';
import { splitLines, guillemets } from './verso/lines.mjs';

const hash = text => createHash('sha256').update(text).digest('hex');
const out = resolve(root, '.lake/explorer/verso');
const pinned = JSON.parse(read('lake-manifest.json')).packages.find(p => p.name === 'verso');
if (!pinned) { console.log('Verso is not a dependency; the explorer keeps its plain rendering.'); process.exit(0); }
const version = hash(read('explorer/verso/lines.mjs') + read('explorer/verso/Render.lean') + pinned.rev);

const moduleOf = path => path.slice(0, -'.lean'.length).replaceAll('/', '.');
const cacheOf = path => resolve(out, `${moduleOf(path)}.json`);
const files = examples().flatMap(e => walk(resolve(root, e.dir))).filter(p => p.endsWith('.lean'))
  .map(p => relative(root, p)).sort();

// Hovers show the types and docstrings of imported declarations, so a render also depends on the
// project files the module imports, directly or not.
const imports = new Map();
function importsOf(path) {
  if (!imports.has(path)) {
    imports.set(path, new Set());
    for (const [, module] of read(path).matchAll(/^(?:public\s+)?(?:meta\s+)?import\s+(\S+)/gm)) {
      const imported = `${module.replaceAll('.', '/')}.lean`;
      if (!/^(BridgingExamples|Common)\//.test(imported) || !existsSync(resolve(root, imported))) continue;
      imports.get(path).add(imported);
      for (const further of importsOf(imported)) imports.get(path).add(further);
    }
  }
  return imports.get(path);
}
const inputsOf = path => hash([path, ...[...importsOf(path)].sort()].map(p => hash(read(p))).join(''));
const fresh = path => {
  if (!existsSync(cacheOf(path))) return false;
  const cached = JSON.parse(read(cacheOf(path)));
  return cached.sha256 === hash(read(path)) && cached.inputs === inputsOf(path) && cached.version === version;
};
const stale = files.filter(p => !fresh(p));
const assetsDir = resolve(out, 'assets');
if (!stale.length && existsSync(resolve(assetsDir, 'highlighting.js'))) {
  console.log(`${files.length} Lean files rendered by Verso; all up to date.`);
  process.exit(0);
}

// Each run works in its own folder, so two runs at once cannot read each other's partial files.
const tmp = resolve(out, `tmp-${process.pid}`);
mkdirSync(tmp, { recursive: true });
execFileSync('lake', ['build', 'subverso-extract-mod', 'Verso.Code.Highlighted', 'Verso.Code.Highlighted.WebAssets', 'SubVerso.Module'],
  { cwd: root, stdio: ['ignore', 'ignore', 'inherit'] });
const extract = resolve(root, '.lake/packages/subverso/.lake/build/bin/subverso-extract-mod');
const run = (command, args) => new Promise((done, fail) => {
  const child = spawn(command, args, { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });
  let log = '';
  child.stdout.on('data', chunk => log += chunk);
  child.stderr.on('data', chunk => log += chunk);
  child.on('close', code => code === 0 ? done() : fail(new Error(`${command} ${args.join(' ')} failed:\n${log.slice(-3000)}`)));
});

try {
  // 1. SubVerso elaborates each module again to record its tokens, hovers and proof states.
  const sources = new Map(stale.map(p => [p, read(p)])), keys = new Map(stale.map(p => [p, inputsOf(p)]));
  const queue = [...stale];
  await Promise.all(Array.from({ length: Number(process.env.VERSO_JOBS || 2) }, async () => {
    for (let path; (path = queue.shift());) {
      const started = Date.now();
      await run('lake', ['env', extract, moduleOf(path), resolve(tmp, `${moduleOf(path)}.sv.json`)]);
      console.log(`${moduleOf(path)}: exported in ${Math.round((Date.now() - started) / 1000)} s`);
    }
  }));

  // 2. One Lean process renders every export with Verso and writes Verso's stylesheet and scripts.
  execFileSync('lake', ['env', 'lean', '--run', 'explorer/verso/Render.lean', '--assets', assetsDir,
    ...stale.flatMap(p => [resolve(tmp, `${moduleOf(p)}.sv.json`), resolve(tmp, `${moduleOf(p)}.html.json`)])],
    { cwd: root, stdio: ['ignore', 'ignore', 'inherit'] });

  // 3. Cut the HTML into source lines. A file that changed while it was being rendered is left
  // for the next run.
  let written = 0;
  for (const path of stale) {
    const module = moduleOf(path), source = sources.get(path);
    if (read(path) !== source || inputsOf(path) !== keys.get(path)) continue;
    const rendered = JSON.parse(read(resolve(tmp, `${module}.html.json`)));
    const lines = splitLines(rendered.items.join(''), module).map(guillemets);
    const expected = source.split('\n').length;
    if (lines.length !== expected) throw Error(`${path}: Verso rendered ${lines.length} lines, the source has ${expected}`);
    const docs = Object.fromEntries(Object.entries(rendered.docs).map(([id, html]) => [`${module}:${id}`, html]));
    const partial = resolve(tmp, `${module}.json`);
    writeFileSync(partial, JSON.stringify({ sha256: hash(source), inputs: keys.get(path), version, lines, docs }));
    renameSync(partial, cacheOf(path));
    written++;
  }
  console.log(`${files.length} Lean files rendered by Verso; ${written} rendered now.`);
} finally {
  rmSync(tmp, { recursive: true, force: true });
}
