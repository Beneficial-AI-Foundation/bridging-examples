import { execFileSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import assert from 'node:assert/strict';
import { resolve, relative } from 'node:path';
import { createHash } from 'node:crypto';
import { root, walk, read } from '../scripts/examples.mjs';
import { opaqueFunctionNames, auditDeclarations, isAssumption } from './trust.mjs';

const sources = ['BridgingExamples', 'Common'].flatMap(dir => walk(resolve(root, dir))).filter(p => p.endsWith('.lean'))
  .map(p => relative(root, p)).sort();
const modules = sources.map(p => p.slice(0, -5).replaceAll('/', '.'));
const translationFiles = walk(resolve(root, 'BridgingExamples')).filter(p => p.endsWith('/translation.json'))
  .map(p => relative(root, p));
const tracked = [...sources, ...translationFiles, 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'];
const sha256 = Object.fromEntries(tracked.map(p => [p, createHash('sha256').update(read(p)).digest('hex')]));
execFileSync('lake', ['build', ...modules], { cwd: root, stdio: 'inherit' });
mkdirSync(resolve(root, '.lake/explorer'), { recursive: true });
const driver = [...modules.map(m => `import ${m}`),
  'set_option maxHeartbeats 0',
  '#export_explorer ".lake/explorer/declarations.json"',
  // Proof ranges are parsed from source text; Aeneas's triple notation is scoped.
  'open Aeneas Aeneas.Std in',
  '#export_proof_ranges ".lake/explorer/declarations.json"', ''].join('\n');
writeFileSync(resolve(root, '.lake/explorer/Export.lean'), driver);
execFileSync('lake', ['env', 'lean', '.lake/explorer/Export.lean'], { cwd: root, stdio: 'inherit' });
const declarations = JSON.parse(read('.lake/explorer/declarations.json')).sort((a, b) => a.name.localeCompare(b.name));
const extractions = translationFiles.map(p => ({ ...JSON.parse(read(p)),
  module: `${p.slice(0, -'/translation.json'.length).replaceAll('/', '.')}.Aeneas` }));
const opaqueFunctions = opaqueFunctionNames(extractions, declarations);
auditDeclarations(declarations, opaqueFunctions);
writeFileSync(resolve(root, '.lake/explorer/declarations.json'), JSON.stringify(declarations, null, 2) + '\n');
for (const [p, digest] of Object.entries(sha256)) {
  assert.equal(createHash('sha256').update(read(p)).digest('hex'), digest, `Source changed during checking: ${p}; rerun export`);
}
// Source links need a GitHub remote and a revision; without them the explorer omits the links.
const git = (...args) => {
  try { return execFileSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim(); }
  catch { return null; }
};
let repository = git('remote', 'get-url', 'origin')?.replace(/^git@github.com:/, 'https://github.com/').replace(/\.git$/, '');
if (!repository?.startsWith('https://github.com/')) repository = null;
const status = git('status', '--porcelain');
writeFileSync(resolve(root, '.lake/explorer/check.json'), JSON.stringify({ sha256,
  opaqueFunctions: [...opaqueFunctions].sort(),
  assumptions: declarations.filter(isAssumption).map(d => d.name).sort(),
  repository,
  revision: git('rev-parse', 'HEAD'),
  dirty: status === null ? null : status.length > 0,
}, null, 2) + '\n');
