// Repository paths and the list of examples, shared by the scripts and the explorer.
import { readdirSync, existsSync, readFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { resolve, relative, basename } from 'node:path';
import { fileURLToPath } from 'node:url';

export const root = fileURLToPath(new URL('../', import.meta.url));
export const read = path => readFileSync(resolve(root, path), 'utf8');
/** The files below `dir`, except in `target`, `.lake` and `.git`. */
export const walk = dir => existsSync(dir) ? readdirSync(dir, { withFileTypes: true })
  .flatMap(e => e.isDirectory() ? (['target', '.lake', '.git'].includes(e.name) ? [] : walk(resolve(dir, e.name))) : [resolve(dir, e.name)]) : [];

// Examples from simple to complex: the order of the overview page, the example picker, and the
// README. An example that is not listed comes last, by folder name.
const order = ['Smoke', 'ProbSmoke', 'ByteMask', 'Commitment', 'ModularMasking', 'EtM', 'OneTimePad', 'LazyOracle'];
const rank = id => order.includes(id) ? order.indexOf(id) : order.length;

/** An example is a folder `BridgingExamples/<Name>/` with a Rust crate in `rust/`. Its generated Lean is
 * `Aeneas.lean`; `Spec.lean`, `Crypto.lean`, `Bridge.lean` and other Lean files are handwritten.
 * When it has several bridges, each is in a folder beside `rust/`, with its own `Bridge.lean`; a
 * folder without one holds files shared by the bridges. */
export function examples(base = root) {
  return readdirSync(resolve(base, 'BridgingExamples'), { withFileTypes: true }).filter(e => e.isDirectory())
    .filter(e => existsSync(resolve(base, 'BridgingExamples', e.name, 'rust/Cargo.toml'))).map(e => {
      const dir = `BridgingExamples/${e.name}`, manifest = resolve(base, dir, 'rust/Cargo.toml');
      const data = JSON.parse(execFileSync('cargo', ['metadata', '--no-deps', '--offline', '--format-version', '1', '--manifest-path', manifest], { encoding: 'utf8' }));
      const pkg = data.packages.find(p => resolve(p.manifest_path) === manifest);
      const explorer = pkg.metadata?.explorer;
      return { id: e.name, crate: pkg.name.replaceAll('-', '_'),
        name: explorer?.name, itemAliases: explorer?.['item-aliases'],
        dir, rust: `${dir}/rust`, aeneas: `${dir}/Aeneas.lean`, module: `BridgingExamples.${e.name}.Aeneas`,
        translation: `${dir}/translation.json`, provenance: `${dir}/provenance.json` };
    }).sort((a, b) => rank(a.id) - rank(b.id) || a.id.localeCompare(b.id));
}

/** The modules that the Lean source `text` imports. Imports are in the header: after comments,
 * `module` and `prelude`, and before the first other command. */
export function leanImports(text) {
  let code = text, previous;
  // Block comments nest, so the innermost ones go first.
  do { previous = code; code = code.replace(/\/-(?:(?!\/-|-\/)[\s\S])*-\//g, ' '); } while (code !== previous);
  const tokens = code.replace(/--.*$/gm, ' ').split(/\s+/).filter(Boolean);
  const modules = [];
  for (let i = 0; i < tokens.length; i++) {
    if (['module', 'prelude', 'public', 'meta', 'all'].includes(tokens[i])) continue;
    if (tokens[i] !== 'import') break;
    while (['public', 'meta', 'all'].includes(tokens[i + 1])) i++;
    modules.push(tokens[++i]);
  }
  return modules;
}

/** The project Lean files that the Lean file `path` imports, directly or not. `cache` keeps the
 * results between calls. */
export function projectImports(path, base = root, cache = new Map()) {
  if (!cache.has(path)) {
    cache.set(path, new Set());
    for (const module of leanImports(readFileSync(resolve(base, path), 'utf8'))) {
      const imported = `${module.replaceAll('.', '/')}.lean`;
      if (!/^(BridgingExamples|Common)\//.test(imported) || !existsSync(resolve(base, imported))) continue;
      cache.get(path).add(imported);
      for (const further of projectImports(imported, base, cache)) cache.get(path).add(further);
    }
  }
  return cache.get(path);
}

// Explorer tooling, which no statement mentions.
const tooling = ['Common/Metadata.lean', 'Common/SourceRanges.lean'];

/** The `Common/` files that the `Bridge.lean` files of the example in `dir` import, directly or
 * not, except explorer tooling. The explorer shows them as supporting files of the Bridge panel. */
export function sharedFiles(dir, base = root) {
  const cache = new Map();
  return [...new Set(walk(resolve(base, dir)).filter(p => basename(p) === 'Bridge.lean')
    .flatMap(p => [...projectImports(relative(base, p), base, cache)]))]
    .filter(p => p.startsWith('Common/') && !tooling.includes(p)).sort();
}
