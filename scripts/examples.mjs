import { readdirSync, existsSync, readFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export const root = fileURLToPath(new URL('../', import.meta.url));
export const read = path => readFileSync(resolve(root, path), 'utf8');
export const walk = dir => existsSync(dir) ? readdirSync(dir, { withFileTypes: true })
  .flatMap(e => e.isDirectory() ? (['target', '.lake', '.git'].includes(e.name) ? [] : walk(resolve(dir, e.name))) : [resolve(dir, e.name)]) : [];

// Examples from simple to complex: the order of the overview page, the example picker, and the
// README. An example that is not listed comes last, by folder name.
const order = ['Smoke', 'ProbSmoke', 'ByteMask', 'Commitment', 'ModularMasking', 'EtM', 'OneTimePad', 'LazyOracle'];
const rank = id => order.includes(id) ? order.indexOf(id) : order.length;

/** An example is a folder `BridgingExamples/<Name>/` with a Rust crate in `rust/`. Its generated Lean is
 * `Aeneas.lean`; `Spec.lean`, `Crypto.lean`, `Bridge.lean` and other Lean files are handwritten. */
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
        translation: `${dir}/translation.json`, provenance: `${dir}/provenance.json`, targets: pkg.targets };
    }).sort((a, b) => rank(a.id) - rank(b.id) || a.id.localeCompare(b.id));
}
