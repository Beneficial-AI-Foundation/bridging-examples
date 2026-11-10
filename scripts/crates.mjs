import { readdirSync, existsSync, readFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { resolve, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

export const root = fileURLToPath(new URL('../', import.meta.url));
export const read = path => readFileSync(resolve(root, path), 'utf8');
export const walk = dir => existsSync(dir) ? readdirSync(dir, { withFileTypes: true })
  .flatMap(e => e.isDirectory() ? (['target', '.lake', '.git'].includes(e.name) ? [] : walk(resolve(dir, e.name))) : [resolve(dir, e.name)]) : [];

// Examples from simple to complex: the order of the overview page, the example picker, and the
// README. A crate that is not listed comes last, by folder name.
const order = ['smoke', 'prob-smoke', 'byte-mask', 'commitment', 'modular-masking', 'etm', 'one-time-pad', 'lazy-oracle'];
const rank = id => order.includes(id) ? order.indexOf(id) : order.length;

export function crates(base = root) {
  return readdirSync(resolve(base, 'rust'), { withFileTypes: true }).filter(e => e.isDirectory())
    .filter(e => existsSync(resolve(base, 'rust', e.name, 'Cargo.toml'))).map(e => {
      const manifest = resolve(base, 'rust', e.name, 'Cargo.toml');
      const data = JSON.parse(execFileSync('cargo', ['metadata', '--no-deps', '--offline', '--format-version', '1', '--manifest-path', manifest], { encoding: 'utf8' }));
      const pkg = data.packages.find(p => resolve(p.manifest_path) === manifest);
      const canonical = e.name.split(/[-_]/).map(x => x[0].toUpperCase() + x.slice(1)).join('');
      const dirs = existsSync(resolve(base, 'Generated')) ? readdirSync(resolve(base, 'Generated')) : [];
      const module = dirs.find(d => d.toLowerCase() === canonical.toLowerCase()) || canonical;
      const explorer = pkg.metadata?.explorer;
      return { id: e.name, crate: pkg.name.replaceAll('-', '_'), module,
        name: explorer?.name, itemAliases: explorer?.['item-aliases'],
        rust: relative(base, resolve(base, 'rust', e.name)), generated: `Generated/${module}`,
        handwritten: `BridgingExamples/${module}`, targets: pkg.targets };
    }).sort((a, b) => rank(a.id) - rank(b.id) || a.id.localeCompare(b.id));
}
