import { execFileSync } from 'node:child_process';
import { mkdirSync, writeFileSync, renameSync } from 'node:fs';
import { resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { crates, root, read, walk } from './crates.mjs';

const id = process.argv[2];
const example = crates().find(c => c.id === id);
if (!example || process.argv.slice(3).some(x => x !== '--single-file')) throw Error('Usage: bash scripts/extract.sh <rust-folder> [--single-file]');
const run = (cmd, args, cwd = root) => execFileSync(cmd, args, { cwd, stdio: 'inherit', env: { ...process.env, CARGO_INCREMENTAL: '0' } });
run('python3', ['scripts/check-pins.py']);
mkdirSync(resolve(root, example.generated), { recursive: true });
mkdirSync(resolve(root, '.tools/llbc'), { recursive: true });
const llbc = resolve(root, `.tools/llbc/${example.crate}.llbc`);
run('charon', ['cargo', '--preset', 'aeneas', '--hide-marker-traits', '--sysroot', 'default', '--dest-file', llbc, '--', '--offline', '--locked', '--lib'], resolve(root, example.rust));
const single = process.argv.includes('--single-file');
run('aeneas', ['-backend', 'lean', '-emit-json', '-abort-on-error', '-no-progress-bar',
  '-dest', single ? resolve(root, example.generated) : root,
  ...single ? [] : ['-subdir', example.generated, '-split-files'], '-namespace', example.crate, llbc]);
if (!single) renameSync(resolve(root, 'translation.json'), resolve(root, example.generated, 'translation.json'));
const paths = [...walk(resolve(root, example.rust)).filter(p => p.endsWith('.rs') || p.endsWith('Cargo.toml') || p.endsWith('Cargo.lock')),
  ...walk(resolve(root, example.generated)).filter(p => p.endsWith('.lean') || p.endsWith('translation.json'))];
const hashes = Object.fromEntries(paths.map(p => [p.slice(root.length), createHash('sha256').update(read(p)).digest('hex')]));
writeFileSync(resolve(root, example.generated, 'provenance.json'), JSON.stringify({ crate: example.crate, sha256: hashes }, null, 2) + '\n');
