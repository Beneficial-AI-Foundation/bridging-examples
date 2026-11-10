// Extract one example: Charon reads the Rust crate, Aeneas writes one Lean file, and the hashes
// of the inputs and outputs are recorded so that later edits to either side are noticed.
//   bash scripts/extract.sh <Example>
import { execFileSync } from 'node:child_process';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, renameSync, readdirSync, rmSync } from 'node:fs';
import { resolve, relative } from 'node:path';
import { createHash } from 'node:crypto';
import { examples, root, read, walk } from './examples.mjs';

const example = examples().find(e => e.id === process.argv[2]);
if (!example || process.argv.length !== 3) throw Error('Usage: bash scripts/extract.sh <Example>   (a folder of BridgingExamples/)');
const run = (cmd, args, cwd = root) => execFileSync(cmd, args, { cwd, stdio: 'inherit', env: { ...process.env, CARGO_INCREMENTAL: '0' } });
run('python3', ['scripts/check-pins.py']);
mkdirSync(resolve(root, '.tools/llbc'), { recursive: true });
const llbc = resolve(root, `.tools/llbc/${example.crate}.llbc`);
run('charon', ['cargo', '--preset', 'aeneas', '--hide-marker-traits', '--sysroot', 'default', '--dest-file', llbc, '--', '--offline', '--locked', '--lib'], resolve(root, example.rust));
// Aeneas names its output after the crate; it is written aside and moved to Aeneas.lean.
const out = resolve(root, `.tools/aeneas-out/${example.id}`);
rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });
run('aeneas', ['-backend', 'lean', '-emit-json', '-abort-on-error', '-no-progress-bar', '-dest', out, '-namespace', example.crate, llbc]);
const generated = readdirSync(out).filter(name => name.endsWith('.lean'));
assert.equal(generated.length, 1, `Expected one generated Lean file, found: ${generated}`);
renameSync(resolve(out, generated[0]), resolve(root, example.aeneas));
renameSync(resolve(out, 'translation.json'), resolve(root, example.translation));
rmSync(out, { recursive: true, force: true });
const paths = [...walk(resolve(root, example.rust)).filter(p => p.endsWith('.rs') || p.endsWith('Cargo.toml') || p.endsWith('Cargo.lock'))
  .map(p => relative(root, p)), example.aeneas, example.translation];
const hashes = Object.fromEntries(paths.map(p => [p, createHash('sha256').update(read(p)).digest('hex')]));
writeFileSync(resolve(root, example.provenance), JSON.stringify({ crate: example.crate, sha256: hashes }, null, 2) + '\n');
