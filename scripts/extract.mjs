// Extract examples: Charon reads each Rust crate, Aeneas writes one Lean file, and the hashes
// of the inputs and outputs are recorded so that later edits to either side are noticed.
//   bash scripts/extract.sh <Example>...            extract and record provenance
//   bash scripts/extract.sh --check [<Example>...]  extract again and compare with the files
// Without names, --check covers every example with a translation.json.
import { execFileSync } from 'node:child_process';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, renameSync, readdirSync, rmSync, existsSync } from 'node:fs';
import { resolve, relative } from 'node:path';
import { createHash } from 'node:crypto';
import { examples, root, read, walk } from './examples.mjs';

const usage = 'Usage: bash scripts/extract.sh [--check] <Example>...   (folders of BridgingExamples/)';
const check = process.argv[2] === '--check';
const names = process.argv.slice(check ? 3 : 2);
const all = examples();
const selected = check && !names.length ? all.filter(e => existsSync(resolve(root, e.translation)))
  : names.map(name => all.find(e => e.id === name) ?? assert.fail(`${usage}\nUnknown example: ${name}`));
assert(selected.length, usage);
const run = (cmd, args, cwd = root) => execFileSync(cmd, args, { cwd, stdio: 'inherit', env: { ...process.env, CARGO_INCREMENTAL: '0' } });
const hashes = paths => Object.fromEntries(paths.map(p => [p, createHash('sha256').update(read(p)).digest('hex')]));
// The pin check reads the Lake checkouts, which the cache fetch creates in a fresh clone.
run('lake', ['exe', 'cache', 'get']);
run('python3', ['scripts/check-pins.py']);
mkdirSync(resolve(root, '.tools/llbc'), { recursive: true });
for (const example of selected) {
  const inputs = walk(resolve(root, example.rust))
    .filter(p => p.endsWith('.rs') || p.endsWith('Cargo.toml') || p.endsWith('Cargo.lock')).map(p => relative(root, p));
  const sources = hashes(inputs);
  const llbc = resolve(root, `.tools/llbc/${example.crate}.llbc`);
  run('charon', ['cargo', '--preset', 'aeneas', '--hide-marker-traits', '--sysroot', 'default', '--dest-file', llbc, '--', '--offline', '--locked', '--lib'], resolve(root, example.rust));
  // Aeneas names its output after the crate; it is written aside and moved to Aeneas.lean.
  const out = resolve(root, `.tools/aeneas-out/${example.id}`);
  rmSync(out, { recursive: true, force: true });
  mkdirSync(out, { recursive: true });
  run('aeneas', ['-backend', 'lean', '-emit-json', '-abort-on-error', '-no-progress-bar', '-dest', out, '-namespace', example.crate, llbc]);
  assert.deepEqual(hashes(inputs), sources, `${example.id}: the Rust sources changed during extraction; extract again`);
  const generated = readdirSync(out).filter(name => name.endsWith('.lean'));
  assert.equal(generated.length, 1, `Expected one generated Lean file, found: ${generated}`);
  const outputs = { [example.aeneas]: resolve(out, generated[0]), [example.translation]: resolve(out, 'translation.json') };
  const provenance = { crate: example.crate, sha256: { ...sources,
    ...Object.fromEntries(Object.entries(outputs).map(([path, file]) => [path, createHash('sha256').update(read(file)).digest('hex')])) } };
  if (check) {
    for (const [path, file] of Object.entries(outputs)) {
      assert(existsSync(resolve(root, path)) && read(file) === read(path), `${path} differs from a fresh extraction; extract ${example.id} again`);
    }
    assert.deepEqual(JSON.parse(read(example.provenance)), provenance, `${example.provenance} differs from a fresh extraction`);
  } else {
    for (const [path, file] of Object.entries(outputs)) renameSync(file, resolve(root, path));
    writeFileSync(resolve(root, example.provenance), JSON.stringify(provenance, null, 2) + '\n');
  }
  rmSync(out, { recursive: true, force: true });
}
if (check) console.log(`${selected.length} examples match a fresh extraction.`);
