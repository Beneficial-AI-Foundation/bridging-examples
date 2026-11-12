// The explorer data of each example: its files by panel, its bridge methods, its atoms, and the
// declarations linked to each atom. Every file must match its recorded hash.
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { resolve, relative, basename } from 'node:path';
import { createHash } from 'node:crypto';
import { examples, root, walk } from '../scripts/examples.mjs';
import { opaqueFunctionNames, auditDeclarations, declarationEvidence, isCheckedTheorem, isAssumption } from './trust.mjs';

export const hash = text => createHash('sha256').update(text).digest('hex');
export const stages = ['rust', 'aeneas', 'spec', 'crypto', 'bridge'];

/** The names, most specific first, under which a counterpart of `atom` may be declared. A
 * method `m` of a trait implementation `Owner.Insts.Trait` also matches `Owner.m`, and `m`
 * beside `Owner`. */
function counterpartSuffixes(atom, crate) {
  const exact = atom.leanName.slice(crate.length + 1);
  if (!atom.implementation) return [exact];
  const implementation = atom.implementation.slice(crate.length + 1);
  const marker = implementation.lastIndexOf('.Insts.');
  if (marker < 0) return [exact];
  const owner = implementation.slice(0, marker);
  const method = atom.leanName.slice(atom.implementation.length + 1);
  const scope = owner.split('.').slice(0, -1);
  return [...new Set([exact, `${owner}.${method}`, [...scope, method].join('.')])];
}

/** Links each atom `f` to its specs, Crypto counterpart, bridge theorems and assumptions, by
 * attribute or by name (`crate.Spec.f_spec`, `crate.Crypto.f`, `crate.Bridge.f_bridge`,
 * `crate.Spec.f_assumption`, `crate.Bridge.f_assumption`), and to the assumptions its theorems
 * take as hypotheses. For the bridge method `example.method`, a name is tried under
 * `crate.<Method>` first, so that the method's own declaration replaces the shared one. */
export function linkAtoms(example, declarations) {
  const allNames = new Set(declarations.map(d => d.name));
  const atoms = example.items;
  for (const role of ['spec', 'crypto', 'bridge', 'assumption']) {
    for (const decl of example.declarations.filter(d => role === 'assumption' ? isAssumption(d) : d.stage === role)) {
      for (const link of decl.links.filter(l => l.role === role)) for (const target of link.targets) {
        assert(allNames.has(target), `Dangling ${role} target ${target}`);
        assert(atoms.some(a => a.leanName === target), `Non-atom ${role} target ${target}`);
      }
    }
  }
  const inferred = [];
  const namespaces = { spec: 'Spec', crypto: 'Crypto', bridge: 'Bridge' };
  const prefixes = example.method ? [`${example.crate}.${example.method}`, example.crate] : [example.crate];
  function matching(atom, role, candidates, suffix = '', namespace = namespaces[role]) {
    const eligible = candidates.filter(d => !d.links.some(l => l.role === role));
    let matches = [];
    for (const prefix of prefixes) {
      const names = counterpartSuffixes(atom, example.crate).map(name => `${prefix}.${namespace}.${name}${suffix}`);
      const exact = eligible.filter(d => d.name === names[0]);
      matches = exact.length ? exact : eligible.filter(d => names.slice(1).includes(d.name));
      if (matches.length) break;
    }
    assert(matches.length <= 1, `Ambiguous ${role} counterparts for ${atom.leanName}; add an explicit annotation`);
    for (const decl of matches) inferred.push({ atom, role, name: decl.name });
    return matches;
  }
  const assumptions = example.declarations.filter(d => isAssumption(d));
  for (const atom of atoms) {
    if (!atom.leanName) continue;
    const specs = example.declarations.filter(d => d.stage === 'spec' && !isAssumption(d));
    const taggedSpecs = specs.filter(d => d.links.some(l => l.role === 'spec' && l.targets.includes(atom.leanName)));
    atom.spec = [...taggedSpecs, ...matching(atom, 'spec', specs, '_spec')].map(d => d.name);
    const counterparts = example.declarations.filter(d => d.stage === 'crypto');
    const everyTagged = counterparts.filter(d => d.links.some(l => l.role === 'crypto' && l.targets.includes(atom.leanName)));
    // A counterpart tagged in the method's folder replaces one tagged in a shared file.
    const tagged = everyTagged.some(d => d.method) ? everyTagged.filter(d => d.method) : everyTagged;
    atom.crypto = (tagged.length ? tagged : matching(atom, 'crypto', counterparts)).map(d => d.name);
    assert(atom.crypto.length <= 1, `Ambiguous Crypto counterparts for ${atom.leanName}`);
    const bridges = example.declarations.filter(d => d.stage === 'bridge' && !isAssumption(d));
    const taggedBridges = bridges.filter(d => d.links.some(l => l.role === 'bridge' && l.targets.includes(atom.leanName)));
    atom.bridge = [...taggedBridges, ...matching(atom, 'bridge', bridges, '_bridge')].map(d => d.name);
    for (const d of example.declarations.filter(d => atom.spec.includes(d.name) || atom.bridge.includes(d.name)))
      assert(d.kind === 'theorem', `${d.name} is linked to ${atom.leanName} as a ${d.stage} but is not a theorem`);
    const taggedAssumptions = assumptions.filter(d => d.links.some(l => l.role === 'assumption' && l.targets.includes(atom.leanName)));
    atom.assumptions = [...new Set([...taggedAssumptions,
      ...matching(atom, 'assumption', assumptions, '_assumption', 'Spec'),
      ...matching(atom, 'assumption', assumptions, '_assumption', 'Bridge')].map(d => d.name))];
    const theorems = example.declarations.filter(d => atom.spec.includes(d.name) || atom.bridge.includes(d.name));
    atom.hypotheses = assumptions.filter(d => theorems.some(t => t.typeReferences?.includes(d.name))).map(d => d.name);
  }
  for (const { atom, role, name } of inferred) {
    assert(!atoms.some(other => other !== atom && other[role === 'assumption' ? 'assumptions' : role]?.includes(name)),
      `Ambiguous ${role} counterpart ${name} for ${atom.leanName}; add an explicit annotation`);
  }
  // An assumption about a trait is an assumption about each of its methods.
  for (const atom of atoms.filter(a => a.trait)) {
    const owner = atoms.find(a => a.leanName === atom.trait);
    atom.hypotheses = [...new Set([...atom.hypotheses, ...(owner?.assumptions || [])])];
  }
  // A loop and its body share the Crypto definition and the Bridge theorem of the function that
  // contains them, and a trait implementation is described by its methods.
  const inherit = (atom, sources, kinds) => {
    for (const kind of kinds) if (!atom[kind].length) atom[kind] = [...new Set(sources.flatMap(source => source[kind]))];
  };
  for (const atom of atoms.filter(a => a.parent)) inherit(atom, atoms.filter(a => a.leanName === atom.parent), ['crypto', 'bridge']);
  for (const atom of atoms.filter(a => a.category === 'trait_impls'))
    inherit(atom, atoms.filter(a => a.implementation === atom.leanName), ['spec', 'crypto', 'bridge']);
}

/** The explorer data of each example in `configs`. */
export function discover(base = root, configs = examples(base)) {
  const read = p => readFileSync(resolve(base, p), 'utf8');
  const metadata = '.lake/explorer/declarations.json';
  const declarations = existsSync(resolve(base, metadata)) ? JSON.parse(read(metadata)) : [];
  const check = existsSync(resolve(base, '.lake/explorer/check.json')) ? JSON.parse(read('.lake/explorer/check.json')) : null;
  const extractions = configs.filter(c => existsSync(resolve(base, c.translation)))
    .map(c => ({ ...JSON.parse(read(c.translation)), module: c.module }));
  const opaqueFunctions = opaqueFunctionNames(extractions, declarations);
  auditDeclarations(declarations, opaqueFunctions);
  if (declarations.length) {
    assert(check, 'Missing Lean check provenance');
    for (const [p, digest] of Object.entries(check.sha256)) assert.equal(hash(read(p)), digest, `Stale Lean metadata: ${p}`);
  }
  return configs.map(config => {
    const example = { ...config, name: config.name || config.id.replace(/(?<=[a-z])(?=[A-Z])/g, ' '),
      files: {}, declarations: [], items: [], extraction: 'missing', coverage: null,
      revision: check?.revision, dirty: check?.dirty, repository: check?.repository };
    const crateDoc = `${config.rust}/src/lib.rs`;
    example.description = existsSync(resolve(base, crateDoc)) ? read(crateDoc).match(/^\/\/! ?(.+)$/m)?.[1] || '' : '';
    function file(p, stage, support = false, method = null) {
      if (!example.files[p]) {
        const text = read(p);
        if (stage !== 'rust') assert.equal(check?.sha256[p], hash(text), `Unchecked Lean file: ${p}; run explorer/export.mjs`);
        example.files[p] = { path: p, stage, support, method, text, sha256: hash(text), language: p.endsWith('.rs') ? 'rust' : 'lean' };
      }
      return p;
    }
    for (const p of walk(resolve(base, config.rust)).filter(p => p.endsWith('.rs'))) file(relative(base, p), 'rust', !p.includes('/src/'));
    const generated = existsSync(resolve(base, config.aeneas)) ? [resolve(base, config.aeneas)] : [];
    const translationPath = config.translation;
    if (existsSync(resolve(base, translationPath))) {
      assert(generated.length, `Metadata without generated sources: ${config.id}`);
      const provenancePath = config.provenance;
      assert(existsSync(resolve(base, provenancePath)), `Missing extraction provenance: ${config.id}`);
      const extractedHashes = JSON.parse(read(provenancePath)).sha256;
      for (const [p, digest] of Object.entries(extractedHashes)) assert.equal(hash(read(p)), digest, `Stale extraction: ${p}`);
      const extractionInputs = walk(resolve(base, config.rust))
        .filter(p => p.endsWith('.rs') || p.endsWith('Cargo.toml') || p.endsWith('Cargo.lock'));
      for (const p of [...extractionInputs, ...generated, resolve(base, translationPath)]) {
        const path = relative(base, p);
        assert.equal(extractedHashes[path], hash(read(path)), `Unrecorded extraction source: ${path}`);
      }
      const extraction = JSON.parse(read(translationPath));
      assert.equal(extraction.crate, config.crate);
      example.extraction = 'available';
      example.versions = { aeneas: extraction.aeneas_version, charon: extraction.charon_version };
      example.external = ['functions', 'types', 'globals', 'trait_decls', 'trait_impls']
        .flatMap(category => (extraction[category] || []).filter(a => !a.is_local)
          .map(a => ({ name: a.lean_name, category, opaque: a.is_opaque })));
      for (const p of generated) file(relative(base, p), 'aeneas');
      const seen = new Set();
      for (const category of ['functions', 'types', 'globals', 'trait_decls', 'trait_impls']) {
        for (const atom of extraction[category] || []) {
          if (!atom.is_local || seen.has(atom.lean_name)) continue;
          seen.add(atom.lean_name);
          const decl = declarations.find(d => d.name === atom.lean_name);
          assert(decl, `Missing compiler metadata for ${atom.lean_name}; run explorer/export.mjs`);
          const rustPath = relative(base, resolve(base, config.rust, atom.source.file));
          assert(rustPath.startsWith(`${config.rust}/`), `Source outside crate: ${rustPath}`);
          file(rustPath, 'rust');
          const leanPath = `${decl.module.replaceAll('.', '/')}.lean`;
          assert(example.files[leanPath], `Wrong generated module: ${leanPath}`);
          const short = atom.lean_name.slice(config.crate.length + 1);
          const implementation = category === 'functions' ? (extraction.trait_impls || [])
            .find(impl => atom.lean_name.startsWith(`${impl.lean_name}.`))?.lean_name : null;
          example.items.push({ id: short, name: short, leanName: atom.lean_name, category, opaque: atom.is_opaque,
            implementation: implementation || null,
            parent: atom.parent_lean_name || null,
            rust: { file: rustPath, start: atom.source.begin_line, end: atom.source.end_line },
            aeneas: { file: leanPath, start: decl.start, end: decl.end }, spec: [], crypto: [], bridge: [], assumptions: [], hypotheses: [] });
        }
      }
      // Trait methods are fields of the translated trait structure. Aeneas lists the trait only,
      // so the methods come from compiler metadata and follow their trait in the atom list. A
      // method of an external trait stays an atom only when something is linked to it.
      for (const trait of extraction.trait_decls || []) {
        const rustPath = trait.is_local ? relative(base, resolve(base, config.rust, trait.source.file)) : null;
        const lines = rustPath ? read(rustPath).split('\n') : [];
        const methods = declarations.filter(d => d.projectionOf === trait.lean_name && d.type.includes('Result'))
          .sort((a, b) => a.start - b.start).map(d => {
            const method = d.name.slice(trait.lean_name.length + 1);
            const line = lines.findIndex((text, index) => index + 1 >= trait.source.begin_line &&
              index + 1 <= trait.source.end_line && new RegExp(`\\bfn\\s+${method}\\b`).test(text)) + 1;
            const short = d.name.slice(config.crate.length + 1);
            return { id: short, name: short, leanName: d.name, category: 'trait_methods', opaque: false,
              implementation: null, parent: null, trait: trait.lean_name, external: !trait.is_local,
              rust: !rustPath ? null : line ? { file: rustPath, start: line, end: line }
                : { file: rustPath, start: trait.source.begin_line, end: trait.source.end_line },
              aeneas: { file: `${d.module.replaceAll('.', '/')}.lean`, start: d.start, end: d.end },
              spec: [], crypto: [], bridge: [], assumptions: [], hypotheses: [] };
          });
        const owner = example.items.findIndex(i => i.leanName === trait.lean_name);
        example.items.splice(owner < 0 ? example.items.length : owner + 1, 0, ...methods);
      }
    } else assert(!generated.length, `Incomplete extraction: ${config.id} has Lean files but no translation.json`);
    // A handwritten file in a folder of the example belongs to that bridge method. A file beside
    // Aeneas.lean is shared by every method.
    for (const p of walk(resolve(base, config.dir)).filter(p => p.endsWith('.lean') && relative(base, p) !== config.aeneas)) {
      const filename = basename(p, '.lean');
      const stage = filename === 'Spec' ? 'spec' : filename === 'Crypto' ? 'crypto' : 'bridge';
      const [folder, ...below] = relative(resolve(base, config.dir), p).split('/');
      file(relative(base, p), stage, !['Spec', 'Crypto', 'Bridge'].includes(filename),
        below.length && folder !== 'rust' ? folder : null);
    }
    for (const d of declarations) {
      const path = `${d.module.replaceAll('.', '/')}.lean`;
      const source = example.files[path];
      if (!source || ['rust', 'aeneas'].includes(source.stage) || ['constructor', 'recursor'].includes(d.kind)) continue;
      // Skip declarations generated from a parent: same range, or Aeneas's `step` companion.
      if (declarations.some(parent => parent.name !== d.name && d.name.startsWith(parent.name + '.') && parent.module === d.module &&
        (parent.start === d.start && parent.end === d.end || d.name.endsWith('.mvcgen_spec')))) continue;
      example.declarations.push({ ...d, file: path, stage: source.stage, method: source.method, ...declarationEvidence(d, opaqueFunctions) });
    }
    example.declarations.sort((a,b) => a.file.localeCompare(b.file) || a.start-b.start || a.name.localeCompare(b.name));
    if (!example.items.length) example.items.push({ id: 'source', name: 'Source files', category: 'Rust only',
      rust: { file: Object.keys(example.files).find(p => p.endsWith('/src/lib.rs')) || Object.keys(example.files)[0], start: 1 },
      aeneas: null, spec: [], crypto: [], bridge: [], assumptions: [], hypotheses: [] });
    // The atoms and the coverage of one bridge method, or of an example without methods: the
    // links are made among the shared declarations and those of the method.
    const linked = method => {
      const view = { crate: config.crate, method, items: structuredClone(example.items),
        declarations: example.declarations.filter(d => !d.method || d.method === method) };
      linkAtoms(view, declarations);
      const assumed = i => i.assumptions.length || (i.trait && i.hypotheses.length);
      const items = view.items.filter(i => !i.external || i.spec.length || i.crypto.length || i.bridge.length || assumed(i));
      const checked = names => names.some(n => view.declarations.some(d => d.name === n && isCheckedTheorem(d)));
      // Only functions need a spec; types and traits count in neither number.
      const functions = items.filter(i => i.category === 'functions');
      return { items, coverage: example.extraction !== 'available' ? null : {
        atoms: items.length,
        functions: functions.length,
        // Linked declarations of any kind, then the atoms among them with a checked theorem. An
        // assumption is not evidence; the atoms that have one are counted on their own.
        spec: functions.filter(i => i.spec.length).length,
        checkedSpec: functions.filter(i => checked(i.spec)).length,
        crypto: items.filter(i => i.crypto.length).length,
        bridge: items.filter(i => i.bridge.length).length,
        checkedBridge: items.filter(i => checked(i.bridge)).length,
        assumed: items.filter(i => assumed(i)).length,
      } };
    };
    const folders = [...new Set(Object.values(example.files).map(f => f.method).filter(Boolean))].sort();
    assert(!folders.length || !example.files[`${config.dir}/Bridge.lean`],
      `${config.dir}/Bridge.lean is beside bridge folders; move it into a folder of its own`);
    example.methods = folders.map(id => {
      const bridge = example.files[`${config.dir}/${id}/Bridge.lean`];
      assert(bridge, `${config.dir}/${id} is a bridge folder without a Bridge.lean`);
      // The first line of the module docstring describes the method.
      return { id, name: id.replace(/(?<=[a-z])(?=[A-Z])/g, ' '),
        description: bridge.text.match(/\/-!\s*(?:#+\s*)?(.*?)\s*(?:-\/|$)/m)?.[1] || '', ...linked(id) };
    });
    // With methods, the example's own atoms and coverage are those of its first method.
    const { items, coverage } = example.methods[0] || linked(null);
    return { ...example, items, coverage };
  });
}
