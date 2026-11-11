// The axiom audit and the evidence labels. The allowed axioms are Lean's foundational axioms and
// the functions Aeneas left opaque.
import assert from 'node:assert/strict';

const foundationalAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);

/** The functions Aeneas left opaque, each an axiom of its example's Aeneas module. */
export function opaqueFunctionNames(extractions, declarations) {
  const byName = new Map(declarations.map(d => [d.name, d]));
  const names = new Set();
  for (const { module, functions = [] } of extractions) {
    for (const atom of functions.filter(f => f.is_opaque)) {
      const d = byName.get(atom.lean_name);
      assert(d, `Missing opaque function metadata: ${atom.lean_name}`);
      assert(d.module === module, `Wrong opaque function module: ${d.name}`);
      assert(d.kind === 'axiom' && d.isProof === false && d.isFunction === true,
        `Opaque boundary must be a function symbol, not a proof: ${d.name}`);
      names.add(d.name);
    }
  }
  return names;
}

/** An assumption is a proposition-valued definition in a Spec or Bridge module, named
 * `*_assumption` or tagged `assumption_for`. Spec and Bridge theorems take assumptions as
 * hypotheses: deterministic contracts in Spec, distributions in Bridge. */
export function isAssumption(d) {
  const tagged = d.links?.some(l => l.role === 'assumption');
  const named = d.name.endsWith('_assumption');
  if (!tagged && !named) return false;
  assert(d.module.endsWith('.Spec') || d.module.endsWith('.Bridge'), `Assumptions belong in Spec or Bridge: ${d.name}`);
  assert(d.kind === 'definition' && d.returnsProp && !d.isProof,
    `An assumption must be a proposition-valued definition: ${d.name}`);
  return true;
}

/** Fails on an axiom that is neither foundational nor opaque. */
export function auditDeclarations(declarations, opaqueFunctions) {
  for (const d of declarations) {
    const untrusted = d.axioms.filter(a => !foundationalAxioms.has(a) && !opaqueFunctions.has(a));
    assert.equal(untrusted.length, 0, `${d.name} depends on unchecked axioms: ${untrusted}`);
  }
}

/** The status shown for `d`, and its opaque dependencies. */
export function declarationEvidence(d, opaqueFunctions) {
  const opaqueDependencies = d.axioms.filter(a => opaqueFunctions.has(a));
  const untrusted = d.axioms.some(a => !foundationalAxioms.has(a) && !opaqueFunctions.has(a));
  return { opaqueDependencies,
    status: untrusted ? 'axiom-dependent'
      : d.projectionOf ? 'structure field'
      : isAssumption(d) ? 'assumption'
      : d.kind === 'theorem' ? opaqueDependencies.length ? 'checked theorem (opaque boundary)' : 'checked theorem'
      : d.returnsProp ? d.kind === 'type' ? 'proposition structure' : 'proposition (not a proof)' : d.kind };
}

/** A theorem, not a structure field, that passes the audit. */
export function isCheckedTheorem(d) {
  return !d.projectionOf && d.kind === 'theorem' &&
    ['checked theorem', 'checked theorem (opaque boundary)'].includes(d.status);
}
