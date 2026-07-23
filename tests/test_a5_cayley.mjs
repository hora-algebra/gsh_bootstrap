// Acceptance test for site/a5_cayley.js (the A5 word-problem visualization data).
// Run with: node tests/test_a5_cayley.mjs
import { createRequire } from "node:module";
import assert from "node:assert/strict";

const require = createRequire(import.meta.url);
const A5 = require("../site/a5_cayley.js");

const g = A5.build();

// Generator orders realize the (2,3,5) presentation.
assert.deepEqual(g.orders, { a: 2, b: 3, ab: 5 }, "orders of a, b, ab");

// |A5| = 60, and the permutation labelling is a well-defined homomorphism
// (i.e. the matrix group satisfies no relation the permutations break).
assert.equal(g.n, 60, "group order");
assert.ok(g.wellDefined, "permutation labels well-defined on states");

// a is a fixed-point-free involution on states: 30 a-edges.
for (let i = 0; i < g.n; i++) {
  assert.notEqual(g.ta[i], i, `a acts freely at ${i}`);
  assert.equal(g.ta[g.ta[i]], i, `a^2 = 1 at ${i}`);
}
// b is a fixed-point-free 3-cycle action: 20 b-triangles.
for (let i = 0; i < g.n; i++) {
  assert.notEqual(g.tb[i], i, `b acts freely at ${i}`);
  assert.equal(g.tb[g.tb[g.tb[i]]], i, `b^3 = 1 at ${i}`);
  assert.equal(g.tbInv[g.tb[i]], i, `tbInv inverts tb at ${i}`);
}
// (ab)^5 = 1 as a relation on every state.
for (let i = 0; i < g.n; i++) {
  let s = i;
  for (let k = 0; k < 5; k++) s = g.tb[g.ta[s]];
  assert.equal(s, i, `(ab)^5 = 1 at ${i}`);
}

// Each state's BFS word evaluates back to that state through the tables.
for (let i = 0; i < g.n; i++) {
  let s = 0;
  for (const ch of g.states[i].word) s = ch === "a" ? g.ta[s] : g.tb[s];
  assert.equal(s, i, `word of state ${i} evaluates to itself`);
}
assert.equal(g.states[0].word, "", "state 0 is the identity");
assert.equal(g.states[0].cycles, "e", "identity cycle notation");

// Layout: 60 distinct unit vectors; all a-edges and b-edges share one length.
const d = (u, v) => Math.hypot(u[0] - v[0], u[1] - v[1], u[2] - v[2]);
for (let i = 0; i < g.n; i++) {
  const p = g.states[i].pos;
  assert.ok(Math.abs(Math.hypot(...p) - 1) < 1e-9, `pos ${i} on unit sphere`);
  for (let j = i + 1; j < g.n; j++) {
    assert.ok(d(p, g.states[j].pos) > 0.05, `pos ${i} != pos ${j}`);
  }
}
const aLens = [], bLens = [];
for (let i = 0; i < g.n; i++) {
  aLens.push(d(g.states[i].pos, g.states[g.ta[i]].pos));
  bLens.push(d(g.states[i].pos, g.states[g.tb[i]].pos));
}
const spread = (xs) => Math.max(...xs) - Math.min(...xs);
assert.ok(spread(aLens) < 1e-6, "a-edge lengths equal");
assert.ok(spread(bLens) < 1e-6, "b-edge lengths equal");
assert.ok(Math.abs(aLens[0] - bLens[0]) < 1e-6, "a and b edge lengths match");

const diameter = Math.max(...g.states.map((s) => s.depth));
console.log(`ok: 60 states, edge length ${aLens[0].toFixed(4)}, BFS diameter ${diameter}`);
