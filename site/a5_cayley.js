/*
 * a5_cayley.js — Cayley graph data for A5 = < a, b | a^2 = b^3 = (ab)^5 = 1 >.
 *
 * The group is realized as the rotation group of the icosahedron:
 *   a = rotation by pi about an edge-midpoint axis,
 *   b = rotation by 2pi/3 about an adjacent face-center axis,
 * so that ab is a rotation by 2pi/5 about a vertex axis.
 * States are enumerated by BFS over words in {a, b}; the state reached by a
 * word w is ev(w) with right multiplication (state g --x--> g*x).
 * The 3D position of state g is g applied to a base point p0 chosen in the
 * open fundamental triangle so the orbit is free (60 distinct points); the
 * mixing parameter is tuned so a-edges and b-edges have equal length, which
 * makes the orbit polytope the truncated dodecahedron (20 triangles from b,
 * 12 decagons from the relation (ab)^5 = 1).
 *
 * Loadable both from the browser (window.A5Cayley) and from Node for tests.
 */
(function (root, factory) {
  var api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  root.A5Cayley = api;
})(typeof self !== "undefined" ? self : globalThis, function () {
  "use strict";

  var PHI = (1 + Math.sqrt(5)) / 2;

  // --- small 3D linear algebra -------------------------------------------
  function norm(v) {
    var n = Math.hypot(v[0], v[1], v[2]);
    return [v[0] / n, v[1] / n, v[2] / n];
  }
  function sub(u, v) { return [u[0] - v[0], u[1] - v[1], u[2] - v[2]]; }
  function dist(u, v) { return Math.hypot(u[0] - v[0], u[1] - v[1], u[2] - v[2]); }
  function matVec(m, v) {
    return [
      m[0] * v[0] + m[1] * v[1] + m[2] * v[2],
      m[3] * v[0] + m[4] * v[1] + m[5] * v[2],
      m[6] * v[0] + m[7] * v[1] + m[8] * v[2]
    ];
  }
  function matMul(p, q) {
    var r = new Array(9);
    for (var i = 0; i < 3; i++) {
      for (var j = 0; j < 3; j++) {
        r[3 * i + j] = p[3 * i] * q[j] + p[3 * i + 1] * q[3 + j] + p[3 * i + 2] * q[6 + j];
      }
    }
    return r;
  }
  var IDENTITY = [1, 0, 0, 0, 1, 0, 0, 0, 1];
  function matKey(m) {
    var parts = new Array(9);
    for (var i = 0; i < 9; i++) {
      var x = m[i];
      if (Math.abs(x) < 5e-7) x = 0; // avoid "-0.000000"
      parts[i] = x.toFixed(6);
    }
    return parts.join(",");
  }
  function matEq(m, w, eps) {
    for (var i = 0; i < 9; i++) if (Math.abs(m[i] - w[i]) > eps) return false;
    return true;
  }
  // Rodrigues rotation matrix: angle around unit axis k.
  function rotation(axis, angle) {
    var k = norm(axis);
    var c = Math.cos(angle), s = Math.sin(angle), t = 1 - c;
    var x = k[0], y = k[1], z = k[2];
    return [
      c + x * x * t, x * y * t - z * s, x * z * t + y * s,
      y * x * t + z * s, c + y * y * t, y * z * t - x * s,
      z * x * t - y * s, z * y * t + x * s, c + z * z * t
    ];
  }
  function matOrder(m, maxOrder) {
    var p = m;
    for (var k = 1; k <= maxOrder; k++) {
      if (matEq(p, IDENTITY, 1e-8)) return k;
      p = matMul(p, m);
    }
    return Infinity;
  }

  // --- permutations on {0..4}, for the A5 <= Sym(5) labelling -------------
  // permMul(p, q) = "apply p, then q", matching right multiplication of states.
  function permMul(p, q) {
    var r = new Array(p.length);
    for (var i = 0; i < p.length; i++) r[i] = q[p[i]];
    return r;
  }
  function permOrder(p) {
    var e = p.map(function (_x, i) { return i; });
    var r = p, k = 1;
    while (String(r) !== String(e)) { r = permMul(r, p); k++; if (k > 100) return Infinity; }
    return k;
  }
  function cycleNotation(p) {
    var seen = new Array(p.length).fill(false), out = "";
    for (var i = 0; i < p.length; i++) {
      if (seen[i] || p[i] === i) { seen[i] = true; continue; }
      var cyc = [], j = i;
      while (!seen[j]) { seen[j] = true; cyc.push(j + 1); j = p[j]; }
      out += "(" + cyc.join(" ") + ")";
    }
    return out === "" ? "e" : out;
  }

  // --- build the group and the layout --------------------------------------
  function build() {
    // One face of the icosahedron with vertices (0,±1,±φ) & cyclic shifts:
    var v1 = [0, 1, PHI], v3 = [PHI, 0, 1]; // two vertices of an edge of that face
    var faceCenter = [PHI / 3, 0, (2 * PHI + 1) / 3]; // centroid of {v1,(0,-1,φ),v3}
    var edgeMid = [(v1[0] + v3[0]) / 2, (v1[1] + v3[1]) / 2, (v1[2] + v3[2]) / 2];

    var A = rotation(edgeMid, Math.PI);
    // Choose the sense of b so that ab has order 5 (the (2,3,5) flag condition).
    var B = null, senses = [1, -1];
    for (var si = 0; si < senses.length; si++) {
      var cand = rotation(faceCenter, senses[si] * 2 * Math.PI / 3);
      if (matOrder(matMul(A, cand), 6) === 5) { B = cand; break; }
    }
    if (!B) throw new Error("no rotation sense makes ord(ab)=5");

    // Permutation labels: pa = (1 2)(3 4); search a 3-cycle pb with ord(pa*pb)=5.
    var pa = [1, 0, 3, 2, 4];
    var pb = null;
    outer:
    for (var x = 0; x < 5; x++) for (var y = 0; y < 5; y++) for (var z = 0; z < 5; z++) {
      if (x === y || y === z || x === z) continue;
      var q = [0, 1, 2, 3, 4]; q[x] = y; q[y] = z; q[z] = x;
      if (permOrder(q) === 3 && permOrder(permMul(pa, q)) === 5) { pb = q; break outer; }
    }
    if (!pb) throw new Error("no 3-cycle pb with ord(pa*pb)=5");

    // Base point p0 between the b-axis (face center) and the a-axis (edge
    // midpoint); tune t so |p0 - B p0| = |p0 - A p0| (equal edge lengths).
    var cDir = norm(faceCenter), mDir = norm(edgeMid);
    function p0At(t) {
      return norm([
        (1 - t) * cDir[0] + t * mDir[0],
        (1 - t) * cDir[1] + t * mDir[1],
        (1 - t) * cDir[2] + t * mDir[2]
      ]);
    }
    function edgeGap(t) {
      var p = p0At(t);
      return dist(p, matVec(A, p)) - dist(p, matVec(B, p));
    }
    var lo = 0.02, hi = 0.98; // edgeGap(lo) > 0 (a-edge long), edgeGap(hi) < 0
    for (var it = 0; it < 80; it++) {
      var mid = (lo + hi) / 2;
      if (edgeGap(mid) > 0) lo = mid; else hi = mid;
    }
    var p0 = p0At((lo + hi) / 2);

    // BFS over words in {a, b} with right multiplication.
    var states = [{ word: "", mat: IDENTITY, perm: [0, 1, 2, 3, 4], depth: 0 }];
    var index = new Map([[matKey(IDENTITY), 0]]);
    var ta = [], tb = [];
    var gens = [
      { letter: "a", mat: A, perm: pa, table: ta },
      { letter: "b", mat: B, perm: pb, table: tb }
    ];
    var wellDefined = true;
    for (var head = 0; head < states.length; head++) {
      var st = states[head];
      for (var gi = 0; gi < gens.length; gi++) {
        var g = gens[gi];
        var nm = matMul(st.mat, g.mat);
        var np = permMul(st.perm, g.perm);
        var key = matKey(nm);
        var idx = index.get(key);
        if (idx === undefined) {
          idx = states.length;
          index.set(key, idx);
          states.push({ word: st.word + g.letter, mat: nm, perm: np, depth: st.depth + 1 });
        } else if (String(states[idx].perm) !== String(np)) {
          wellDefined = false; // would contradict the presentation; tested in CI
        }
        g.table[head] = idx;
      }
    }

    var n = states.length;
    var tbInv = new Array(n);
    for (var i2 = 0; i2 < n; i2++) tbInv[tb[i2]] = i2;

    var out = states.map(function (s) {
      return {
        word: s.word,
        depth: s.depth,
        perm: s.perm,
        cycles: cycleNotation(s.perm),
        pos: matVec(s.mat, p0)
      };
    });

    return {
      n: n,
      states: out,
      ta: ta,
      tb: tb,
      tbInv: tbInv,
      wellDefined: wellDefined,
      orders: { a: matOrder(A, 6), b: matOrder(B, 6), ab: matOrder(matMul(A, B), 12) }
    };
  }

  return { build: build, cycleNotation: cycleNotation, permMul: permMul, permOrder: permOrder };
});
