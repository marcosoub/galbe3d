/* Galbe 3D — moteur de modelage CSG pour les vues intégrées de Claude.
   Dépend de THREE (r128) et THREE.OrbitControls, chargés avant ce fichier.
   Usage : Galbe.mount('id-du-conteneur', spec)
   spec = {
     camera: { pos:[x,y,z], target:[x,y,z] },          (optionnel)
     objects: [ { id:'cube_1', ops:[ ... ] } ]
   }
   Opérations (la première crée le solide, les suivantes s'appliquent dans l'ordre) :
     { t:'box', size:[sx,sy,sz], pos:[x,y,z], prefix?:'bossage 1 ', names?:[6 noms] }
     { t:'cyl', r, h, pos, axis:'x'|'y'|'z', seg?:48, prefix?, names?:[latérale, +axe, -axe] }
     { op:'add'|'sub'|'inter', ...primitive ci-dessus }
     { op:'fillet', axis:'x'|'y'|'z', edge:[x,y,z] (un point de l'arête), dir:[sx,sy,sz] (signes vers l'extérieur
       sur les deux autres axes, 0 sur l'axe de l'arête), len, r, name:'congé 1' }
     { op:'chamfer', même chose que fillet, d au lieu de r, name:'chanfrein 1' }
   Les faces nommées '_' sont des faces techniques qui ne doivent pas rester visibles. */
(function (root) {
  'use strict';
  const EPS = 1e-5;
  const FN = { box: ['droite', 'gauche', 'dessus', 'dessous', 'avant', 'arrière'], cyl: ['latérale', 'dessus', 'dessous'] };
  const AX = { x: 0, y: 1, z: 2 };

  // ---------- Noyau CSG (arbres BSP, d'après csg.js d'Evan Wallace) ----------
  class V {
    constructor(x, y, z) { this.x = x; this.y = y; this.z = z; }
    clone() { return new V(this.x, this.y, this.z); }
    neg() { return new V(-this.x, -this.y, -this.z); }
    plus(a) { return new V(this.x + a.x, this.y + a.y, this.z + a.z); }
    minus(a) { return new V(this.x - a.x, this.y - a.y, this.z - a.z); }
    times(k) { return new V(this.x * k, this.y * k, this.z * k); }
    dot(a) { return this.x * a.x + this.y * a.y + this.z * a.z; }
    lerp(a, t) { return this.plus(a.minus(this).times(t)); }
    cross(a) { return new V(this.y * a.z - this.z * a.y, this.z * a.x - this.x * a.z, this.x * a.y - this.y * a.x); }
    unit() { return this.times(1 / Math.hypot(this.x, this.y, this.z)); }
  }
  class Vx {
    constructor(p, n) { this.p = p; this.n = n; }
    clone() { return new Vx(this.p.clone(), this.n.clone()); }
    flip() { this.n = this.n.neg(); }
    lerp(o, t) { return new Vx(this.p.lerp(o.p, t), this.n.lerp(o.n, t)); }
  }
  class Pl {
    constructor(n, w) { this.n = n; this.w = w; }
    static from(a, b, c) { const n = b.minus(a).cross(c.minus(a)).unit(); return new Pl(n, n.dot(a)); }
    clone() { return new Pl(this.n.clone(), this.w); }
    flip() { this.n = this.n.neg(); this.w = -this.w; }
    split(po, cf, cb, f, b) {
      let pt = 0; const ty = [];
      for (const v of po.v) { const t = this.n.dot(v.p) - this.w, y = t < -EPS ? 2 : t > EPS ? 1 : 0; pt |= y; ty.push(y); }
      if (pt === 0) (this.n.dot(po.pl.n) > 0 ? cf : cb).push(po);
      else if (pt === 1) f.push(po);
      else if (pt === 2) b.push(po);
      else {
        const F = [], B = [];
        for (let i = 0; i < po.v.length; i++) {
          const j = (i + 1) % po.v.length, ti = ty[i], tj = ty[j], vi = po.v[i], vj = po.v[j];
          if (ti !== 2) F.push(vi);
          if (ti !== 1) B.push(ti !== 2 ? vi.clone() : vi);
          if ((ti | tj) === 3) {
            const t = (this.w - this.n.dot(vi.p)) / this.n.dot(vj.p.minus(vi.p)), v = vi.lerp(vj, t);
            F.push(v); B.push(v.clone());
          }
        }
        if (F.length >= 3) f.push(new Po(F, po.s, po.pl));
        if (B.length >= 3) b.push(new Po(B, po.s, po.pl));
      }
    }
  }
  class Po {
    constructor(v, s, pl) { this.v = v; this.s = s; this.pl = pl ? pl.clone() : Pl.from(v[0].p, v[1].p, v[2].p); }
    clone() { return new Po(this.v.map(x => x.clone()), this.s, this.pl); }
    flip() { this.v.reverse().forEach(x => x.flip()); this.pl.flip(); }
  }
  class Nd {
    constructor(ps) { this.pl = null; this.f = null; this.b = null; this.ps = []; if (ps) this.build(ps); }
    invert() {
      this.ps.forEach(p => p.flip()); if (this.pl) this.pl.flip();
      if (this.f) this.f.invert(); if (this.b) this.b.invert();
      const t = this.f; this.f = this.b; this.b = t;
    }
    clip(ps) {
      if (!this.pl) return ps.slice();
      let f = [], b = [];
      for (const p of ps) this.pl.split(p, f, b, f, b);
      if (this.f) f = this.f.clip(f);
      b = this.b ? this.b.clip(b) : [];
      return f.concat(b);
    }
    clipTo(n) { this.ps = n.clip(this.ps); if (this.f) this.f.clipTo(n); if (this.b) this.b.clipTo(n); }
    all() { let p = this.ps.slice(); if (this.f) p = p.concat(this.f.all()); if (this.b) p = p.concat(this.b.all()); return p; }
    build(ps) {
      if (!ps.length) return;
      if (!this.pl) this.pl = ps[0].pl.clone();
      const f = [], b = [];
      for (const p of ps) this.pl.split(p, this.ps, this.ps, f, b);
      if (f.length) { if (!this.f) this.f = new Nd(); this.f.build(f); }
      if (b.length) { if (!this.b) this.b = new Nd(); this.b.build(b); }
    }
  }
  const cl = a => a.map(p => p.clone());
  const CSG = {
    add(a, b) { const A = new Nd(cl(a)), B = new Nd(cl(b)); A.clipTo(B); B.clipTo(A); B.invert(); B.clipTo(A); B.invert(); A.build(B.all()); return A.all(); },
    sub(a, b) { const A = new Nd(cl(a)), B = new Nd(cl(b)); A.invert(); A.clipTo(B); B.clipTo(A); B.invert(); B.clipTo(A); B.invert(); A.build(B.all()); A.invert(); return A.all(); },
    inter(a, b) { const A = new Nd(cl(a)), B = new Nd(cl(b)); A.invert(); B.clipTo(A); B.invert(); A.clipTo(B); B.clipTo(A); A.build(B.all()); A.invert(); return A.all(); }
  };

  // ---------- Primitives ----------
  function box(s, c, names) {
    const F = [[[0, 4, 6, 2], 1], [[1, 3, 7, 5], 0], [[0, 1, 5, 4], 3], [[2, 6, 7, 3], 2], [[0, 2, 3, 1], 5], [[4, 5, 7, 6], 4]];
    return F.map(([ix, k]) => {
      const n = new V(0, 0, 0); n[['x', 'y', 'z'][k >> 1]] = k % 2 ? -1 : 1;
      return new Po(ix.map(i => new Vx(new V(
        c[0] + s[0] / 2 * (i & 1 ? 1 : -1), c[1] + s[1] / 2 * (i & 2 ? 1 : -1), c[2] + s[2] / 2 * (i & 4 ? 1 : -1)), n.clone())), names[k]);
    });
  }
  // Orientation : l'axe local Y du cylindre est envoyé sur l'axe demandé (rotation directe).
  const ORIENT = {
    x: v => new V(v.y, -v.x, v.z),
    y: v => v,
    z: v => new V(v.x, -v.z, v.y)
  };
  function cyl(r, h, c, axis, names, seg) {
    const T = ORIENT[axis || 'y'], C = new V(c[0], c[1], c[2]);
    const P = (v, n) => new Vx(T(v).plus(C), T(n));
    const ps = [], hh = h / 2, top = [], bot = [];
    for (let i = 0; i < seg; i++) {
      const a0 = i / seg * Math.PI * 2, a1 = (i + 1) / seg * Math.PI * 2;
      const n0 = new V(Math.cos(a0), 0, Math.sin(a0)), n1 = new V(Math.cos(a1), 0, Math.sin(a1));
      ps.push(new Po([P(new V(r * n0.x, -hh, r * n0.z), n0), P(new V(r * n0.x, hh, r * n0.z), n0),
        P(new V(r * n1.x, hh, r * n1.z), n1), P(new V(r * n1.x, -hh, r * n1.z), n1)], names[0]));
      top.unshift(P(new V(r * n0.x, hh, r * n0.z), new V(0, 1, 0)));
      bot.push(P(new V(r * n0.x, -hh, r * n0.z), new V(0, -1, 0)));
    }
    ps.push(new Po(top, names[1]), new Po(bot, names[2]));
    return ps;
  }
  function prim(o) {
    const pre = o.prefix || '';
    if (o.t === 'box') return box(o.size, o.pos, (o.names || FN.box.map(n => pre + n)));
    if (o.t === 'cyl') return cyl(o.r, o.h, o.pos, o.axis, (o.names || FN.cyl.map(n => pre + n)), o.seg || 48);
    throw new Error('Primitive inconnue : ' + o.t);
  }
  // Chanfrein : prisme triangulaire construit directement (plus simple et exact).
  function chamferCutter(o) {
    const a = AX[o.axis], u = (a + 1) % 3, w = (a + 2) % 3, d = o.d, m = 1, L = o.len + 4;
    const su = o.dir[u], sw = o.dir[w];
    const P = (pa, pu, pw) => { const q = [0, 0, 0]; q[a] = o.edge[a] + pa; q[u] = o.edge[u] + su * pu; q[w] = o.edge[w] + sw * pw; return new V(q[0], q[1], q[2]); };
    // Profil (u,w) local, côté extérieur positif : triangle A(-d,0) B(0,-d) étendu vers l'extérieur.
    const prof = [[-d, 0], [0, -d], [m, -d], [m, m], [-d, m]];
    const ps = [];
    const n = prof.length, ha = L / 2;
    // Sens : on construit puis on vérifie l'orientation via le volume signé.
    const faces = [];
    for (let i = 0; i < n; i++) {
      const p0 = prof[i], p1 = prof[(i + 1) % n];
      faces.push({ v: [P(-ha, ...p0), P(ha, ...p0), P(ha, ...p1), P(-ha, ...p1)], s: i === 0 ? o.name : '_' });
    }
    faces.push({ v: prof.map(p => P(ha, ...p)), s: '_' });
    faces.push({ v: prof.slice().reverse().map(p => P(-ha, ...p)), s: '_' });
    // Volume signé pour fixer l'orientation (normales vers l'extérieur).
    let vol = 0;
    faces.forEach(f => { for (let i = 1; i < f.v.length - 1; i++) vol += f.v[0].dot(f.v[i].cross(f.v[i + 1])); });
    faces.forEach(f => {
      const pts = vol < 0 ? f.v.slice().reverse() : f.v;
      const pl = Pl.from(pts[0], pts[1], pts[2]);
      ps.push(new Po(pts.map(p => new Vx(p, pl.n.clone())), f.s, pl));
    });
    return ps;
  }

  function buildObject(ob) {
    let solid = null;
    for (const o of ob.ops) {
      let piece;
      if (o.op === 'fillet') { solid = CSG.sub(solid, edgeCutterFillet(o)); continue; }
      if (o.op === 'chamfer') { solid = CSG.sub(solid, chamferCutter(o)); continue; }
      piece = prim(o);
      if (!solid) { solid = piece; continue; }
      solid = CSG[o.op || 'add'](solid, piece);
    }
    return solid;
  }
  function edgeCutterFillet(o) {
    const a = AX[o.axis], u = (a + 1) % 3, w = (a + 2) % 3, r = o.r, m = 1;
    const su = o.dir[u], sw = o.dir[w], L = o.len + 4;
    const size = [0, 0, 0], pos = o.edge.slice();
    size[a] = L; size[u] = r + m; size[w] = r + m;
    pos[u] = o.edge[u] - su * r + su * (r + m) / 2;
    pos[w] = o.edge[w] - sw * r + sw * (r + m) / 2;
    const c = o.edge.slice(); c[u] -= su * r; c[w] -= sw * r;
    return CSG.sub(box(size, pos, Array(6).fill('_')), cyl(r, L + 2, c, o.axis, [o.name, '_', '_'], o.seg || 48));
  }

  // ---------- Conversion en maillage THREE ----------
  const COL = { base: 0xD3D1C7, hl: 0x378ADD, edge: 0x5F5E5A };
  function toMesh(THREE, ps) {
    const by = new Map();
    ps.forEach(p => {
      if (p.s === '_') return;
      if (!by.has(p.s)) by.set(p.s, { p: [], n: [] });
      const g = by.get(p.s);
      for (let i = 1; i < p.v.length - 1; i++) for (const v of [p.v[0], p.v[i], p.v[i + 1]]) { g.p.push(v.p.x, v.p.y, v.p.z); g.n.push(v.n.x, v.n.y, v.n.z); }
    });
    const geo = new THREE.BufferGeometry(), P = [], N = [], mats = []; let st = 0;
    [...by].forEach(([nm, g], mi) => {
      for (let i = 0; i < g.p.length; i++) { P.push(g.p[i]); N.push(g.n[i]); }
      const c = g.p.length / 3; geo.addGroup(st, c, mi); st += c;
      const m = new THREE.MeshStandardMaterial({ color: COL.base, roughness: 0.6, metalness: 0, polygonOffset: true, polygonOffsetFactor: 1, polygonOffsetUnits: 1 });
      m.userData.name = nm; mats.push(m);
    });
    geo.setAttribute('position', new THREE.Float32BufferAttribute(P, 3));
    geo.setAttribute('normal', new THREE.Float32BufferAttribute(N, 3));
    return new THREE.Mesh(geo, mats);
  }

  // Arêtes nommées d'après les deux faces qu'elles séparent ; grille spatiale pour la vitesse.
  function edgesFor(THREE, mesh) {
    const g = mesh.geometry, p = g.attributes.position, T = [], CELL = 4, grid = new Map();
    const key = (i, j, k) => i + ',' + j + ',' + k;
    g.groups.forEach(G => {
      const nm = mesh.material[G.materialIndex].userData.name;
      for (let i = G.start; i < G.start + G.count; i += 3) {
        const v = [0, 1, 2].map(j => new THREE.Vector3().fromBufferAttribute(p, i + j));
        const bb = new THREE.Box3().setFromPoints(v).expandByScalar(0.02), t = { t: new THREE.Triangle(v[0], v[1], v[2]), nm };
        const id = T.push(t) - 1;
        for (let x = Math.floor(bb.min.x / CELL); x <= Math.floor(bb.max.x / CELL); x++)
          for (let y = Math.floor(bb.min.y / CELL); y <= Math.floor(bb.max.y / CELL); y++)
            for (let z = Math.floor(bb.min.z / CELL); z <= Math.floor(bb.max.z / CELL); z++) {
              const k = key(x, y, z); if (!grid.has(k)) grid.set(k, []); grid.get(k).push(id);
            }
      }
    });
    const e = new THREE.EdgesGeometry(g, 1).attributes.position, out = new Map(), cp = new THREE.Vector3(), M = new THREE.Vector3();
    for (let i = 0; i < e.count; i += 2) {
      const a = new THREE.Vector3().fromBufferAttribute(e, i), b = new THREE.Vector3().fromBufferAttribute(e, i + 1);
      const near = t => {
        M.copy(a).lerp(b, t); const s = new Set();
        const cand = grid.get(key(Math.floor(M.x / CELL), Math.floor(M.y / CELL), Math.floor(M.z / CELL))) || [];
        for (const id of cand) { const x = T[id]; x.t.closestPointToPoint(M, cp); if (cp.distanceToSquared(M) < 4e-4) s.add(x.nm); }
        return s;
      };
      let s = near(0.5);
      if (s.size > 2) { const s1 = near(0.3), s2 = near(0.7); s = new Set([...s].filter(n => s1.has(n) && s2.has(n))); }
      if (s.size !== 2) continue;
      const k = [...s].sort().join(' / ');
      if (!out.has(k)) out.set(k, []); out.get(k).push(a, b);
    }
    return [...out].map(([k, pts]) => {
      const l = new THREE.LineSegments(new THREE.BufferGeometry().setFromPoints(pts), new THREE.LineBasicMaterial({ color: COL.edge }));
      l.userData.name = 'arête ' + k; return l;
    });
  }

  // ---------- Interface ----------
  const CSS = '.g3-bar{display:flex;gap:8px;margin:0 0 8px;align-items:center}.g3-b{font-size:13px;padding:6px 12px}' +
    '.g3-b.on{background:var(--bg-accent);color:var(--text-accent);border-color:var(--border-accent)}' +
    '.g3-vp{height:340px;border:0.5px solid var(--border);border-radius:12px;touch-action:none;overflow:hidden}' +
    '.g3-sel{font-size:13px;color:var(--text-secondary);margin:8px 0;min-height:20px}' +
    '.g3-row{display:flex;gap:8px}.g3-row input{flex:1;min-width:0}' +
    '.g3-err{font-size:13px;color:var(--text-danger);min-height:18px;margin-top:4px}';

  function mount(elId, spec) {
    const THREE = root.THREE, host = document.getElementById(elId);
    const st = document.createElement('style'); st.textContent = CSS; document.head.appendChild(st);
    host.innerHTML = '<div class="g3-bar"><button class="g3-b on" data-m="objet">Objet</button><button class="g3-b" data-m="face">Face</button>' +
      '<button class="g3-b" data-m="arete">Arête</button><span style="flex:1"></span>' +
      '<button class="g3-b" data-clr aria-label="Effacer la sélection"><i class="ti ti-x" aria-hidden="true"></i></button></div>' +
      '<div class="g3-vp"></div><div class="g3-sel">Calcul…</div>' +
      '<div class="g3-row"><input placeholder="' + (spec.placeholder || 'congé de 2 mm') + '"><button data-ok>OK ↗</button></div><div class="g3-err"></div>';
    const vp = host.querySelector('.g3-vp'), selEl = host.querySelector('.g3-sel'), err = host.querySelector('.g3-err'), cmd = host.querySelector('input');
    try {
      let W = vp.clientWidth; const H = 340;
      const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
      renderer.setPixelRatio(Math.min(root.devicePixelRatio || 1, 2)); renderer.setSize(W, H); vp.appendChild(renderer.domElement);
      const scene = new THREE.Scene(), camera = new THREE.PerspectiveCamera(45, W / H, 1, 3000);
      const cam = spec.camera || {}; camera.position.set(...(cam.pos || [100, 90, 130]));
      scene.add(new THREE.HemisphereLight(0xffffff, 0x888780, 0.85));
      const dl = new THREE.DirectionalLight(0xffffff, 0.6); dl.position.set(-60, 120, 90); scene.add(dl);
      const grid = new THREE.GridHelper(200, 20, 0x888780, 0xB4B2A9); grid.material.transparent = true; grid.material.opacity = 0.5; scene.add(grid);
      const controls = new THREE.OrbitControls(camera, renderer.domElement);
      controls.target.set(...(cam.target || [0, 20, 0])); controls.enableDamping = true; controls.update();
      const meshes = [], edges = []; let edgesDone = false;
      spec.objects.forEach(ob => { const m = toMesh(THREE, buildObject(ob)); m.userData.oid = ob.id; scene.add(m); meshes.push(m); });
      function ensureEdges() { if (edgesDone) return; edgesDone = true; meshes.forEach(m => edgesFor(THREE, m).forEach(l => { m.add(l); edges.push(l); })); }
      setTimeout(ensureEdges, 50);
      let mode = 'objet'; const sel = new Map();
      const refresh = () => { selEl.textContent = sel.size ? 'Sélection : ' + [...sel.keys()].join(', ') : 'Aucune sélection'; };
      const clearSel = () => { sel.forEach(s => s(false)); sel.clear(); refresh(); };
      const toggle = (k, f) => { if (sel.has(k)) { sel.get(k)(false); sel.delete(k); } else { f(true); sel.set(k, f); } err.textContent = ''; refresh(); };
      refresh();
      host.querySelectorAll('[data-m]').forEach(b => b.onclick = () => {
        mode = b.dataset.m; host.querySelectorAll('[data-m]').forEach(x => x.classList.toggle('on', x === b));
        if (mode === 'arete') ensureEdges(); clearSel();
      });
      host.querySelector('[data-clr]').onclick = clearSel;
      const rc = new THREE.Raycaster(), mv = new THREE.Vector2(); let down = null;
      renderer.domElement.addEventListener('pointerdown', e => { down = [e.clientX, e.clientY]; });
      renderer.domElement.addEventListener('pointerup', e => {
        if (!down) return; const d = Math.hypot(e.clientX - down[0], e.clientY - down[1]); down = null; if (d > 6) return;
        const R = renderer.domElement.getBoundingClientRect();
        mv.set((e.clientX - R.left) / R.width * 2 - 1, -(e.clientY - R.top) / R.height * 2 + 1); rc.setFromCamera(mv, camera);
        if (mode === 'arete') {
          ensureEdges(); rc.params.Line.threshold = camera.position.distanceTo(controls.target) / 80;
          const h = rc.intersectObjects(edges, false)[0]; if (!h) return clearSel();
          const l = h.object; toggle(l.parent.userData.oid + '/' + l.userData.name, on => l.material.color.setHex(on ? COL.hl : COL.edge)); return;
        }
        const h = rc.intersectObjects(meshes, false)[0]; if (!h) return clearSel();
        const m = h.object, id = m.userData.oid;
        if (mode === 'objet') toggle(id, on => m.material.forEach(x => x.color.setHex(on ? COL.hl : COL.base)));
        else { const mt = m.material[h.face.materialIndex]; toggle(id + '/face ' + mt.userData.name, on => mt.color.setHex(on ? COL.hl : COL.base)); }
      });
      cmd.oninput = () => { err.textContent = ''; };
      host.querySelector('[data-ok]').onclick = () => {
        if (!sel.size) { err.textContent = "Sélectionne d'abord un élément"; return; }
        if (!cmd.value.trim()) { err.textContent = 'Écris une consigne'; return; }
        root.sendPrompt('Sélection : ' + [...sel.keys()].join(', ') + ' → ' + cmd.value.trim());
      };
      root.addEventListener('resize', () => { W = vp.clientWidth; renderer.setSize(W, H); camera.aspect = W / H; camera.updateProjectionMatrix(); });
      (function loop() { root.requestAnimationFrame(loop); controls.update(); renderer.render(scene, camera); })();
    } catch (e) { selEl.textContent = ''; err.textContent = 'Erreur : ' + e.message; }
  }

  root.Galbe = { mount, CSG, box, cyl, buildObject, toMesh, edgesFor, version: '1.0.0' };
})(typeof window !== 'undefined' ? window : globalThis);
