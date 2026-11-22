/* Teste Modelo — física dos dedos + buracos do rosto (boca, orelhas e narinas).
   - Física nos dedos: a mão DESENHADA não atravessa mais a pele da cabeça (malha real do rosto) nem as cápsulas do corpo.
     O dedo rastreado continua indo adiante, então a pressão ainda empurra o corpo (modelo_corpo.js); só o visual para na pele.
   - Buracos: boca, 2 orelhas e 2 narinas são túneis. Quando a ponta do dedo está alinhada, ela entra, é guiada pela parede
     do túnel e para no fundo. Dedo dentro = a cabeça acompanha o movimento (arrasto) e, no fundo, é empurrada.
   - A boca abre sozinha (pose "A") enquanto há um dedo entrando e fecha de volta depois.
   - Painel Teste Modelo > Interação com o corpo: Física nos dedos, Buracos do rosto e Tamanho dos buracos.
     "Mostrar colisores" também desenha os túneis (rosa).
   Roda depois do rastreador (prioridade 22) e restaura os pontos reais antes dos outros sistemas (prioridade 26). */
(() => {
'use strict';
const VR = window.VR, T = VR.T, S = VR.S, H = VR.H, md = VR.modelo, ui = VR.ui, clamp = VR.clamp;
if (!md || !md.body) return;
const bd = md.body;

// ---------- ajustes (entram no "Restaurar tudo" do modelo) ----------
const DEF = { mdFingPhys: true, mdHoles: true, mdHoleSize: 1 };
for (const k in DEF) { md.DEF[k] = DEF[k]; if (!(k in S)) S[k] = DEF[k]; }

// ---------- buracos: [id, nome, entrada (espaço do osso 頭), direção para dentro, eixo largo, meia-largura, meia-altura, profundidade, funil] ----------
const V3 = (x, y, z) => new T.Vector3(x, y, z);
function frame(id, E, a, up, Rx, Ry, D, F, open) {
  const A = a.clone().normalize(), U = up.clone().sub(A.clone().multiplyScalar(up.dot(A))).normalize(), V = new T.Vector3().crossVectors(A, U).normalize();
  return { id, E, a: A, u: U, v: V, Rx, Ry, D, F, open: !!open };
}
const CAV = [
  frame('boca', V3(0, 0.022, 0.117), V3(0, -0.12, -0.99), V3(1, 0, 0), 0.024, 0.0145, 0.065, 0.02, true),
  frame('orelhaL', V3(0.094, 0.088, 0.022), V3(-1, 0, 0.12), V3(0, 1, 0), 0.0078, 0.0078, 0.028, 0.012),
  frame('orelhaR', V3(-0.094, 0.088, 0.022), V3(1, 0, 0.12), V3(0, 1, 0), 0.0078, 0.0078, 0.028, 0.012),
  frame('narinaL', V3(0.0095, 0.041, 0.119), V3(0, 0.85, -0.45), V3(1, 0, 0), 0.0068, 0.0068, 0.016, 0.012),
  frame('narinaR', V3(-0.0095, 0.041, 0.119), V3(0, 0.85, -0.45), V3(1, 0, 0), 0.0068, 0.0068, 0.016, 0.012)
];

// raio (m) de cada junta do dedo: mesma tabela da mão desenhada (handgeo.js) + folga
const RAD = { 1: [0.0138, 0.0124, 0.0110, 0.0092], 5: [0.0090, 0.0082, 0.0074, 0.0064], 9: [0.0094, 0.0085, 0.0076, 0.0066], 13: [0.0088, 0.0080, 0.0072, 0.0062], 17: [0.0078, 0.0070, 0.0063, 0.0055] };
const CHAINS = [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16], [17, 18, 19, 20]], PALM = [0, 5, 9, 13, 17], MARGIN = 0.0012, PALM_R = 0.016;

// ---------- superfície do rosto (vértices da malha em pose de repouso, no espaço do osso da cabeça) ----------
let ctx = null, head = null, ready = false, VP = null, VN = null, grid = null, tries = 0;
const CS = 0.012, gk = (x, y, z) => ((x + 64) * 128 + (y + 64)) * 128 + (z + 64);
function buildSurface(c) {
  head = c.bones['頭']; if (!head) return false;
  let mesh = null;
  c.model.traverse(o => { if (!mesh && o.isSkinnedMesh && o.morphTargetDictionary && o.morphTargetDictionary.el_blink !== undefined) mesh = o; });
  if (!mesh) c.model.traverse(o => { if (!mesh && o.isSkinnedMesh && /^head/i.test(o.name || (o.parent && o.parent.name) || '')) mesh = o; });
  if (!mesh) return false;
  const bi = mesh.skeleton.bones.indexOf(head); if (bi < 0) return false;
  const M = new T.Matrix4().copy(mesh.skeleton.boneInverses[bi]).multiply(mesh.bindMatrix), N3 = new T.Matrix3().getNormalMatrix(M);
  const g = mesh.geometry, pos = g.attributes.position; if (!g.attributes.normal) g.computeVertexNormals(); const nor = g.attributes.normal;
  const n = pos.count, v = new T.Vector3(), nn = new T.Vector3(); VP = new Float32Array(n * 3); VN = new Float32Array(n * 3); grid = new Map();
  for (let i = 0; i < n; i++) {
    v.fromBufferAttribute(pos, i).applyMatrix4(M); nn.fromBufferAttribute(nor, i).applyMatrix3(N3).normalize();
    VP[i * 3] = v.x; VP[i * 3 + 1] = v.y; VP[i * 3 + 2] = v.z; VN[i * 3] = nn.x; VN[i * 3 + 1] = nn.y; VN[i * 3 + 2] = nn.z;
    const k = gk(Math.floor(v.x / CS), Math.floor(v.y / CS), Math.floor(v.z / CS)); let a = grid.get(k); if (!a) grid.set(k, a = []); a.push(i);
  }
  return n > 100;
}
function nearest(p) {                                                           // vértice mais próximo (busca em células vizinhas)
  const cx = Math.floor(p.x / CS), cy = Math.floor(p.y / CS), cz = Math.floor(p.z / CS); let best = -1, bd2 = 1e9;
  for (let R = 1; R <= 2 && best < 0; R++) for (let x = -R; x <= R; x++) for (let y = -R; y <= R; y++) for (let z = -R; z <= R; z++) {
    const a = grid.get(gk(cx + x, cy + y, cz + z)); if (!a) continue;
    for (let q = 0; q < a.length; q++) { const i = a[q], dx = VP[i * 3] - p.x, dy = VP[i * 3 + 1] - p.y, dz = VP[i * 3 + 2] - p.z, d2 = dx * dx + dy * dy + dz * dz; if (d2 < bd2) { bd2 = d2; best = i; } }
  }
  return best;
}

// ---------- estado ----------
const _inv = new T.Matrix4(), _m3 = new T.Matrix3(), _qInv = new T.Quaternion(), _s = new T.Vector3();
const pl = new T.Vector3(), dl = new T.Vector3(), tmp = new T.Vector3(), tmp2 = new T.Vector3(), cp = new T.Vector3();
const W = [0, 1].map(() => Array.from({ length: 21 }, () => new T.Vector3())), PW = [0, 1].map(() => Array.from({ length: 21 }, () => new T.Vector3())), DD = [0, 1].map(() => Array.from({ length: 21 }, () => new T.Vector3()));
const saved = [0, 1].map(() => Array.from({ length: 21 }, () => new T.Vector3())), active = [false, false], inHole = [0, 1].map(() => new Array(5).fill(null)), hasPrev = [false, false];
const palmD = new T.Vector3(), OUT = { d: new T.Vector3(), cav: null, t: 0, hit: 0 }, HL = { d: new T.Vector3(), cav: null, t: 0, hit: 0 };
let sx = 1, sfxT = 0, tAcc = 0, mouthWant = 0, mouthSaved = null, tpMap = null;

// ---------- buraco: o ponto (espaço da cabeça) está num túnel? devolve o deslocamento que o mantém dentro da parede ----------
function holeAt(p, rl) {
  const k = clamp(S.mdHoleSize || 1, 0.5, 2.5);
  for (let ci = 0; ci < CAV.length; ci++) {
    const c = CAV[ci]; tmp.subVectors(p, c.E); const t = tmp.dot(c.a); if (t < -c.F || t > c.D * k + 0.01) continue;
    const Rx = c.Rx * k, Ry = c.Ry * k; if (rl > Math.min(Rx, Ry) * 1.45) continue;      // dedo grosso demais para este buraco (a pele não estica tanto)
    const fx = Math.max(Rx - 0.6 * rl, 0.35 * Rx), fy = Math.max(Ry - 0.6 * rl, 0.35 * Ry), x = tmp.dot(c.u), y = tmp.dot(c.v), e = Math.hypot(x / fx, y / fy);
    if (e > (t < 0 ? 1.5 : 1.0)) continue;                                       // fora da boca do túnel (funil de 1,5× na frente)
    let nx = x, ny = y, nt = t; if (e > 1) { nx = x / e; ny = y / e; }
    const tMax = c.D * k - rl * 0.5; let hit = 0; if (nt > tMax) { hit = nt - tMax; nt = tMax; }
    HL.d.copy(c.E).addScaledVector(c.a, nt).addScaledVector(c.u, nx).addScaledVector(c.v, ny).sub(p); HL.cav = c; HL.t = t; HL.hit = hit; return true;
  }
  return false;
}
// ---------- superfície do rosto: empurra o ponto para fora da pele (raio rl) ----------
function headSurface(p, rl) {
  if (Math.abs(p.x) > 0.2 || p.y < -0.15 || p.y > 0.32 || p.z < -0.18 || p.z > 0.25) return false;
  const i = grid ? nearest(p) : -1;
  if (i >= 0) {
    const nx = VN[i * 3], ny = VN[i * 3 + 1], nz = VN[i * 3 + 2], s = (p.x - VP[i * 3]) * nx + (p.y - VP[i * 3 + 1]) * ny + (p.z - VP[i * 3 + 2]) * nz;
    if (s >= rl) return false;
    dl.set(nx, ny, nz).multiplyScalar(Math.min(rl - s, rl + 0.025)); return true;
  }
  tmp.set(p.x / 0.1, (p.y - 0.09) / 0.125, (p.z - 0.03) / 0.105); const q = tmp.length();   // sem vértices por perto (nuca): elipsoide grosseiro
  if (q >= 1 || q < 1e-6) return false;
  dl.set(p.x, p.y - 0.09, p.z - 0.03).multiplyScalar(1 / q - 1 + rl / Math.max(0.05, Math.hypot(p.x, p.y - 0.09, p.z - 0.03))); return true;
}
// ---------- colisão de um ponto (mundo): devolve em OUT.d o deslocamento que o tira da pele / do corpo ----------
function collide(pw, rw, allowHole) {
  OUT.d.set(0, 0, 0); OUT.cav = null; OUT.hit = 0; OUT.t = 0;
  const segs = bd.SG;
  if (segs) for (let i = 0; i < segs.length; i++) {
    const sg = segs[i]; if (sg.id === 'cabeca') continue;                        // a cabeça usa a malha do rosto, não a cápsula
    tmp.subVectors(sg.b, sg.a); const L2 = tmp.lengthSq(); let t = 0; if (L2 > 1e-10) t = clamp(tmp2.subVectors(pw, sg.a).dot(tmp) / L2, 0, 1);
    cp.copy(sg.a).addScaledVector(tmp, t); tmp2.subVectors(pw, cp); const d = tmp2.length(), R = sg.R + rw; if (d >= R) continue;
    if (d > 1e-5) tmp2.divideScalar(d); else tmp2.set(0, 0, 1); OUT.d.addScaledVector(tmp2, Math.min(R - d, 0.03));
  }
  if (!head) return;
  pl.copy(pw).applyMatrix4(_inv); const rl = rw / sx;
  if (allowHole && S.mdHoles !== false && holeAt(pl, rl)) { OUT.cav = HL.cav; OUT.t = HL.t; OUT.hit = HL.hit; dl.copy(HL.d); OUT.d.add(dl.applyMatrix3(_m3)); }
  else if (headSurface(pl, rl)) OUT.d.add(dl.applyMatrix3(_m3));
}
function tpFlag(h, i, v) { const t = tpMap && tpMap.get(h * 32 + i); if (t) t.hole = v; }

// ---------- 1) antes da mão desenhada: ajusta os pontos que vão para a malha ----------
VR.hook(22, dt => {
  active[0] = active[1] = false; mouthWant = 0;
  if (!bd.ready || !md.on || !S.mdFingPhys || S.pass) { if (tpMap) bd.TP.forEach(t => { t.hole = false; }); return mouth(dt); }
  if (!ctx) { ctx = bd.ctx; if (!ctx) return; }
  if (!ready && tries < 40) { tries++; try { ready = buildSurface(ctx); } catch (e) { tries = 99; VR.log('buracos: ' + e.message); } if (ready) VR.log('buracos: malha do rosto ' + (VP.length / 3) + ' vértices'); }
  if (!head || !ctx.root.visible) return mouth(dt);
  if (!tpMap && bd.TP) { tpMap = new Map(); bd.TP.forEach(t => tpMap.set(t.h * 32 + t.i, t)); }
  if (tpMap) bd.TP.forEach(t => { t.hole = false; });
  head.updateWorldMatrix(true, false); _inv.copy(head.matrixWorld).invert(); _m3.setFromMatrix4(head.matrixWorld); sx = Math.max(_s.setFromMatrixScale(head.matrixWorld).x, 1e-3);
  _qInv.copy(VR.headQ).invert(); tAcc += dt;
  for (let h = 0; h < 2; h++) {
    const s = H[h]; if (!(s.vis && s.on)) { hasPrev[h] = false; continue; }
    const Wh = W[h], Dh = DD[h], P = s.P; active[h] = true;
    for (let i = 0; i < 21; i++) { saved[h][i].copy(P[i]); VR.toWorld(Wh[i], P[i]); Dh[i].set(0, 0, 0); }
    // mão toda (pulso + base dos dedos): maior penetração vira um deslocamento rígido
    palmD.set(0, 0, 0);
    for (let q = 0; q < PALM.length; q++) { collide(Wh[PALM[q]], PALM_R, false); if (OUT.d.lengthSq() > palmD.lengthSq()) palmD.copy(OUT.d); }
    if (palmD.length() > 0.08) palmD.setLength(0.08);
    if (palmD.lengthSq() > 0) for (let i = 0; i < 21; i++) { Wh[i].add(palmD); Dh[i].add(palmD); }
    // cada dedo, da base para a ponta: quem bate na pele dobra o dedo ali; a parte da frente acompanha
    for (let c = 0; c < 5; c++) {
      const ch = CHAINS[c]; inHole[h][c] = null;
      for (let k = 0; k < 4; k++) {
        const j = ch[k]; collide(Wh[j], RAD[ch[0]][k] + MARGIN, true);
        if (OUT.cav) { tpFlag(h, j, true); if (k === 3) { inHole[h][c] = { cav: OUT.cav, t: OUT.t, hit: OUT.hit }; if (OUT.cav.open && OUT.t > -0.012) mouthWant = 1; } }
        const l = OUT.d.length(); if (l < 1e-6) continue; if (l > 0.05) OUT.d.setLength(0.05);
        for (let kk = k; kk < 4; kk++) { Wh[ch[kk]].add(OUT.d); Dh[ch[kk]].add(OUT.d); }
      }
    }
    // escreve o resultado na mão (espaço da cabeça do jogador); os pontos reais voltam em seguida (prioridade 26)
    for (let i = 0; i < 21; i++) if (Dh[i].lengthSq() > 1e-10) P[i].add(tmp.copy(Dh[i]).applyQuaternion(_qInv));
    reaction(h, dt);
  }
  mouth(dt);
});
// ---------- 2) depois da mão desenhada: os pontos reais voltam (gestos, pinça e toque no corpo usam o dedo real) ----------
VR.hook(26, () => { for (let h = 0; h < 2; h++) if (active[h]) { const P = H[h].P; for (let i = 0; i < 21; i++) P[i].copy(saved[h][i]); active[h] = false; } });

// ---------- reação: dedo dentro do buraco arrasta a cabeça; no fundo, empurra ----------
function reaction(h, dt) {
  const Wh = W[h], Ph = PW[h];
  for (let c = 0; c < 5; c++) {
    const st = inHole[h][c], j = CHAINS[c][3];
    if (st && hasPrev[h]) {
      tmp.subVectors(Wh[j], Ph[j]).divideScalar(Math.max(dt, 0.004)); if (tmp.length() > 1.5) tmp.setLength(1.5);
      tmp.multiplyScalar(14);                                                   // arrasto
      if (st.hit > 0) { tmp2.copy(st.cav.a).transformDirection(head.matrixWorld); tmp.addScaledVector(tmp2, Math.min(st.hit * sx, 0.02) * 900); }   // fundo do túnel
      bd.nudge('頭', Wh[j], tmp);
      if (tAcc - sfxT > 0.18 && st.t < 0.004) { sfxT = tAcc; ui.sfx && ui.sfx(210 + Math.random() * 30, 0.04, 0.1); }   // entrou
    }
    Ph[j].copy(Wh[j]);
  }
  for (let i = 0; i < 21; i++) Ph[i].copy(Wh[i]); hasPrev[h] = true;
}
// ---------- a boca abre enquanto há um dedo entrando ----------
const MOUTH_A = 3;                                                              // índice de "A" em MOUTHS (modelo.js)
let mouthIdle = 0;
function mouth(dt) {
  if (mouthWant && S.mdHoles !== false) {
    mouthIdle = 0;
    if (mouthSaved === null && Math.round(S.mdMouth || 0) === 0) { mouthSaved = 0; S.mdMouth = MOUTH_A; }
  } else if (mouthSaved !== null) {
    mouthIdle += dt; if (mouthIdle > 0.35) { if (Math.round(S.mdMouth || 0) === MOUTH_A) S.mdMouth = mouthSaved; mouthSaved = null; }
  }
}

// ---------- túneis visíveis (junto de "Mostrar colisores") ----------
let dbgBuilt = false, dbgMeshes = [];
function debug() {
  const want = !!S.mdColl && md.on && ctx && ctx.root.visible && head;
  if (!want) { dbgMeshes.forEach(m => { m.visible = false; }); return; }
  if (!dbgBuilt) {
    dbgBuilt = true; const mat = new T.MeshBasicMaterial({ color: 0xff77cc, wireframe: true, transparent: true, opacity: 0.55, depthTest: false });
    CAV.forEach(c => { const m = new T.Mesh(new T.CylinderGeometry(1, 1, 1, 14, 1, true), mat); m.frustumCulled = false; m.matrixAutoUpdate = false; m.userData.c = c; head.add(m); dbgMeshes.push(m); });
  }
  const k = clamp(S.mdHoleSize || 1, 0.5, 2.5), bas = new T.Matrix4();
  dbgMeshes.forEach(m => {
    const c = m.userData.c; bas.makeBasis(tmp.copy(c.u).multiplyScalar(c.Rx * k), tmp2.copy(c.a).multiplyScalar(c.D * k), cp.copy(c.v).multiplyScalar(c.Ry * k));
    bas.setPosition(c.E.x + c.a.x * c.D * k * 0.5, c.E.y + c.a.y * c.D * k * 0.5, c.E.z + c.a.z * c.D * k * 0.5); m.matrix.copy(bas); m.matrixWorldNeedsUpdate = true; m.visible = true;
  });
}
VR.hook(52, () => { try { debug(); } catch (e) { if (!md._eb) { md._eb = 1; VR.log('buracos: ' + e.message); } } });

md.holes = { CAV, get ready() { return ready; } };
})();
