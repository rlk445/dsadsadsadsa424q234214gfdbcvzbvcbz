/* Teste Modelo — interação física com o corpo.
   - Os dedos (pontas, juntas, palma) empurram cabeça, pescoço, tronco, braços, antebraços, mãos, quadril, pernas, canelas e pés.
     Cada parte reage como uma mola amortecida: balança, passa do ponto e volta; a força também "vaza" para as juntas de cima (empurrar a mão balança o braço todo).
   - Cabelo, orelhas e rabo são empurrados pelos dedos (usa a física de mola que já existia em modelo.js).
   - Pinça ou mão fechada perto de uma parte = pega e arrasta (braço/perna/cabeça seguem a mão com limites de junta). Soltar = volta balançando.
   - De longe: aponte e pince (ou clique com o mouse / toque) numa parte para pegar e arrastar.
   - Cotovelos e joelhos são dobradiças (só dobram no sentido certo). Empurrar o tronco também desloca o corpo todo um pouco.
   Não há colisores específicos para as partes íntimas (as chaves "Mamilos"/"Parte íntima" continuam só visuais). */
(() => {
'use strict';
const VR = window.VR, T = VR.T, S = VR.S, H = VR.H, HEAD = VR.HEAD, md = VR.modelo, ui = VR.ui;
if (!md) return;
const DEG = Math.PI / 180, clamp = VR.clamp, W = VR.world;
const bd = md.body = { ready: false, on: false, NAMES: [], grabs: [null, null, null], info: '' };

// ---------- juntas: [nome, pai na cadeia, limite (graus), rigidez K, ganho de toque g, força de puxar kg, dobradiça (+1 dobra p/ frente, -1 p/ trás)] ----------
const JD = [['腰', null, 18, 48, 0.6, 260], ['上半身', '腰', 22, 62, 1.6, 320], ['上半身2', '上半身', 24, 62, 1.8, 340], ['首', '上半身2', 34, 130, 3.6, 520], ['頭', '首', 44, 105, 3.5, 560]];
['L', 'R'].forEach(s => {
  JD.push(['肩' + s, '上半身2', 16, 160, 1.6, 420], ['腕' + s, '肩' + s, 125, 55, 2.2, 480], ['ひじ' + s, '腕' + s, 150, 65, 4.0, 520, +1], ['手首' + s, 'ひじ' + s, 75, 80, 8.0, 600]);
  JD.push(['足' + s, '腰', 90, 70, 0.9, 320], ['ひざ' + s, '足' + s, 140, 80, 2.0, 380, -1], ['足首' + s, 'ひざ' + s, 50, 110, 4.5, 480]);
});
bd.NAMES = JD.map(j => j[0]);
// ---------- partes com colisão: [id, junta dona, ponta A, ponta B, raio (unid. do modelo), peso do deslocamento do corpo todo] — ponta = osso ou [osso, x, y, z] no espaço local do osso ----------
const SD = [['cabeca', '頭', ['頭', 0, 0.077, 0.075], ['頭', 0, 0.077, 0.075], 0.115, 0.3], ['pescoco', '首', '首', '頭', 0.036, 0.2],
  ['peito', '上半身2', ['上半身2', 0, 0.03, 0], ['上半身2', 0, 0.17, 0], 0.10, 1], ['barriga', '上半身', '上半身', '上半身2', 0.10, 1], ['quadril', '腰', ['下半身', 0, 0.01, 0], ['下半身', 0, 0.12, 0], 0.115, 1]];
['L', 'R'].forEach(s => {
  SD.push(['ombro' + s, '肩' + s, '肩' + s, '腕' + s, 0.045, 0.2], ['braco' + s, '腕' + s, '腕' + s, 'ひじ' + s, 0.04, 0.12], ['antebraco' + s, 'ひじ' + s, 'ひじ' + s, '手首' + s, 0.03, 0.1], ['mao' + s, '手首' + s, '手首' + s, ['手首' + s, 0, 0.11, 0], 0.035, 0.08],
    ['coxa' + s, '足' + s, '足' + s, 'ひざ' + s, 0.085, 0.6], ['canela' + s, 'ひざ' + s, 'ひざ' + s, '足首' + s, 0.045, 0.5], ['pe' + s, '足首' + s, '足首' + s, 'つま先' + s, 0.045, 0.5], ['dedos' + s, '足首' + s, 'つま先' + s, ['つま先' + s, 0, 0.07, 0], 0.04, 0.4]);
});
const NAME_PT = { cabeca: 'cabeça', pescoco: 'pescoço', peito: 'peito', barriga: 'barriga', quadril: 'quadril', ombro: 'ombro', braco: 'braço', antebraco: 'antebraço', mao: 'mão', coxa: 'coxa', canela: 'canela', pe: 'pé', dedos: 'dedos do pé' };
// constantes de sensação (ajustadas em teste)
const KP = 2200, KV = 450, KF = 30, PEN_MAX = 0.03, CW = [1, 0.5, 0.25, 0.12, 0.06], GW = [0.8, 0.5, 0.3, 0.18, 0.1, 0.06], MAXA = 900, MAXW = 14;

// ---------- estado ----------
let ctx = null, J = [], jIdx = {}, SG = [], TP = [], sc = 1, tAcc = 0;
const off = new T.Vector3(), offV = new T.Vector3();                           // deslocamento do corpo todo (metros, mundo)
const QP = new T.Quaternion(), qi = new T.Quaternion(), V1 = new T.Vector3(), V2 = new T.Vector3(), V3 = new T.Vector3(), V4 = new T.Vector3(), V5 = new T.Vector3(), Q1 = new T.Quaternion(), Q2 = new T.Quaternion();
const gripPrev = [false, false];
const HAND_PTS = [[4, 0.013], [8, 0.011], [12, 0.011], [16, 0.011], [20, 0.01], [3, 0.012], [7, 0.011], [11, 0.011], [15, 0.011], [19, 0.01], [9, 0.04], [0, 0.03], [5, 0.022], [17, 0.02]];   // [ponto da mão, raio em metros]
for (let h = 0; h < 2; h++) HAND_PTS.forEach(([i, r]) => TP.push({ h, i, r, p: new T.Vector3(), prev: new T.Vector3(), v: new T.Vector3(), on: false, has: false }));
bd.TP = TP;                                                                    // pontos de toque dos dedos (modelo_buracos.js marca t.hole quando o dedo está dentro de um buraco)

// ---------- início (chamado quando o modelo carrega) ----------
bd.init = c => {
  ctx = c; bd.ctx = c; J = []; jIdx = {}; SG = []; bd.SG = SG;
  const { bones, model, pivot } = c; model.updateMatrixWorld(true); pivot.getWorldQuaternion(QP);
  JD.forEach(([n, par, lim, K, g, kg, hinge]) => {
    const b = bones[n]; if (!b) return;
    const j = { n, b, par, lim: lim * DEG, K, g, kg, hinge: hinge || 0, rv: new T.Vector3(), w: new T.Vector3(), tq: new T.Vector3(), dg: new T.Vector3(), pos: new T.Vector3(), pq: new T.Quaternion(), aq: new T.Quaternion(), up: [], axis: null, grab: 0 };
    jIdx[n] = J.length; J.push(j);
  });
  J.forEach(j => { let p = j.par; while (p) { if (jIdx[p] !== undefined) j.up.push(jIdx[p]); const pj = JD.find(d => d[0] === p); p = pj ? pj[1] : null; } });
  // eixo da dobradiça (espaço do osso pai): perpendicular ao osso e à frente do personagem
  J.forEach(j => {
    if (!j.hinge) return; const child = j.b.children.find(ch => ch.isBone && /^(手首|足首)/.test(ch.name)); if (!child) { j.hinge = 0; return; }
    j.b.getWorldPosition(V1); child.getWorldPosition(V2); V2.sub(V1).normalize();
    V3.set(0, 0, j.hinge > 0 ? 1 : -1); V4.crossVectors(V2, V3).normalize();    // eixo no mundo (personagem de frente, sem giro no início)
    j.b.parent.getWorldQuaternion(Q1); j.axis = V4.clone().applyQuaternion(Q1.invert()).normalize();
  });
  SD.forEach(([id, own, a, bb, r, sw]) => {
    const ji = jIdx[own]; if (ji === undefined) return; const get = s => typeof s === 'string' ? { b: bones[s] } : { b: bones[s[0]], l: new T.Vector3(s[1], s[2], s[3]) };
    const A = get(a), B = get(bb); if (!A.b || !B.b) return;
    SG.push({ id, ji, A, B, r, sw, a: new T.Vector3(), b: new T.Vector3(), R: r, ab: new T.Vector3() });
  });
  bd.ready = true; bd.on = true;
};
bd.reset = () => { J.forEach(j => { j.rv.set(0, 0, 0); j.w.set(0, 0, 0); }); off.set(0, 0, 0); offV.set(0, 0, 0); releaseAll(); if (ctx && ctx.model) { ctx.model.position.x = 0; ctx.model.position.z = 0; } };

// ---------- geometria ----------
function segPoint(out, e) { if (e.l) { out.copy(e.l); e.b.localToWorld(out); } else out.setFromMatrixPosition(e.b.matrixWorld); }
function closestOnSeg(p, A, B, out) {                                           // retorna t (0..1) e coloca o ponto em out
  V5.subVectors(B, A); const L2 = V5.lengthSq(); let t = 0;
  if (L2 > 1e-10) { t = clamp(V3.subVectors(p, A).dot(V5) / L2, 0, 1); }
  out.copy(A).addScaledVector(V5, t); return t;
}
const _hit = { t: 0, s: 0, d: 0 };
function raySeg(o, d, A, B) {                                                   // aproximação mais próxima entre um raio (d normalizado) e um segmento
  const v = V5.subVectors(B, A), w0 = V3.subVectors(o, A), b = d.dot(v), c = v.lengthSq(), d0 = d.dot(w0), e = v.dot(w0);
  let s = 0; if (c > 1e-10) { const den = c - b * b; s = den > 1e-10 ? (e - b * d0) / den : 0; s = clamp(s, 0, 1); }
  let t = s * b - d0; if (t < 0) { t = 0; s = c > 1e-10 ? clamp(e / c, 0, 1) : 0; }
  V4.copy(A).addScaledVector(v, s); V2.copy(o).addScaledVector(d, t);
  _hit.t = t; _hit.s = s; _hit.d = V2.distanceTo(V4); return _hit;
}
function computeSegs() {
  SG.forEach(s => { segPoint(s.a, s.A); segPoint(s.b, s.B); s.R = s.r * sc; });
  J.forEach(j => { j.pos.setFromMatrixPosition(j.b.matrixWorld); j.b.parent.getWorldQuaternion(j.pq); });
}

// ---------- pegar ----------
function releaseGrab(i) {
  const g = bd.grabs[i]; if (!g) return;
  if (g.kind === 'tip' && md.st && md.st.ph && md.st.ph[g.name] && g.s && g.s.vel) md.st.ph[g.name].v.copy(g.s.vel).multiplyScalar(0.5);   // solta o fio de cabelo com a velocidade da mão
  bd.grabs[i] = null; if (bd.tipT) delete bd.tipT[g.name]; J.forEach(j => { j.grab = 0; }); bd.grabs.forEach(o => { if (o && o.kind === 'seg') J[o.ji].grab = 1; });
}
function releaseAll() { for (let i = 0; i < 3; i++) releaseGrab(i); bd.tipT = {}; }
bd.releaseAll = releaseAll;
function tipList() { const o = []; if (!md.st || !md.st.ph) return o; for (const n in md.st.ph) { if (/^(hair|ear|tail)/.test(n) && ctx.bones[n]) o.push(n); } return o; }
function nearestNear(p) {                                                       // parte mais próxima de um ponto (mãos tocando)
  let best = null, bd2 = 1e9;
  SG.forEach(s => { closestOnSeg(p, s.a, s.b, V1); const d = V1.distanceTo(p) - s.R; if (d < 0.05 * Math.max(1, sc) && d < bd2) { bd2 = d; best = { kind: 'seg', s, ji: s.ji, d }; } });
  tipList().forEach(n => { const ps = md.st.ph[n]; ctx.bones[n].getWorldPosition(V2); closestOnSeg(p, V2, ps.p, V1); const d = V1.distanceTo(p) - 0.02 - 0.02 * sc; if (d < 0.05 && d < bd2) { bd2 = d; best = { kind: 'tip', name: n, d }; } });
  return best;
}
function pickRay(o, d) {                                                        // parte atingida por um raio (mais perto)
  if (!bd.ready || !ctx || !ctx.root.visible) return null; let best = null, bt = 1e9;
  SG.forEach(s => { const h = raySeg(o, d, s.a, s.b); if (h.d <= s.R * 1.25 && h.t < bt && h.t > 0.1) { bt = h.t; best = { kind: 'seg', s, ji: s.ji, t: h.t, pt: V4.clone() }; } });
  tipList().forEach(n => { const ps = md.st.ph[n]; ctx.bones[n].getWorldPosition(V2); const h = raySeg(o, d, V2.clone(), ps.p); if (h.d <= 0.035 * Math.max(1, sc) && h.t < bt - 0.05 && h.t > 0.1) { bt = h.t; best = { kind: 'tip', name: n, t: h.t, pt: V4.clone() }; } });
  return best;
}
bd.pickRay = pickRay;
function startGrab(i, s, cand, pt, mode, dist) {
  if (!cand || bd.grabs[i]) return false;
  for (const g of bd.grabs) if (g && ((cand.kind === 'seg' && g.kind === 'seg' && g.ji === cand.ji) || (cand.kind === 'tip' && g.kind === 'tip' && g.name === cand.name))) return false;   // uma parte só é segurada por uma mão
  const g = { kind: cand.kind, s, mode, dist: dist || 1, T: new T.Vector3(), name: cand.name, ji: cand.ji, sw: cand.s ? cand.s.sw : 0.2, local: new T.Vector3(), part: cand.s ? cand.s.id.replace(/[LR]$/, '') : 'cabelo' };
  if (cand.kind === 'seg') { g.local.copy(pt); J[cand.ji].b.worldToLocal(g.local); J[cand.ji].grab = 1; } else { if (!bd.tipT) bd.tipT = {}; bd.tipT[cand.name] = g.T; g.T.copy(pt); }
  bd.grabs[i] = g; ui.sfx && ui.sfx(300, 0.05, 0.25); return true;
}
function targetOf(i, g) {
  const s = g.s;
  if (g.mode === 'near') return g.T.copy(s.anchor);
  const o = i === 2 ? ui.mouse.o : HEAD, d = i === 2 ? ui.mouse.d : s.aim; return g.T.copy(o).addScaledVector(d, g.dist);
}
function updateGrabs(dt) {
  for (let i = 0; i < 3; i++) {
    const s = i === 2 ? VR.MH : H[i], g = bd.grabs[i];
    if (i < 2) { const grip = !!(s.vis && s.on && (s.pinch || s.fist)); const edge = grip && !gripPrev[i]; gripPrev[i] = grip;
      if (g && !grip) { releaseGrab(i); continue; }
      if (!g && edge && !s.held && !s.uiHover && !s.busy && S.mdTouch) { const c = nearestNear(s.anchor); if (c) startGrab(i, s, c, s.anchor, 'near'); } }
    else if (g && !s.pinch) { releaseGrab(i); continue; }
    const gg = bd.grabs[i]; if (!gg) continue;
    targetOf(i, gg);
    if (gg.kind === 'tip') continue;
    const j0 = J[gg.ji]; V1.copy(gg.local); j0.b.localToWorld(V1);              // ponto segurado agora
    V2.subVectors(gg.T, V1); const err = V2.length(); gg.err = err;
    if (err > 0.55 * Math.max(1, sc)) { releaseGrab(i); continue; }              // esticou demais: solta
    const chain = [gg.ji].concat(J[gg.ji].up);
    for (let k = 0; k < chain.length && k < GW.length; k++) {
      const j = J[chain[k]]; V3.subVectors(V1, j.pos); V4.subVectors(gg.T, j.pos); const la = V3.length(), lb = V4.length(); if (la < 0.02 || lb < 0.02) continue;
      V5.crossVectors(V3, V4); const sn = V5.length(); if (sn < 1e-8) continue; const ang = Math.atan2(sn, V3.dot(V4));
      V5.multiplyScalar(Math.min(ang, 0.7) * GW[k] / sn); j.dg.add(V5); j.grab = 1;
    }
    V2.y = 0; offV.addScaledVector(V2, 26 * dt * gg.sw);                         // puxar uma parte leva o corpo junto (mais no tronco e nas pernas)
  }
}

// ---------- pontos de toque das mãos ----------
function gatherTouchers(dt) {
  const k = dt > 0 ? 1 / dt : 0;
  TP.forEach(t => {
    const s = H[t.h]; t.on = !!(S.mdTouch && s.vis && s.on && !bd.grabs[t.h]);
    if (!t.on) { t.has = false; return; }
    VR.toWorld(t.p, s.P[t.i]);
    if (t.has) { V1.subVectors(t.p, t.prev).multiplyScalar(k); if (V1.length() > 6) V1.setLength(6); t.v.lerp(V1, 0.5); } else t.v.set(0, 0, 0);
    t.prev.copy(t.p); t.has = true;
  });
}
let sfxT = 0;
function contacts(dt) {
  TP.forEach(t => {
    if (!t.on) return; const tr = t.r;
    for (let si = 0; si < SG.length; si++) {
      const sg = SG[si]; if (t.hole && (sg.id === 'cabeca' || sg.id === 'pescoco')) continue;   // dedo dentro de um buraco do rosto: não empurra a cabeça pela cápsula
      closestOnSeg(t.p, sg.a, sg.b, V1); const d = V1.distanceTo(t.p), R = sg.R + tr; if (d >= R) continue;
      const pen = Math.min(R - d, PEN_MAX * Math.max(1, sc)); if (d > 1e-5) V2.subVectors(V1, t.p).divideScalar(d); else { V2.copy(t.v); if (V2.lengthSq() < 1e-8) V2.set(0, 0, -1); V2.normalize(); }   // n: do dedo para dentro da parte
      const vn = t.v.dot(V2), vnp = Math.min(Math.max(vn, 0), 3);
      V3.copy(V2).multiplyScalar(pen * KP + vnp * KV);                          // força de contato
      V4.copy(t.v).addScaledVector(V2, -vn); if (V4.length() > 1.5) V4.setLength(1.5); V3.addScaledVector(V4, KF);   // atrito: arrastar a pele
      const chain = [sg.ji].concat(J[sg.ji].up);
      for (let k = 0; k < chain.length && k < CW.length; k++) { const j = J[chain[k]]; V5.subVectors(t.p, j.pos).cross(V3); j.tq.addScaledVector(V5, CW[k]); }
      V3.y = 0; offV.addScaledVector(V3, 0.0008 * sg.sw);                        // empurrão no corpo todo
      if (vnp > 0.35 && tAcc - sfxT > 0.14) { sfxT = tAcc; ui.sfx && ui.sfx(170 + Math.min(vnp, 2) * 90 + Math.random() * 40, 0.035, 0.18); }
    }
  });
}

// ---------- molas das juntas ----------
function integrate(dt) {
  const stiff = clamp(S.mdStiff === undefined ? 1 : S.mdStiff, 0.3, 3), N = 2, h = dt / N;
  J.forEach(j => {
    qi.copy(j.pq).invert();
    const ac = V1.copy(j.tq).applyQuaternion(qi).multiplyScalar(j.g);           // aceleração do toque (espaço do osso pai)
    if (j.grab) ac.addScaledVector(V2.copy(j.dg).applyQuaternion(qi), j.kg);
    const K = j.K * stiff * (j.grab ? 0.12 : 1), zeta = j.grab ? 1.0 : 0.26, D = 2 * zeta * Math.sqrt(K + (j.grab ? j.kg : 0));
    for (let n = 0; n < N; n++) {
      V3.copy(ac).addScaledVector(j.rv, -K).addScaledVector(j.w, -D); const al = V3.length(); if (al > MAXA) V3.multiplyScalar(MAXA / al);
      j.w.addScaledVector(V3, h); const wl = j.w.length(); if (wl > MAXW) j.w.multiplyScalar(MAXW / wl);
      j.rv.addScaledVector(j.w, h);
      if (j.hinge && j.axis) { const a = clamp(j.rv.dot(j.axis), 0, j.lim), wa = j.w.dot(j.axis); j.rv.copy(j.axis).multiplyScalar(a); j.w.copy(j.axis).multiplyScalar((a <= 0 && wa < 0) || (a >= j.lim && wa > 0) ? 0 : wa); }
      else { const l = j.rv.length(); if (l > j.lim) { j.rv.multiplyScalar(j.lim / l); V4.copy(j.rv).normalize(); const o = j.w.dot(V4); if (o > 0) j.w.addScaledVector(V4, -o); } }
    }
    if (!isFinite(j.rv.x + j.rv.y + j.rv.z + j.w.x + j.w.y + j.w.z)) { j.rv.set(0, 0, 0); j.w.set(0, 0, 0); }
    j.tq.set(0, 0, 0); j.dg.set(0, 0, 0);
  });
  // deslocamento do corpo todo
  const K = 34 * stiff, D = 2 * 0.35 * Math.sqrt(K);
  for (let n = 0; n < N; n++) { offV.addScaledVector(off, -K * h).addScaledVector(offV, -D * h); off.addScaledVector(offV, h); }
  off.y = 0; offV.y = 0; const ol = off.length(), mx = 0.16 * Math.max(1, sc); if (ol > mx) { off.multiplyScalar(mx / ol); }
  if (offV.length() > 3) offV.setLength(3); if (!isFinite(off.x + off.z + offV.x + offV.z)) { off.set(0, 0, 0); offV.set(0, 0, 0); }
}
function applyPose() {                                                           // aplica o deslocamento atual das molas por cima da pose base (rotação no espaço do osso pai)
  for (let i = 0; i < J.length; i++) {
    const j = J[i], a = j.rv.length(); if (a < 1e-6) { j.aq.identity(); continue; }
    j.aq.setFromAxisAngle(V1.copy(j.rv).divideScalar(a), a); j.b.quaternion.premultiply(j.aq);
  }
}
function applyDelta() {                                                          // depois de integrar: aplica só a diferença (sem atraso de um quadro)
  for (let i = 0; i < J.length; i++) {
    const j = J[i], a = j.rv.length(); if (a < 1e-6 && j.aq.w > 0.999999) continue;
    if (a < 1e-6) Q1.identity(); else Q1.setFromAxisAngle(V1.copy(j.rv).divideScalar(a), a);
    j.b.quaternion.premultiply(Q2.copy(j.aq).invert().premultiply(Q1)); j.aq.copy(Q1);
  }
}

// ---------- quadro a quadro: chamado por modelo.js depois da pose e antes da física do cabelo ----------
bd.step = dt => {
  if (!bd.ready || !ctx) return;
  dt = clamp(dt, 0.001, 0.033); tAcc += dt; const { model, pivot } = ctx;
  sc = pivot.scale.x; pivot.getWorldQuaternion(QP);
  bd.on = !!S.mdTouch;
  if (!bd.on && bd.grabs.some(Boolean)) releaseAll();
  if (!bd.on && off.lengthSq() < 1e-8 && offV.lengthSq() < 1e-8 && !J.some(j => j.rv.lengthSq() > 1e-8 || j.w.lengthSq() > 1e-8)) { debug(); return; }   // desligado e já parado
  // o corpo todo desliza (mundo → espaço do modelo)
  V1.copy(off).applyQuaternion(Q1.copy(QP).invert()).divideScalar(sc || 1); model.position.x = V1.x; model.position.z = V1.z;
  applyPose(); model.updateMatrixWorld(true);                                  // colisores seguem a pose já deslocada
  computeSegs(); gatherTouchers(dt);
  if (bd.on) { updateGrabs(dt); contacts(dt); }
  integrate(dt); applyDelta(); model.updateMatrixWorld(true);
  bd.info = (() => { const g = bd.grabs.find(Boolean); return g ? 'segurando: ' + (NAME_PT[g.part] || g.part) : ''; })();
  debug();
};

// ---------- física do cabelo / orelhas / rabo: empurrados e puxados pelos dedos (chamado dentro de physStep) ----------
bd.tip = (n, ps, head, L, dt) => {
  if (!bd.on || !/^(hair|ear|tail)/.test(n)) return false;
  const T0 = bd.tipT && bd.tipT[n];
  if (T0) { ps.p.lerp(T0, 1 - Math.exp(-22 * dt)); ps.v.set(0, 0, 0); return true; }   // segurado: a ponta segue a mão
  for (let i = 0; i < TP.length; i++) {
    const t = TP[i]; if (!t.on) continue; const R = t.r + 0.022 * sc;
    for (let m = 0; m < 2; m++) {
      V1.copy(ps.p); if (m === 0) V1.add(head).multiplyScalar(0.5);               // meio e ponta do fio
      const d = V1.distanceTo(t.p); if (d >= R) continue;
      if (d > 1e-5) V2.subVectors(V1, t.p).divideScalar(d); else V2.set(0, 1, 0);
      ps.p.addScaledVector(V2, (R - d) * (m === 0 ? 2 : 1)); ps.v.addScaledVector(V2, 0.25).addScaledVector(t.v, 0.4);
    }
  }
  if (ps.v.length() > 4) ps.v.setLength(4);
  return false;
};
bd.held = n => !!(bd.tipT && bd.tipT[n]);

// ---------- ponteiro (mouse, toque ou mão apontando de longe): realça e pega partes do corpo ----------
const _pointer = W.pointer, _peek = W.peek, hoverPt = new T.Vector3();
W.pointer = (p, press, s) => {
  const r = _pointer(p, press, s);
  if (r || !md.on || !S.mdTouch || !bd.ready || S.pass) return r;
  const i = p.idx, hand = i < 2 ? H[i] : null;
  if (hand && (hand.held || hand.busy)) return r;
  let c = null, pt = null, mode = 'ray', dist = 1;
  if (hand && press) { const n = nearestNear(hand.anchor); if (n) { c = n; pt = hand.anchor; mode = 'near'; } }   // dedos já encostados: pega ali mesmo
  const hit = pickRay(p.o, p.d);
  if (!c && hit) { c = hit; pt = hit.pt; dist = hit.t; }
  if (!c) return null;
  if (press && s && !s.held) { if (startGrab(i, s, c, pt, mode, dist) && s) s.busy = i < 2; }
  if (hit) { hoverPt.copy(hit.pt); return { point: hoverPt, kind: 'prop' }; }
  return null;
};
W.peek = (o, d) => _peek(o, d) || !!(md.on && S.mdTouch && bd.ready && !S.pass && pickRay(o, d));

// ---------- colisores visíveis (opcional) ----------
let dbg = null, dSeg = [], dPts = [], dMat = null, dPm = null;
function debug() {
  const want = !!S.mdColl && md.on && ctx && ctx.root.visible && bd.ready;
  if (!want) { if (dbg) dbg.visible = false; return; }
  if (!dbg) { dbg = new T.Group(); VR.scene.add(dbg); }
  dbg.visible = true;
  const mat = dMat || (dMat = new T.MeshBasicMaterial({ color: 0x66ffcc, wireframe: true, transparent: true, opacity: 0.35, depthTest: false }));
  while (dSeg.length < SG.length) {
    const i = dSeg.length, s = SG[i]; const len = Math.max(s.a.distanceTo(s.b), 0.001), geo = T.CapsuleGeometry ? new T.CapsuleGeometry(s.R, len, 4, 10) : new T.CylinderGeometry(s.R, s.R, len + 2 * s.R, 10);
    const m = new T.Mesh(geo, mat); m.userData.len = len; m.userData.R = s.R; dbg.add(m); dSeg.push(m);
  }
  SG.forEach((s, i) => {
    const m = dSeg[i], len = Math.max(s.a.distanceTo(s.b), 0.001);
    if (Math.abs(m.userData.R - s.R) > 1e-4 || Math.abs(m.userData.len - len) > 2e-3) { m.geometry.dispose(); m.geometry = T.CapsuleGeometry ? new T.CapsuleGeometry(s.R, len, 4, 10) : new T.CylinderGeometry(s.R, s.R, len + 2 * s.R, 10); m.userData.len = len; m.userData.R = s.R; }
    m.position.copy(s.a).add(s.b).multiplyScalar(0.5); V1.subVectors(s.b, s.a); if (V1.lengthSq() > 1e-10) m.quaternion.setFromUnitVectors(V2.set(0, 1, 0), V1.normalize());
  });
  const pm = dPm || (dPm = new T.MeshBasicMaterial({ color: 0xffd166, depthTest: false }));
  while (dPts.length < TP.length) { const m = new T.Mesh(new T.SphereGeometry(1, 8, 6), pm); dbg.add(m); dPts.push(m); }
  TP.forEach((t, i) => { const m = dPts[i]; m.visible = t.on; if (t.on) { m.position.copy(t.p); m.scale.setScalar(t.r); } });
}
bd.hide = () => { if (dbg) dbg.visible = false; };
// empurrão externo numa junta (força em newtons aproximados, ponto no mundo) — usado pelos buracos do rosto
bd.nudge = (name, p, f) => { const j = J[jIdx[name]]; if (!j) return; V5.subVectors(p, j.pos).cross(f); j.tq.add(V5); };
})();
