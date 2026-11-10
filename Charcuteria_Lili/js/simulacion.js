(function () {
  "use strict";
  // Los registros iniciales se cargan desde datos.js.
  const { SEED_M, SEED_C } = window.LILI_DATOS;

  const VENTANA = 120; let NUM_EMP = 3;   // NUM_EMP ahora se puede cambiar (1 a 3) desde el panel
  const COLORES = { cola1: 0xf0a030, cola2: 0xf0a030, mostrador: 0x3cb04a, caja: 0x3a78d8, salida: 0x999999 };

  const $ = id => document.getElementById(id);
  const { fmt, expo, pick, fact, clamp, numero, tmin, hhmm, media } = window.LILI_UTILIDADES;

  // Geometría de la escena 3D (unidades ≈ metros) 
  const X_ENT = -19, X_SAL = 19.8, Z_EMP = [-5.6, 0, 5.6];
  const X_SERV = -3.6, X_EMPL = -1.6, X_BAR = -2.6, LANE_X = -4.8, Z_PAS = -9.6;
  const Z_CAJA = 10.1, X_CLI_CAJA = X_SERV, Z_SALIDA = 13.4;   // la caja queda al lado del empleado 3
  const posCola1 = i => [-6.4 - (i % 10) * 0.96, Math.floor(i / 10) * 0.96];
  const posCola2 = i => [-4.8 - (i % 8) * 0.96, Z_CAJA - Math.floor(i / 8) * 0.96];

  // Base de datos (guardada en el navegador)
  const KEY = 'lili_bd_v1';
  function semilla() {
    const bd = { obs: [], mostrador: [], caja: [] };
    [1, 2, 3].forEach(o => {
      bd.obs.push({ id: o, nombre: 'Observación ' + o });
      SEED_M[o].forEach(r => bd.mostrador.push({ o: o, cl: r[0], ll: r[1], en: r[2], sv: r[3], ini: r[4], fin: r[5], se: r[6], es: r[7] }));
      SEED_C[o].forEach(r => bd.caja.push({ o: o, cl: r[0], ll: r[1], en: r[2], ini: r[3], fin: r[4], se: r[5], es: r[6] }));
    });
    return bd;
  }
  function cargaBD() {
    try { const s = localStorage.getItem(KEY); if (s) { const o = JSON.parse(s); if (o && Array.isArray(o.obs) && Array.isArray(o.mostrador) && Array.isArray(o.caja)) return o; } } catch (e) { }
    return semilla();
  }
  let BD = cargaBD();
  function guardaBD() { try { localStorage.setItem(KEY, JSON.stringify(BD)); } catch (e) { } }
  const ui = { obs: 'all', tabla: 'M' };
  const enScope = (rows, sc) => sc === 'all' ? rows : rows.filter(r => r.o === sc);

  function estadisticas(sc) {
    const M = enScope(BD.mostrador, sc), C = enScope(BD.caja, sc), entre = [];
    const ids = sc === 'all' ? BD.obs.map(o => o.id) : [sc];
    ids.forEach(id => {
      const rs = BD.mostrador.filter(r => r.o === id).sort((a, b) => tmin(a.ll) - tmin(b.ll) || a.cl - b.cl);
      rs.slice(1).forEach(r => entre.push(r.en));   // el primer cliente de cada observación no tiene intervalo previo
    });
    const mEn = media(entre), mSM = media(M.map(r => r.se)), mSC = media(C.map(r => r.se));
    const lam = 1 / mEn, mu1 = 1 / mSM, mu2 = 1 / mSC;
    return {
      nM: M.length, nC: C.length, mEn: mEn, mSM: mSM, mSC: mSC, lam: lam, mu1: mu1, mu2: mu2,
      rho1: lam / (NUM_EMP * mu1), rho2: lam / mu2, eM: media(M.map(r => r.es)), eC: media(C.map(r => r.es))
    };
  }
  function construyeTraza(id) {
    const rs = BD.mostrador.filter(r => r.o === id).sort((a, b) => tmin(a.ll) - tmin(b.ll) || a.cl - b.cl);
    if (!rs.length) return { items: [], base: 360 };
    const base = tmin(rs[0].ll), cj = {};
    BD.caja.filter(r => r.o === id).forEach(r => { cj[r.cl] = r.se; });
    return { items: rs.map(r => ({ t: tmin(r.ll) - base, cl: r.cl, sM: Math.max(0, r.se), sC: cj[r.cl] != null ? Math.max(0, cj[r.cl]) : 1 })), base: base };
  }

  // Teoría 
  function teoria(lam, mu1, mu2, s = NUM_EMP) {
    const a = lam / mu1;
    if (lam >= s * mu1 || lam >= mu2) return null;
    const rho1 = lam / (s * mu1);
    let sum = 0; for (let n = 0; n < s; n++) sum += Math.pow(a, n) / fact(n);
    const p0 = 1 / (sum + (Math.pow(a, s) / fact(s)) * (s / (s - a)));
    const pw1 = Math.pow(a, s) / (fact(s) * (1 - rho1)) * p0;           // Erlang C
    const lq1 = Math.pow(a, s + 1) / (fact(s - 1) * Math.pow(s - a, 2)) * p0;
    const wq1 = lq1 / lam, w1 = wq1 + 1 / mu1, l1 = lam * w1;
    const rho2 = lam / mu2, lq2 = rho2 * rho2 / (1 - rho2), wq2 = lq2 / lam, w2 = wq2 + 1 / mu2, l2 = lam * w2;
    return { rho1, pw1, lq1, wq1, w1, l1, rho2, pw2: rho2, lq2, wq2, w2, l2, wq: wq1 + wq2, w: w1 + w2, l: lam * (w1 + w2), x: lam };
  }

  // Motor de simulación (eventos exactos) 
  class Sim {
    constructor() {
      this.lam = 0.409; this.mu1 = 0.159; this.mu2 = 0.567; this.modo = 'exp'; this.datosM = []; this.datosC = [];
      this.traza = []; this.horaBase = 360; this.obsId = 1; this.reiniciar();
    } // reinicia la simulación
    reiniciar() {
      this.terminado = false; this.reloj = 0; this.iTraza = 0;
      this.sigLlegada = (this.modo === 'traza' && this.traza.length) ? this.traza[0].t : expo(this.lam);
      this.cola1 = []; this.cola2 = []; this.emp = Array(NUM_EMP).fill(null); this.caja = null;
      this.llegadas = 0; this.atendidos = 0;
      this.e1 = { n: 0, s: 0, pos: 0, max: 0 }; this.e2 = { n: 0, s: 0, pos: 0, max: 0 };   // esperas en fila
      this.t1 = { n: 0, s: 0 }; this.t2 = { n: 0, s: 0 }; this.ts = { n: 0, s: 0 };          // fila + servicio
      this.aq1 = this.aq2 = this.aOcup = this.aCaja = this.aSis = 0;
      this.nuevos = []; this.muestras = [[0, 0, 0]]; this.ultM = 0; this.registro = [];
    }
    // Tiempo de servicio (mostrador o caja) según el modo de simulación
    tMostrador(c) { if (this.modo === 'traza') return c.sM; return this.modo === 'emp' ? pick(this.datosM) : expo(this.mu1); }
    tCaja(c) { if (this.modo === 'traza') return c.sC; return this.modo === 'emp' ? pick(this.datosC) : expo(this.mu2); }
    acumular(t) {
      const dt = t - this.reloj;
      this.aq1 += this.cola1.length * dt; this.aq2 += this.cola2.length * dt;
      this.aOcup += this.emp.filter(Boolean).length * dt; this.aCaja += (this.caja ? 1 : 0) * dt;
      this.aSis += (this.llegadas - this.atendidos) * dt; this.reloj = t;
    }// actualiza los acumuladores de tiempo
    anota(o, v) { o.n++; o.s += v; if (v > 1e-9) o.pos++; if (v > o.max) o.max = v; }
    asignar() {
      for (let i = 0; i < NUM_EMP; i++) {
        if (!this.emp[i] && this.cola1.length) {
          const c = this.cola1.shift(); c.estado = 'mostrador'; c.puesto = i; c.esp1 = this.reloj - c.llegada;
          this.anota(this.e1, c.esp1); this.emp[i] = [c, this.reloj + this.tMostrador(c)];
        }
      }
      if (!this.caja && this.cola2.length) {
        const c = this.cola2.shift(); c.estado = 'caja'; c.esp2 = this.reloj - c.llego2;
        this.anota(this.e2, c.esp2); this.caja = [c, this.reloj + this.tCaja(c)];
      }
    }// asigna clientes a mostradores y caja si hay disponibles
    muestrear() {
      if (this.reloj - this.ultM >= 0.25) {
        this.muestras.push([this.reloj, this.cola1.length, this.cola2.length]); this.ultM = this.reloj;
        if (this.muestras.length > 3000) this.muestras.splice(0, 1000);
      }
    }// guarda el estado de las colas cada 0.25 minutos
    avanzar(dt) {
      if (this.terminado) return;
      const objetivo = this.reloj + dt;
      for (; ;) {
        let t = this.sigLlegada, tipo = 'llegada', idx = -1;
        this.emp.forEach((e, i) => { if (e && e[1] < t) { t = e[1]; tipo = 'fin1'; idx = i; } });
        if (this.caja && this.caja[1] < t) { t = this.caja[1]; tipo = 'fin2'; }
        if (t > objetivo) break;
        this.acumular(t);
        if (tipo === 'llegada') {
          this.llegadas++;
          const c = { id: this.llegadas, llegada: t, estado: 'cola1' };
          if (this.modo === 'traza') {
            const it = this.traza[this.iTraza++]; c.id = it.cl; c.sM = it.sM; c.sC = it.sC;
            this.sigLlegada = this.iTraza < this.traza.length ? this.traza[this.iTraza].t : Infinity;
          } else this.sigLlegada = t + expo(this.lam);
          this.cola1.push(c); this.nuevos.push(c);
        } else if (tipo === 'fin1') {
          const c = this.emp[idx][0]; this.emp[idx] = null; c.estado = 'cola2'; c.llego2 = t;
          this.t1.n++; this.t1.s += t - c.llegada; this.cola2.push(c);
        } else {
          const c = this.caja[0]; this.caja = null; c.estado = 'salida'; this.atendidos++;
          this.t2.n++; this.t2.s += t - c.llego2; this.ts.n++; this.ts.s += t - c.llegada;
          this.registro.unshift({ id: c.id, llegada: c.llegada, esp1: c.esp1 || 0, esp2: c.esp2 || 0, total: t - c.llegada });
          if (this.registro.length > 8) this.registro.length = 8;
        }
        this.asignar(); this.muestrear();
        if (this.modo === 'traza' && this.iTraza >= this.traza.length && this.atendidos === this.llegadas) { this.terminado = true; return; }
      }
      this.acumular(objetivo);
    }// avanza la simulación hasta reloj + dt, procesando todos los eventos intermedios
    metricas() {
      const T = this.reloj; if (T <= 0) return null;
      const m = o => o.n ? o.s / o.n : 0, lq1 = this.aq1 / T, lq2 = this.aq2 / T;
      return {
        rho1: this.aOcup / (NUM_EMP * T), pw1: this.e1.n ? this.e1.pos / this.e1.n : 0, lq1, wq1: m(this.e1), wmax1: this.e1.max,
        w1: m(this.t1), l1: lq1 + this.aOcup / T,
        rho2: this.aCaja / T, pw2: this.e2.n ? this.e2.pos / this.e2.n : 0, lq2, wq2: m(this.e2), wmax2: this.e2.max,
        w2: m(this.t2), l2: lq2 + this.aCaja / T,
        wq: m(this.e1) + m(this.e2), w: m(this.ts), l: this.aSis / T, x: this.atendidos / T
      };
    }
  }

  // Estado de la página
  const sim = new Sim();
  let teo = null, corriendo = false, pausa = false, vivos = [], speed = 4, nLog = -1, E = null;

  // ---------- Escena 3D 
  function crearEscena() {
    if (typeof THREE === 'undefined') return null;
    const canvas = $('stage'), cont = $('stage3d');
    let renderer;
    try { renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true }); } catch (e) { return null; }
    renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1));
    renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    const scene = new THREE.Scene(); scene.background = new THREE.Color(0xdfe8ef);
    const camera = new THREE.PerspectiveCamera(45, 16 / 9, 0.1, 300);

    scene.add(new THREE.HemisphereLight(0xffffff, 0xb8c4cf, 0.72));
    const sun = new THREE.DirectionalLight(0xffffff, 0.62); sun.position.set(-12, 28, 16); sun.castShadow = true;
    sun.shadow.mapSize.set(2048, 2048);
    const sc = sun.shadow.camera; sc.left = -28; sc.right = 28; sc.top = 22; sc.bottom = -22; sc.near = 1; sc.far = 80;
    scene.add(sun);

    const mat = (c, r) => new THREE.MeshStandardMaterial({ color: c, roughness: r == null ? 0.75 : r, metalness: 0.05 });
    function caja3(w, h, d, x, y, z, color, sombra) {
      const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat(color));
      m.position.set(x, y, z); m.castShadow = sombra !== false; m.receiveShadow = true; scene.add(m); return m;
    }// crea un cubo y lo agrega a la escena
    function rr(x, a, b, w, h, r) { x.beginPath(); x.moveTo(a + r, b); x.arcTo(a + w, b, a + w, b + h, r); x.arcTo(a + w, b + h, a, b + h, r); x.arcTo(a, b + h, a, b, r); x.arcTo(a, b, a + w, b, r); x.closePath(); }
    function textura(t, w, h, font, color, bg) {
      const c = document.createElement('canvas'); c.width = w; c.height = h; const x = c.getContext('2d');
      if (bg) { x.fillStyle = bg; rr(x, 0, 0, w, h, h * 0.22); x.fill(); }
      x.fillStyle = color; x.font = font; x.textAlign = 'center'; x.textBaseline = 'middle'; x.fillText(t, w / 2, h / 2 + 2);
      const tx = new THREE.CanvasTexture(c); tx.anisotropy = 4; return tx;
    }// crea una textura con texto y fondo redondeado
    function etiqueta(t, ancho, alto, color, bg, x, y, z) {
      const tx = textura(t, Math.round(ancho * 128), Math.round(alto * 128), '700 ' + Math.round(alto * 128 * 0.5) + 'px Arial, sans-serif', color, bg);
      const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: tx, transparent: true, depthWrite: false }));
      s.scale.set(ancho, alto, 1); s.position.set(x, y, z); scene.add(s); return s;
    }// crea un sprite con texto y fondo redondeado
    function suelo(t, ancho, alto, color, x, z) {
      const tx = textura(t, Math.round(ancho * 100), Math.round(alto * 100), '700 ' + Math.round(alto * 100 * 0.62) + 'px Arial, sans-serif', color, null);
      const m = new THREE.Mesh(new THREE.PlaneGeometry(ancho, alto), new THREE.MeshBasicMaterial({ map: tx, transparent: true, depthWrite: false }));
      m.rotation.x = -Math.PI / 2; m.position.set(x, 0.04, z); scene.add(m);
    }

    // Piso, exterior y pared
    const cv = document.createElement('canvas'); cv.width = cv.height = 128; const g = cv.getContext('2d');
    g.fillStyle = '#ece3cf'; g.fillRect(0, 0, 128, 128); g.fillStyle = '#e2d7bd'; g.fillRect(0, 0, 64, 64); g.fillRect(64, 64, 64, 64);
    const tex = new THREE.CanvasTexture(cv); tex.wrapS = tex.wrapT = THREE.RepeatWrapping; tex.repeat.set(23, 14);
    const piso = new THREE.Mesh(new THREE.PlaneGeometry(46, 28), new THREE.MeshStandardMaterial({ map: tex, roughness: 0.9 }));
    piso.rotation.x = -Math.PI / 2; piso.position.z = 2; piso.receiveShadow = true; scene.add(piso);
    const ext = new THREE.Mesh(new THREE.PlaneGeometry(150, 100), mat(0xb9c6b2, 1)); ext.rotation.x = -Math.PI / 2; ext.position.y = -0.05; ext.receiveShadow = true; scene.add(ext);
    caja3(46, 4, 0.3, 0, 2, -12.15, 0xe8e0cf, false);
    const letrero = new THREE.Mesh(new THREE.PlaneGeometry(14, 2.2),
      new THREE.MeshBasicMaterial({ map: textura('CHARCUTERÍA LILI', 1792, 282, '700 150px Arial, sans-serif', '#19375a', '#fff3d6') }));
    letrero.position.set(0, 2.6, -11.95); scene.add(letrero);

    // Mostrador, vitrina y balanzas
    caja3(1.0, 1.1, 16.8, X_BAR, 0.55, 0, 0x7fb2dd);
    caja3(1.25, 0.1, 16.8, X_BAR, 1.15, 0, 0xd5e7f5);
    caja3(0.8, 2.2, 20.2, 0.6, 1.1, 1.8, 0xc9d6e2);
    [0.6, 1.2, 1.8].forEach(y => caja3(0.06, 0.06, 20, 0.17, y, 1.8, 0xffffff, false));
    const balanzas = Z_EMP.map(z => caja3(0.5, 0.16, 0.5, X_BAR, 1.28, z, 0x555b63));

    // Caja de pago: continúa el mostrador, al lado del empleado 3
    caja3(1.0, 1.1, 3.4, X_BAR, 0.55, Z_CAJA, 0xe3a95a);
    caja3(1.25, 0.1, 3.4, X_BAR, 1.15, Z_CAJA, 0xf5dfb8);
    caja3(0.5, 0.4, 0.6, X_BAR, 1.4, Z_CAJA, 0x333a42);

    // Personas
    const matPiel = mat(0xf0c8a0, 0.8);
    const matEmpOn = mat(0x1f6fc4, 0.6), matEmpOff = mat(0x7d8fa3, 0.8), matCajOn = mat(0xd9822b, 0.6), matCajOff = mat(0xa89886, 0.8);
    function persona(matCuerpo, x, z) {
      const grp = new THREE.Group();
      const b = new THREE.Mesh(new THREE.CylinderGeometry(0.3, 0.38, 1.1, 16), matCuerpo); b.position.y = 0.55; b.castShadow = true; grp.add(b);
      const h = new THREE.Mesh(new THREE.SphereGeometry(0.27, 16, 12), matPiel); h.position.y = 1.38; h.castShadow = true; grp.add(h);
      const gorro = new THREE.Mesh(new THREE.CylinderGeometry(0.24, 0.26, 0.2, 14), mat(0xffffff, 0.7)); gorro.position.y = 1.68; gorro.castShadow = true; grp.add(gorro);
      [-0.34, 0.34].forEach(dx => { const br = new THREE.Mesh(new THREE.CylinderGeometry(0.07, 0.06, 0.55, 8), matPiel); br.position.set(dx, 0.85, 0.08); br.rotation.x = -0.5; br.castShadow = true; grp.add(br); });
      const pelo = new THREE.Mesh(new THREE.SphereGeometry(0.28, 12, 8, 0, Math.PI * 2, 0, Math.PI * 0.5), mat(0x3a2616, 0.9)); pelo.position.set(0, 1.4, -0.02); grp.add(pelo);
      grp.position.set(x, 0, z); scene.add(grp); grp.userData.body = b; return grp;
    }
    const empleados = Z_EMP.map(z => persona(matEmpOff, X_EMPL, z));
    const cajero = persona(matCajOff, X_EMPL, Z_CAJA);

    // Etiquetas
    const etiqEmp = Z_EMP.map((z, i) => etiqueta('Empleado ' + (i + 1), 3.2, 0.72, '#ffffff', 'rgba(20,80,144,0.92)', X_EMPL, 2.75, z));
    etiqueta('Cajero', 2.2, 0.72, '#ffffff', 'rgba(160,85,20,0.94)', X_EMPL, 2.75, Z_CAJA);
    etiqueta('ENTRADA', 2.8, 0.7, '#14202e', 'rgba(255,255,255,0.88)', X_ENT, 2.4, 0);
    etiqueta('SALIDA', 2.4, 0.7, '#14202e', 'rgba(255,255,255,0.88)', X_SAL - 1, 2.4, Z_SALIDA);
    suelo('FILA DEL MOSTRADOR', 8, 1, '#566677', -10.6, -1.6);
    suelo('FILA DE LA CAJA', 6.4, 1, '#566677', -8.6, Z_CAJA + 1.9);

    // Clientes
    // Clientes: cuerpo, piernas, brazos, cabeza y pelo; cada uno con tono de piel, pelo y pantalón distintos
    const gPierna = new THREE.CylinderGeometry(0.09, 0.075, 0.55, 8), gBrazo = new THREE.CylinderGeometry(0.07, 0.055, 0.5, 8);
    const gTorso = new THREE.CylinderGeometry(0.25, 0.2, 0.62, 12), gCab = new THREE.SphereGeometry(0.17, 14, 10);
    const gPelo = new THREE.SphereGeometry(0.185, 12, 8, 0, Math.PI * 2, 0, Math.PI * 0.55);
    const matsC = {}; Object.keys(COLORES).forEach(k => { matsC[k] = mat(COLORES[k], 0.6); });
    const pieles = [0xf1c9a5, 0xe0a97c, 0xc68a5c, 0x8d5a3b, 0x6b4226].map(c => mat(c, 0.8));
    const pelos = [0x2a1b12, 0x4a2f1c, 0x1c1c1c, 0x8a6a3a, 0x777777, 0xb5482a].map(c => mat(c, 0.9));
    const pantalones = [0x2f3a4a, 0x3d3d3d, 0x4a3a2a, 0x1f2d44, 0x5a5f66].map(c => mat(c, 0.8));
    const rnd = (id, k) => { const v = Math.sin(id * 12.9898 + k * 78.233) * 43758.5453; return v - Math.floor(v); };
    function nuevoCliente(id) {
      const grp = new THREE.Group(), piel = pieles[Math.floor(rnd(id, 1) * pieles.length)], pant = pantalones[Math.floor(rnd(id, 2) * pantalones.length)];
      const parte = (g, m, x, y, z, pivY) => { const pv = new THREE.Group(); pv.position.set(x, pivY, z); const me = new THREE.Mesh(g, m); me.position.y = y; me.castShadow = true; pv.add(me); grp.add(pv); return pv; };
      const pL = parte(gPierna, pant, -0.11, -0.27, 0, 0.55), pR = parte(gPierna, pant, 0.11, -0.27, 0, 0.55);
      const aL = parte(gBrazo, piel, -0.3, -0.22, 0, 1.12), aR = parte(gBrazo, piel, 0.3, -0.22, 0, 1.12);
      const b = new THREE.Mesh(gTorso, matsC.cola1); b.position.y = 0.86; b.castShadow = true; grp.add(b);
      const h = new THREE.Mesh(gCab, piel); h.position.y = 1.32; h.castShadow = true; grp.add(h);
      const pe = new THREE.Mesh(gPelo, pelos[Math.floor(rnd(id, 3) * pelos.length)]); pe.position.y = 1.34; grp.add(pe);
      grp.scale.setScalar(0.9 + rnd(id, 4) * 0.2);
      scene.add(grp); grp.userData.b = b; grp.userData.p = [pL, pR, aL, aR]; return grp;
    }// crea un cliente con id único, asignando aleatoriamente piel, pelo y pantalón según el id
    function sync(lista, t) {
      lista.forEach(c => {
        if (!c.mesh) c.mesh = nuevoCliente(c.id);
        const bob = c.mov ? Math.abs(Math.sin(t * 10 + c.id)) * 0.05 : 0;
        c.mesh.position.set(c.x, bob, c.z);
        c.mesh.rotation.y = c.mov && c.ang !== undefined ? c.ang : Math.PI / 2;
        const w = c.mov ? Math.sin(t * 10 + c.id) * 0.7 : 0, p = c.mesh.userData.p;
        p[0].rotation.x = w; p[1].rotation.x = -w; p[2].rotation.x = -w * 0.8; p[3].rotation.x = w * 0.8;
        c.mesh.userData.b.material = matsC[c.estado] || matsC.cola1;
      });
    } // sincroniza la posición y animación de los clientes en la escena
    function quita(c) { if (c.mesh) { scene.remove(c.mesh); c.mesh = null; } }
    function estados() {
      empleados.forEach((e, i) => { const on = i < NUM_EMP; e.visible = on; etiqEmp[i].visible = on; balanzas[i].visible = on; if (on) e.userData.body.material = sim.emp[i] ? matEmpOn : matEmpOff; });
      cajero.userData.body.material = sim.caja ? matCajOn : matCajOff;
    }

    // Cámara orbital propia
    const PRE = {
      general: { tx: 0, ty: 0, tz: 3, r: 33, th: -0.42, ph: 0.95 },
      aerea: { tx: 0, ty: 0, tz: 2, r: 36, th: 0, ph: 0.06 },
      mostrador: { tx: -3, ty: 0.8, tz: 0, r: 20, th: -0.65, ph: 1.05 },
      caja: { tx: -5, ty: 0.8, tz: 10, r: 15, th: -0.6, ph: 1.05 }
    };
    const cam = Object.assign({}, PRE.general), goal = Object.assign({}, PRE.general);
    function marcaCam(k) { document.querySelectorAll('#camtools .btn').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.cam === k))); }
    function setCam(k) { if (PRE[k]) { Object.assign(goal, PRE[k]); marcaCam(k); } }
    function pan(dx, dy) {
      const s = goal.r * 0.0016, rx = Math.cos(goal.th), rz = -Math.sin(goal.th), fx = -Math.sin(goal.th), fz = -Math.cos(goal.th);
      goal.tx += -rx * dx * s + fx * dy * s; goal.tz += -rz * dx * s + fz * dy * s;
      goal.tx = clamp(goal.tx, -25, 25); goal.tz = clamp(goal.tz, -14, 18);
    }
    const ptrs = new Map();
    canvas.addEventListener('pointerdown', e => { canvas.setPointerCapture(e.pointerId); ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY }); marcaCam(''); });
    canvas.addEventListener('pointermove', e => {
      const p = ptrs.get(e.pointerId); if (!p) return;
      const dx = e.clientX - p.x, dy = e.clientY - p.y;
      if (ptrs.size === 1) {
        if (e.shiftKey || e.ctrlKey || (e.buttons & 2)) pan(dx, dy);
        else { goal.th -= dx * 0.006; goal.ph = clamp(goal.ph - dy * 0.006, 0.05, 1.5); }
      } else if (ptrs.size === 2) {
        const ids = Array.from(ptrs.keys()), a = ptrs.get(ids[0]), b = ptrs.get(ids[1]);
        const d0 = Math.hypot(a.x - b.x, a.y - b.y);
        p.x = e.clientX; p.y = e.clientY;
        const d1 = Math.hypot(a.x - b.x, a.y - b.y);
        if (d0 > 0 && d1 > 0) goal.r = clamp(goal.r * d0 / d1, 8, 70);
        return;
      }
      p.x = e.clientX; p.y = e.clientY;
    });
    const suelta = e => { ptrs.delete(e.pointerId); };
    canvas.addEventListener('pointerup', suelta); canvas.addEventListener('pointercancel', suelta);
    canvas.addEventListener('contextmenu', e => e.preventDefault());
    canvas.addEventListener('wheel', e => { e.preventDefault(); goal.r = clamp(goal.r * Math.exp(e.deltaY * 0.0012), 8, 70); marcaCam(''); }, { passive: false });
    $('camtools').addEventListener('click', e => { const b = e.target.closest('button[data-cam]'); if (b) setCam(b.dataset.cam); });
    //    3D: ajusta tamaño del canvas y cámara al contenedor
    function ajusta() {
      const w = cont.clientWidth, h = cont.clientHeight; if (!w || !h) return;
      renderer.setSize(w, h, false); camera.aspect = w / h; camera.updateProjectionMatrix();
    }
    if (window.ResizeObserver) new ResizeObserver(ajusta).observe(cont); else window.addEventListener('resize', ajusta);
    ajusta();
    //    3D: renderiza la escena y mueve la cámara suavemente hacia la posición objetivo
    function render(dt) {
      const k = 1 - Math.exp(-dt * 9);
      ['tx', 'ty', 'tz', 'r', 'th', 'ph'].forEach(p => { cam[p] += (goal[p] - cam[p]) * k; });
      const sp = Math.sin(cam.ph);
      camera.position.set(cam.tx + cam.r * sp * Math.sin(cam.th), cam.ty + cam.r * Math.cos(cam.ph), cam.tz + cam.r * sp * Math.cos(cam.th));
      camera.lookAt(cam.tx, cam.ty, cam.tz);
      renderer.render(scene, camera);
    }
    return { render: render, sync: sync, quita: quita, estados: estados };
  }

  // Movimiento de los clientes 
  function objetivos() {
    sim.cola1.forEach((c, i) => { const p = posCola1(i); c.tx = p[0]; c.tz = p[1]; });
    sim.cola2.forEach((c, i) => { const p = posCola2(i); c.tx = p[0]; c.tz = p[1]; });
    sim.emp.forEach((e, i) => { if (e) { e[0].tx = X_SERV; e[0].tz = Z_EMP[i]; } });
    if (sim.caja) { sim.caja[0].tx = X_CLI_CAJA; sim.caja[0].tz = Z_CAJA; }
  }// actualiza los objetivos de posición de todos los clientes según su estado
  function mueveClientes(dt) {
    sim.nuevos.forEach(c => { c.x = X_ENT; c.z = 0; c.wps = []; c.est0 = 'cola1'; c.lane = false; c.sale = false; c.mov = false; vivos.push(c); });
    sim.nuevos.length = 0;
    objetivos();
    vivos = vivos.filter(c => {
      if (c.estado !== c.est0) {
        if (!c.lane && (c.estado === 'cola2' || c.estado === 'caja' || c.estado === 'salida')) {
          c.lane = true; c.wps = [[LANE_X, c.z]];   // sale al pasillo del lado de los clientes
        }
        if (c.estado === 'salida') { c.wps.push([X_CLI_CAJA, Z_SALIDA], [X_SAL, Z_SALIDA]); c.sale = true; }
        c.est0 = c.estado;
      }
      if (c.sale && c.wps.length === 0) { if (E) E.quita(c); return false; }
      let tx, tz, interm = false;
      if (c.wps.length) { tx = c.wps[0][0]; tz = c.wps[0][1]; interm = true; } else { tx = c.tx; tz = c.tz; }
      c.mov = false;
      if (tx === undefined || tz === undefined) return true;
      const dx = tx - c.x, dz = tz - c.z, d = Math.hypot(dx, dz);
      if (interm && d < 0.3) { c.wps.shift(); }
      else if (d > 0.001) {
        const v = clamp(d * 4, 3.5, 30), st = Math.min(d, v * dt);
        c.x += dx / d * st; c.z += dz / d * st; c.mov = st > 0.002; c.ang = Math.atan2(dx, dz);
      }
      return true;
    });
    if (E) E.sync(vivos, performance.now() / 1000);
  }

  // Panel de rendimiento 
  const FILAS1 = [['Utilización ρ', 'rho1'], ['Prob. de esperar', 'pw1'], ['Lq clientes en fila', 'lq1'], ['Wq espera en fila (min)', 'wq1'],
  ['Wq máxima (min)', 'wmax1'], ['W fila + servicio (min)', 'w1'], ['L clientes en total', 'l1']];
  const FILAS2 = [['Utilización ρ', 'rho2'], ['Prob. de esperar', 'pw2'], ['Lq clientes en fila', 'lq2'], ['Wq espera en fila (min)', 'wq2'],
  ['Wq máxima (min)', 'wmax2'], ['W fila + servicio (min)', 'w2'], ['L clientes en total', 'l2']];
  const FILAS3 = [['Wq total (min)', 'wq'], ['W total en tienda (min)', 'w'], ['L clientes en tienda', 'l'], ['Atendidos por minuto', 'x']];
  function armaTabla(id, filas) {
    $(id).innerHTML = filas.map(f => '<tr><td>' + f[0] + '</td><td data-t="' + f[1] + '">—</td><td data-s="' + f[1] + '">—</td></tr>').join('');
  }// arma las tablas de métricas teóricas y simuladas
  function llenaTabla(id, sm) {
    const tb = $(id);
    tb.querySelectorAll('[data-t]').forEach(td => { td.textContent = teo && teo[td.dataset.t] != null ? fmt(teo[td.dataset.t]) : '—'; });
    tb.querySelectorAll('[data-s]').forEach(td => { td.textContent = sm ? fmt(sm[td.dataset.s]) : '—'; });
  }// llena las tablas de métricas teóricas y simuladas
  function actualizaPanel() {
    const sm = corriendo ? sim.metricas() : null, traza = sim.modo === 'traza';
    llenaTabla('tb1', sm); llenaTabla('tb2', sm); llenaTabla('tb3', sm);
    const bd = $('badge');
    if (corriendo) {
      const oc = sim.emp.filter(Boolean).length;
      $('now1').textContent = 'Ahora: fila ' + sim.cola1.length + ' · empleados ocupados ' + oc + '/' + NUM_EMP;
      $('now2').textContent = 'Ahora: fila ' + sim.cola2.length + ' · cajero ' + (sim.caja ? 'ocupado' : 'libre');
      $('now3').textContent = (traza ? 'Hora ' + hhmm(sim.horaBase + sim.reloj) : 'Reloj ' + fmt(sim.reloj, 1) + ' min') + ' · llegadas ' + sim.llegadas + ' · pagaron ' + sim.atendidos;
      bd.hidden = false; bd.textContent = traza ? 'Obs. ' + sim.obsId + ' · ' + hhmm(sim.horaBase + sim.reloj) : 'Reloj ' + fmt(sim.reloj, 1) + ' min';
    } else { ['now1', 'now2', 'now3'].forEach(i => { $(i).textContent = ''; }); bd.hidden = true; }
    $('unstable').hidden = !(corriendo && !teo);
    $('unstable').textContent = 'Parámetros inestables (λ ≥ ' + NUM_EMP + '·μ1 o λ ≥ μ2): las filas crecen sin límite y no existe solución teórica.';
    const h = $('hint');
    if (corriendo && sim.terminado) { h.textContent = 'Observación ' + sim.obsId + ' reproducida completa: compara los valores simulados con la teoría y con las esperas observadas en la base de datos.'; h.hidden = false; }
    else if (corriendo) { h.hidden = true; }
    if (sim.atendidos !== nLog) {
      nLog = sim.atendidos; const tb = $('log');
      tb.innerHTML = sim.registro.length ? sim.registro.map(r => '<tr><td>#' + r.id + '</td><td>' + (traza ? hhmm(sim.horaBase + r.llegada) : fmt(r.llegada, 1)) + '</td><td>' + fmt(r.esp1, 1) + '</td><td>' + fmt(r.esp2, 1) + '</td><td>' + fmt(r.total, 1) + '</td></tr>').join('')
        : '<tr><td colspan="5" style="text-align:left;color:var(--muted)">Aún no ha pagado nadie.</td></tr>';
    }
    dibujaGrafico();
  }

  // Gráfico de la fila 
  const chart = $('chart'), cg = chart.getContext('2d');
  const SANS = 'Barlow, Arial, sans-serif';
  function dibujaGrafico() {// dibuja el gráfico de la fila de clientes 
    const dpr = Math.min(2, window.devicePixelRatio || 1), w = chart.clientWidth, h = chart.clientHeight; if (!w) return;
    if (chart.width !== Math.round(w * dpr)) { chart.width = Math.round(w * dpr); chart.height = Math.round(h * dpr); }
    cg.setTransform(dpr, 0, 0, dpr, 0, 0); cg.clearRect(0, 0, w, h);
    const cs = getComputedStyle(document.documentElement), css = n => cs.getPropertyValue(n).trim();
    const t1 = Math.max(VENTANA, sim.reloj), t0 = t1 - VENTANA, pts = sim.muestras.filter(p => p[0] >= t0);
    let maxq = 5; pts.forEach(p => { maxq = Math.max(maxq, p[1], p[2]); });
    if (corriendo && teo) maxq = Math.max(maxq, teo.lq1 * 1.3, teo.lq2 * 1.3);
    maxq = Math.ceil(maxq / 5) * 5;
    const pl = 30, pr = 8, pt = 8, pb = 18, X = t => pl + (t - t0) / VENTANA * (w - pl - pr), Y = q => h - pb - q / maxq * (h - pt - pb);
    cg.font = '11px ' + SANS; cg.textBaseline = 'middle'; cg.lineWidth = 1;
    for (let i = 0; i <= 2; i++) {
      const q = maxq * i / 2, y = Y(q);
      cg.strokeStyle = css('--line'); cg.beginPath(); cg.moveTo(pl, y); cg.lineTo(w - pr, y); cg.stroke();
      cg.fillStyle = css('--muted'); cg.textAlign = 'right'; cg.fillText(String(Math.round(q * 10) / 10), pl - 5, y);
    }
    cg.fillStyle = css('--muted'); cg.textBaseline = 'alphabetic';
    cg.textAlign = 'left'; cg.fillText(Math.round(t0) + ' min', pl, h - 4);
    cg.textAlign = 'right'; cg.fillText(Math.round(t1) + ' min', w - pr, h - 4);
    if (corriendo && teo) {
      cg.setLineDash([5, 4]); cg.lineWidth = 1.5;
      [['lq1', '--s1'], ['lq2', '--s2']].forEach(p => { cg.strokeStyle = css(p[1]); cg.beginPath(); cg.moveTo(pl, Y(teo[p[0]])); cg.lineTo(w - pr, Y(teo[p[0]])); cg.stroke(); });
      cg.setLineDash([]);
    }
    [[1, '--s1'], [2, '--s2']].forEach(p => {
      if (pts.length < 2) return;
      cg.strokeStyle = css(p[1]); cg.lineWidth = 2; cg.beginPath();
      pts.forEach((q, j) => { const x = X(q[0]), y = Y(q[p[0]]); j ? cg.lineTo(x, y) : cg.moveTo(x, y); }); cg.stroke();
    });
  }

  // Base de datos: pantalla
  const COLS_M = [['Obs', 'o'], ['Cliente', 'cl'], ['Llegada', 'll'], ['Entre llegadas', 'en'], ['Servidor', 'sv'], ['Inicio', 'ini'], ['Fin', 'fin'], ['Servicio (min)', 'se'], ['Espera (min)', 'es']];
  const COLS_C = [['Obs', 'o'], ['Cliente', 'cl'], ['Llegada', 'll'], ['Entre llegadas', 'en'], ['Inicio', 'ini'], ['Fin', 'fin'], ['Servicio (min)', 'se'], ['Espera (min)', 'es']];
  const chip = (v, t, on) => '<button type="button" class="chip" data-o="' + v + '" aria-pressed="' + on + '">' + t + '</button>';
  function poblarSelObs() { // llena los select de observación en el formulario de agregar registro
    ['inObs', 'addObs'].forEach(id => {
      const s = $(id), prev = s.value;
      s.innerHTML = BD.obs.map(o => '<option value="' + o.id + '">' + o.nombre + '</option>').join('');
      if (prev && BD.obs.some(o => String(o.id) === prev)) s.value = prev;
    });
  }
  function renderDB() {// renderiza la pantalla de base de datos
    if (ui.obs !== 'all' && !BD.obs.some(o => o.id === ui.obs)) ui.obs = 'all';
    $('segObs').innerHTML = chip('all', 'Todas', ui.obs === 'all') + BD.obs.map(o => chip(o.id, 'Obs. ' + o.id, ui.obs === o.id)).join('') + '<button type="button" class="chip nuevo" data-o="nueva">+ Nueva</button>';
    $('segTabla').querySelectorAll('.chip').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.t === ui.tabla)));
    $('btnDelObs').hidden = ui.obs === 'all';
    $('lblSv').hidden = ui.tabla !== 'M';
    const st = estadisticas(ui.obs);
    const items = [
      [st.nM + ' · ' + st.nC, 'clientes en mostrador · caja'],
      [fmt(st.mEn, 3), 'min entre llegadas (λ = ' + fmt(st.lam, 3) + ' /min)'],
      [fmt(st.mSM, 3), 'min de servicio por empleado (μ₁ = ' + fmt(st.mu1, 3) + ' /min)'],
      [fmt(st.mSC, 3), 'min de servicio en caja (μ₂ = ' + fmt(st.mu2, 3) + ' /min)'],
      [fmt(st.rho1, 2) + ' · ' + fmt(st.rho2, 2), 'ρ estimada: mostrador · caja'],
      [fmt(st.eM, 2) + ' · ' + fmt(st.eC, 2), 'espera media observada (min): mostrador · caja']
    ];
    $('dbStats').innerHTML = items.map(i => '<div class="stat"><b>' + i[0] + '</b><span>' + i[1] + '</span></div>').join('');
    const cols = ui.tabla === 'M' ? COLS_M : COLS_C, key = ui.tabla === 'M' ? 'mostrador' : 'caja';
    $('dbTabla').querySelector('thead').innerHTML = '<tr>' + cols.map(c => '<th>' + c[0] + '</th>').join('') + '<th></th></tr>';
    const filas = [];
    BD[key].forEach((r, i) => { if (ui.obs === 'all' || r.o === ui.obs) filas.push('<tr>' + cols.map(c => '<td>' + r[c[1]] + '</td>').join('') + '<td><button type="button" class="del" data-i="' + i + '" aria-label="Eliminar registro">✕</button></td></tr>'); });
    $('dbTabla').querySelector('tbody').innerHTML = filas.length ? filas.join('') : '<tr><td colspan="' + (cols.length + 1) + '" style="color:var(--muted)">Sin registros.</td></tr>';
    poblarSelObs();
  }
  function errAdd(m) { const e = $('errAdd'); e.textContent = m; e.hidden = !m; } // muestra un mensaje de error en el formulario de agregar registro
  $('segObs').addEventListener('click', e => {
    const b = e.target.closest('button[data-o]'); if (!b) return;
    const v = b.dataset.o;
    if (v === 'nueva') {
      const id = BD.obs.reduce((m, o) => Math.max(m, o.id), 0) + 1;
      BD.obs.push({ id: id, nombre: 'Observación ' + id }); ui.obs = id; guardaBD();
    } else ui.obs = v === 'all' ? 'all' : +v;
    renderDB();
  });
  $('segTabla').addEventListener('click', e => { const b = e.target.closest('button[data-t]'); if (b) { ui.tabla = b.dataset.t; renderDB(); } });
  $('dbTabla').addEventListener('click', e => {
    const b = e.target.closest('button.del'); if (!b) return;
    BD[ui.tabla === 'M' ? 'mostrador' : 'caja'].splice(+b.dataset.i, 1); guardaBD(); renderDB();
  });
  $('formAdd').addEventListener('submit', e => {
    e.preventDefault();
    const o = +$('addObs').value, cl = parseInt($('addCl').value, 10);
    const ll = tmin($('addLl').value), ini = tmin($('addIni').value), fin = tmin($('addFin').value);
    if (!isFinite(o) || !isFinite(cl) || cl < 1) { errAdd('Escribe el número de cliente (1, 2, 3…).'); return; }
    if (!isFinite(ll) || !isFinite(ini) || !isFinite(fin)) { errAdd('Las horas deben tener el formato H:MM, por ejemplo 6:15.'); return; }
    if (ini < ll) { errAdd('El inicio del servicio no puede ser antes de la llegada.'); return; }
    if (fin < ini) { errAdd('El fin del servicio no puede ser antes del inicio.'); return; }
    const key = ui.tabla === 'M' ? 'mostrador' : 'caja';
    const previos = BD[key].filter(r => r.o === o && tmin(r.ll) <= ll).map(r => tmin(r.ll));
    const en = previos.length ? ll - Math.max.apply(null, previos) : 0;
    const reg = { o: o, cl: cl, ll: hhmm(ll), en: en };
    if (key === 'mostrador') reg.sv = $('addSv').value;
    reg.ini = hhmm(ini); reg.fin = hhmm(fin); reg.se = fin - ini; reg.es = ini - ll;
    BD[key].push(reg); guardaBD(); errAdd('');
    ['addCl', 'addLl', 'addIni', 'addFin'].forEach(id => { $(id).value = ''; });
    ui.obs = o; renderDB();
  });
  $('btnExport').addEventListener('click', () => {
    const key = ui.tabla === 'M' ? 'mostrador' : 'caja', cols = ui.tabla === 'M' ? COLS_M : COLS_C;
    const rows = enScope(BD[key], ui.obs);
    const txt = cols.map(c => c[0]).join(';') + '\n' + rows.map(r => cols.map(c => r[c[1]]).join(';')).join('\n');
    const url = URL.createObjectURL(new Blob(['\ufeff' + txt], { type: 'text/csv;charset=utf-8' }));
    const a = document.createElement('a'); a.href = url; a.download = 'lili_' + key + '_' + (ui.obs === 'all' ? 'todas' : 'obs' + ui.obs) + '.csv';
    document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 1000);
  });
  $('btnReset').addEventListener('click', () => {
    if (!confirm('Se borrarán los cambios y volverán los datos originales de las 3 observaciones. ¿Continuar?')) return;
    BD = semilla(); guardaBD(); ui.obs = 'all'; renderDB();
  });
  $('btnDelObs').addEventListener('click', () => {
    if (ui.obs === 'all' || !confirm('¿Eliminar la observación ' + ui.obs + ' con todos sus registros?')) return;
    const id = ui.obs;
    BD.obs = BD.obs.filter(o => o.id !== id); BD.mostrador = BD.mostrador.filter(r => r.o !== id); BD.caja = BD.caja.filter(r => r.o !== id);
    ui.obs = 'all'; guardaBD(); renderDB();
  });

  // Controles de la simulación
  function muestraError(m) { const e = $('err'); e.textContent = m; e.hidden = !m; }
  function formatoEntrada(x) { return String(Math.round(x * 1000) / 1000).replace('.', ','); }
  function cargarDesdeBD() { // carga los tiempos de la base de datos en los campos de entrada
    const st = estadisticas(ui.obs);
    if (![st.mEn, st.mSM, st.mSC].every(x => isFinite(x) && x > 0)) { muestraError('La selección de la base de datos no tiene datos suficientes.'); return; }
    $('inLleg').value = formatoEntrada(st.mEn); $('inEmp').value = formatoEntrada(st.mSM); $('inCaja').value = formatoEntrada(st.mSC);
    ['inLleg', 'inEmp', 'inCaja'].forEach(id => sincro(id));
    muestraError('');
    $('info').textContent = 'Cargado desde la base de datos (' + (ui.obs === 'all' ? 'todas las observaciones' : 'observación ' + ui.obs) + ').';
  }
  function preparaModo() {// prepara los datos de simulación según el modo seleccionado
    const modo = $('inModo').value;
    if (modo === 'emp') {
      const m = BD.mostrador.map(r => r.se).filter(v => v > 0), c = BD.caja.map(r => r.se).filter(v => v > 0);
      if (!m.length || !c.length) return 'La base de datos no tiene tiempos de servicio para remuestrear.';
      sim.datosM = m; sim.datosC = c;
    }
    if (modo === 'traza') {
      const id = +$('inObs').value, t = construyeTraza(id);
      if (!t.items.length) return 'Esa observación no tiene registros de mostrador.';
      sim.traza = t.items; sim.horaBase = t.base; sim.obsId = id;
    }
    sim.modo = modo; return '';
  }
  function reinicia() {// reinicia la simulación y borra los clientes vivos de la escena
    vivos.forEach(c => { if (E) E.quita(c); }); vivos = [];
    sim.reiniciar(); nLog = -1; $('hint').hidden = true; actualizaPanel();
  }
  function aplicaYReinicia() {// aplica los parámetros y reinicia la simulación
    const e = preparaModo(); if (e) { muestraError(e); return; }
    muestraError(''); reinicia();
  }
  const PARES = [['inLleg', 'inLlegH'], ['inEmp', 'inEmpH'], ['inCaja', 'inCajaH']];
  const fmtH = x => String(Math.round(x * 10) / 10).replace('.', ',');
  function sincro(id) {   // tiempo (min)  <->  clientes por hora = 60 / tiempo
    PARES.forEach(p => {
      if (id === p[0]) { const v = numero($(p[0]).value); $(p[1]).value = (isFinite(v) && v > 0) ? fmtH(60 / v) : ''; }
      if (id === p[1]) { const v = numero($(p[1]).value); $(p[0]).value = (isFinite(v) && v > 0) ? formatoEntrada(60 / v) : ''; }
    });
  }
  function etiquetasModelo() { // actualiza las etiquetas de la simulación según el número de empleados
    $('mmc').textContent = 'M/M/' + NUM_EMP;
    $('lede').textContent = 'Colas en serie: ' + (NUM_EMP === 1 ? 'un empleado' : NUM_EMP + ' empleados') + ' en el mostrador (M/M/' + NUM_EMP + ') y luego un cajero (M/M/1).';
  }
  function aplicaParametros() { // aplica los parámetros de entrada a la simulación y calcula la teoría
    const v = [$('inLleg'), $('inEmp'), $('inCaja')].map(i => numero(i.value));
    if (v.some(x => !isFinite(x))) { muestraError('Llena los tres tiempos (o los clientes por hora), con números (ej. 2,442), o usa «Cargar datos de la BD».'); return false; }
    if (v.some(x => x <= 0)) { muestraError('Los valores deben ser mayores que 0.'); return false; }
    if (v[0] < 0.05) { muestraError('El tiempo entre llegadas debe ser de al menos 0,05 min.'); return false; }
    const e = preparaModo(); if (e) { muestraError(e); return false; }
    muestraError('');
    NUM_EMP = +$('inN').value || 3; etiquetasModelo();
    sim.lam = 1 / v[0]; sim.mu1 = 1 / v[1]; sim.mu2 = 1 / v[2];
    teo = teoria(sim.lam, sim.mu1, sim.mu2);
    $('info').textContent = 'λ = ' + fmt(sim.lam) + ' llegadas/min · μ1 = ' + fmt(sim.mu1) + ' /min por empleado · μ2 = ' + fmt(sim.mu2) + ' /min del cajero · ' + NUM_EMP + ' empleado' + (NUM_EMP > 1 ? 's' : '') + ' en el mostrador';
    return true;
  }
  function iniciar(ev) { // inicia la simulación
    ev.preventDefault();
    if (!aplicaParametros()) return;
    corriendo = true; pausa = false;
    $('btnPausa').disabled = false; $('btnReiniciar').disabled = false; $('btnPausa').textContent = 'Pausa';
    reinicia();
  }
  const CAMPOS = ['inLleg', 'inEmp', 'inCaja', 'inLlegH', 'inEmpH', 'inCajaH', 'inN'];
  $('form').addEventListener('input', e => { if (CAMPOS.indexOf(e.target.id) >= 0) sincro(e.target.id); });
  $('form').addEventListener('change', e => {
    if (CAMPOS.indexOf(e.target.id) < 0) return;
    if (corriendo) { if (aplicaParametros()) reinicia(); }          // cambio en vivo: reinicia con los datos nuevos
    else if (e.target.id === 'inN') { NUM_EMP = +$('inN').value || 3; etiquetasModelo(); }
  });
  $('form').addEventListener('submit', iniciar);
  $('btnMedidos').addEventListener('click', cargarDesdeBD);
  $('btnUsar').addEventListener('click', () => { cargarDesdeBD(); window.scrollTo({ top: 0, behavior: 'smooth' }); });
  $('btnPausa').addEventListener('click', () => { pausa = !pausa; $('btnPausa').textContent = pausa ? 'Reanudar' : 'Pausa'; });
  $('btnReiniciar').addEventListener('click', aplicaYReinicia);
  $('inModo').addEventListener('change', () => { $('fObs').hidden = $('inModo').value !== 'traza'; if (corriendo) aplicaYReinicia(); });
  $('inObs').addEventListener('change', () => { if (corriendo && $('inModo').value === 'traza') aplicaYReinicia(); });
  $('velSlider').addEventListener('input', e => { speed = +e.target.value; $('velOut').textContent = speed; });

  // Arranque y bucle
  armaTabla('tb1', FILAS1); armaTabla('tb2', FILAS2); armaTabla('tb3', FILAS3);
  renderDB();
  let errEsc = '';
  try { E = crearEscena(); } catch (err) { E = null; errEsc = String(err && err.message || err); }
  if (!E) { $('nogl').textContent += errEsc ? ' Detalle técnico: ' + errEsc : ''; $('nogl').hidden = false; $('camtools').hidden = true; }
  let last = performance.now(), acc = 1;
  function frame(now) {
    const dt = Math.min(0.1, (now - last) / 1000); last = now;
    if (corriendo && !pausa) sim.avanzar(dt * speed);
    mueveClientes(dt);
    if (E) { E.estados(); E.render(dt); }
    acc += dt; if (acc > 0.15) { acc = 0; actualizaPanel(); }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
})();
