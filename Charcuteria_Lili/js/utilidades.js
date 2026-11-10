/* Archivo que contiene funciones de utilidad para la simulación. */
(function () { // Se definen en un archivo separado para que sea sencillo revisar o actualizar las funciones.
    "use strict";
    const fmt = (v, d = 3) => (v == null || !isFinite(v)) ? '—' : v.toLocaleString('es-CO', { minimumFractionDigits: d, maximumFractionDigits: d });
    const expo = rate => -Math.log(1 - Math.random()) / rate;
    const pick = a => a[Math.floor(Math.random() * a.length)];
    const fact = n => { let f = 1; for (let i = 2; i <= n; i++)f *= i; return f; };
    const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
    const numero = s => parseFloat(String(s).trim().replace(',', '.'));
    const tmin = s => { const m = /^(\d{1,2}):(\d{2})$/.exec(String(s).trim()); return m ? (+m[1]) * 60 + (+m[2]) : NaN; };
    const hhmm = x => { x = Math.floor(x + 1e-9); return Math.floor(x / 60) + ':' + String(x % 60).padStart(2, '0'); };
    const media = a => a.length ? a.reduce((s, v) => s + v, 0) / a.length : NaN;
    window.LILI_UTILIDADES = { fmt, expo, pick, fact, clamp, numero, tmin, hhmm, media };
})();
