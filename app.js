/**
 * ============================================================================
 * INTERPOLACIÓN POLINOMIAL DE NEWTON (DIFERENCIAS DIVIDIDAS)
 * Solucionador General de Métodos Numéricos con Aritmética Exacta de Fracciones
 * ============================================================================
 */

"use strict";

// Elementos del DOM
const el = {
    vectorX: document.getElementById("vectorX"),
    vectorY: document.getElementById("vectorY"),
    valorEvaluar: document.getElementById("valorEvaluar"),
    checkOrdenarX: document.getElementById("checkOrdenarX"),
    btnResolver: document.getElementById("btnResolver"),
    btnEjemplo: document.getElementById("btnEjemplo"),
    btnLimpiar: document.getElementById("btnLimpiar"),
    mensajeAlerta: document.getElementById("mensajeAlerta"),
    
    // Resultados
    panelResultado: document.getElementById("panelResultado"),
    badgeGrado: document.getElementById("badgeGrado"),
    resultadoLatencia: document.getElementById("resultadoLatencia"),
    resultadoCarga: document.getElementById("resultadoCarga"),
    badgeTipoEvaluacion: document.getElementById("badgeTipoEvaluacion"),
    explicacionResultado: document.getElementById("explicacionResultado"),

    // Polinomios
    polinomioNewtonKatex: document.getElementById("polinomioNewtonKatex"),
    polinomioNewtonFallback: document.getElementById("polinomioNewtonFallback"),
    polinomioEstandarKatex: document.getElementById("polinomioEstandarKatex"),
    polinomioEstandarFallback: document.getElementById("polinomioEstandarFallback"),

    // Tablas
    tablaDiferencias: document.getElementById("tablaDiferencias"),
    tablaValidacion: document.getElementById("tablaValidacion"),
    badgeValidacionGlobal: document.getElementById("badgeValidacionGlobal"),
    mensajeValidacionTexto: document.getElementById("mensajeValidacionTexto"),

    // Gráfica
    canvas: document.getElementById("graficaLatencia"),
    chartTooltip: document.getElementById("chartTooltip")
};

// Estado global para la gráfica y cálculos
let chartState = {
    X: [],
    Y: [],
    coeficientes: [],
    valorEvaluar: null,
    muestras: [],
    xMin: 0,
    xMax: 0,
    yMin: 0,
    yMax: 0,
    margen: { izq: 60, der: 24, sup: 24, inf: 48 },
    hoverPoint: null,
    isHovering: false
};

// Event listeners
el.btnResolver.addEventListener("click", () => resolverInterpolacion());
el.btnEjemplo.addEventListener("click", () => cargarEjemplo());
if (el.btnLimpiar) {
    el.btnLimpiar.addEventListener("click", () => limpiarCampos());
}

if (el.checkOrdenarX) {
    el.checkOrdenarX.addEventListener("change", () => resolverInterpolacion());
}

// Resolver al presionar Enter en cualquier campo
[el.vectorX, el.vectorY, el.valorEvaluar].forEach(input => {
    input.addEventListener("keydown", (e) => {
        if (e.key === "Enter") {
            resolverInterpolacion();
        }
    });
});

/* ==========================================================================
   1. CLASE FRACCIÓN PARA ARITMÉTICA RACIONAL EXACTA (BIGINT)
   ========================================================================== */

/**
 * Algoritmo de Euclides para el Máximo Común Divisor con BigInt.
 */
function mcd(a, b) {
    a = a < 0n ? -a : a;
    b = b < 0n ? -b : b;
    while (b !== 0n) {
        const t = b;
        b = a % b;
        a = t;
    }
    return a;
}

class Fraccion {
    constructor(num, den = 1n) {
        if (typeof num === "number") num = BigInt(Math.round(num));
        else if (typeof num === "string") num = BigInt(num);
        if (typeof den === "number") den = BigInt(Math.round(den));
        else if (typeof den === "string") den = BigInt(den);

        if (den === 0n) {
            throw new Error("División por cero en el cálculo fraccionario.");
        }

        if (den < 0n) {
            num = -num;
            den = -den;
        }

        const g = mcd(num, den);
        this.num = num / g;
        this.den = den / g;
    }

    add(other) {
        return new Fraccion(
            this.num * other.den + other.num * this.den,
            this.den * other.den
        );
    }

    sub(other) {
        return new Fraccion(
            this.num * other.den - other.num * this.den,
            this.den * other.den
        );
    }

    mul(other) {
        return new Fraccion(
            this.num * other.num,
            this.den * other.den
        );
    }

    div(other) {
        if (other.num === 0n) {
            throw new Error("División por cero.");
        }
        return new Fraccion(
            this.num * other.den,
            this.den * other.num
        );
    }

    neg() {
        return new Fraccion(-this.num, this.den);
    }

    abs() {
        return new Fraccion(this.num < 0n ? -this.num : this.num, this.den);
    }

    isZero() {
        return this.num === 0n;
    }

    isNegative() {
        return this.num < 0n;
    }

    equals(other) {
        return this.num === other.num && this.den === other.den;
    }

    toNumber() {
        return Number(this.num) / Number(this.den);
    }

    toLatex() {
        if (this.den === 1n) return this.num.toString();
        const sign = this.num < 0n ? "-" : "";
        const absNum = this.num < 0n ? -this.num : this.num;
        return `${sign}\\frac{${absNum}}{${this.den}}`;
    }

    toString() {
        if (this.den === 1n) return this.num.toString();
        return `${this.num}/${this.den}`;
    }

    toDecimalString(maxDec = 6) {
        if (this.den === 1n) return this.num.toString();
        const val = this.toNumber();
        if (Math.abs(val) < 1e-5 || Math.abs(val) >= 1e7) {
            return val.toExponential(4).replace("e+", "e");
        }
        return parseFloat(val.toFixed(maxDec)).toString();
    }
}

/* ==========================================================================
   2. PARSEO DE FRACCIONES Y NÚMEROS ARBITRARIOS (SIN PÉRDIDA DE PRECISIÓN)
   ========================================================================== */

/**
 * Convierte cualquier representación de texto a una Fracción exacta:
 * - Enteros: "45", "-7"
 * - Fracciones explícitas: "1/3", "-5/6"
 * - Decimales de cualquier longitud: "0.0000000003" -> 3/10000000000
 * - Notación científica: "3e-10", "1.5e-3"
 */
function parsearFraccion(texto) {
    if (!texto || typeof texto !== "string") {
        throw new Error("Valor vacío o inválido.");
    }
    texto = texto.trim();

    // 1. Fracción con barra inclinada
    if (texto.includes("/")) {
        const partes = texto.split("/");
        if (partes.length !== 2) {
            throw new Error(`Fracción mal formada: "${texto}".`);
        }
        const fNum = parsearFraccion(partes[0]);
        const fDen = parsearFraccion(partes[1]);
        return fNum.div(fDen);
    }

    // 2. Notación científica (ej. 3e-10)
    if (texto.toLowerCase().includes("e")) {
        const [mantisa, expStr] = texto.toLowerCase().split("e");
        const fMantisa = parsearFraccion(mantisa);
        const exp = parseInt(expStr, 10);
        if (isNaN(exp)) {
            throw new Error(`Exponente científico inválido en: "${texto}".`);
        }
        if (exp >= 0) {
            return fMantisa.mul(new Fraccion(10n ** BigInt(exp)));
        } else {
            return fMantisa.div(new Fraccion(10n ** BigInt(-exp)));
        }
    }

    // 3. Número decimal exacto (ej. 0.0000000003)
    if (texto.includes(".")) {
        let neg = false;
        if (texto.startsWith("-")) {
            neg = true;
            texto = texto.slice(1);
        } else if (texto.startsWith("+")) {
            texto = texto.slice(1);
        }

        const [entero, decimales] = texto.split(".");
        const entStr = entero === "" ? "0" : entero;
        const numStr = entStr + decimales;
        const num = BigInt(numStr);
        const den = 10n ** BigInt(decimales.length);
        const f = new Fraccion(num, den);
        return neg ? f.neg() : f;
    }

    // 4. Entero
    return new Fraccion(BigInt(texto), 1n);
}

/**
 * Parsea un vector de texto aceptando comas, espacios, saltos de línea y tabuladores.
 */
function parsearVector(cadena) {
    if (!cadena || typeof cadena !== "string") return [];
    // Normaliza espacios alrededor de barras de fracción: "1 / 2" -> "1/2"
    const normalizada = cadena.replace(/\s*\/\s*/g, "/");
    return normalizada
        .trim()
        .split(/[\s,;\n\t]+/)
        .filter(v => v !== "")
        .map(v => parsearFraccion(v));
}

function validarEntradas(X, Y, valorEvaluar) {
    if (!Array.isArray(X) || X.length < 2) {
        throw new Error("Se requieren al menos 2 nodos para construir un polinomio interpolante (grado n ≥ 1).");
    }

    if (X.length !== Y.length) {
        throw new Error(`Los vectores deben tener la misma cantidad de elementos: el vector X tiene ${X.length} nodos y el vector Y tiene ${Y.length} valores.`);
    }

    if (!(valorEvaluar instanceof Fraccion)) {
        throw new Error("El punto a evaluar x no es una fracción o número válido.");
    }

    // Verificar nodos duplicados en X (división entre cero en diferencias divididas)
    for (let i = 0; i < X.length; i++) {
        for (let j = i + 1; j < X.length; j++) {
            if (X[i].equals(X[j])) {
                throw new Error(`El vector X contiene nodos repetidos (${X[i].toString()}). Todos los nodos x_i deben ser distintos para evitar división entre cero.`);
            }
        }
    }
}

/* ==========================================================================
   3. ALGORITMOS NUMÉRICOS DE NEWTON CON FRACCIONES EXACTAS
   ========================================================================== */

/**
 * Construye la tabla triangular de diferencias divididas de orden O(n^2) con fracciones exactas.
 * tabla[i][j] = f[x_i, ..., x_{i+j}]
 * La primera fila tabla[0][j] corresponde a los coeficientes de Newton c_j.
 */
function calcularDiferenciasDivididas(X, Y) {
    const n = X.length;
    const tabla = Array.from({ length: n }, () => Array(n).fill(null));

    // Columna 0: diferencias de orden 0 -> f[x_i] = y_i
    for (let i = 0; i < n; i++) {
        tabla[i][0] = Y[i];
    }

    // Columnas 1 a n-1: diferencias divididas de orden k
    for (let orden = 1; orden < n; orden++) {
        for (let i = 0; i < n - orden; i++) {
            const numerador = tabla[i + 1][orden - 1].sub(tabla[i][orden - 1]);
            const denominador = X[i + orden].sub(X[i]);
            tabla[i][orden] = numerador.div(denominador);
        }
    }

    return tabla;
}

/**
 * Evaluación de Newton mediante el algoritmo anidado tipo Horner:
 * P_n(x) = c_0 + (x - x_0)[c_1 + (x - x_1)[c_2 + ...]]
 */
function evaluarNewton(X, coeficientes, x) {
    const n = coeficientes.length;
    let resultado = coeficientes[n - 1];

    for (let i = n - 2; i >= 0; i--) {
        const factor = x.sub(X[i]);
        resultado = coeficientes[i].add(factor.mul(resultado));
    }

    return resultado;
}

/**
 * Expansión algebraica del polinomio a forma estándar con fracciones exactas:
 * P(x) = a_n * x^n + ... + a_1 * x + a_0
 */
function sumarPolinomiosFrac(p1, p2) {
    const longitud = Math.max(p1.length, p2.length);
    const resultado = [];
    for (let i = 0; i < longitud; i++) {
        const v1 = p1[i] || new Fraccion(0n);
        const v2 = p2[i] || new Fraccion(0n);
        resultado.push(v1.add(v2));
    }
    return resultado;
}

function multiplicarPorFactorFrac(polinomio, raiz) {
    // Multiplica polinomio por (x - raiz)
    const resultado = Array.from({ length: polinomio.length + 1 }, () => new Fraccion(0n));
    for (let i = 0; i < polinomio.length; i++) {
        const prod = polinomio[i].mul(raiz.neg());
        resultado[i] = resultado[i].add(prod);
        resultado[i + 1] = resultado[i + 1].add(polinomio[i]);
    }
    return resultado;
}

function obtenerPolinomioEstandar(X, coeficientes) {
    let acumulado = [new Fraccion(0n)];
    let productoBase = [new Fraccion(1n)];

    for (let i = 0; i < coeficientes.length; i++) {
        const ci = coeficientes[i];
        const termino = productoBase.map(c => c.mul(ci));
        acumulado = sumarPolinomiosFrac(acumulado, termino);
        productoBase = multiplicarPorFactorFrac(productoBase, X[i]);
    }

    return acumulado; // [a_0, a_1, a_2, ..., a_n] en Fraccion
}

/* ==========================================================================
   4. FORMATEO MATEMÁTICO EN LATEX / KATEX Y TEXTO PLANO
   ========================================================================== */

/**
 * Genera el string LaTeX y texto plano para la forma de Newton con fracciones exactas.
 */
function generarFormaNewton(X, coeficientes) {
    const n = coeficientes.length;
    const partesLatex = [];
    const partesPlanas = [];

    for (let i = 0; i < n; i++) {
        const c = coeficientes[i];
        if (c.isZero() && i > 0) continue;

        const cAbs = c.abs();
        const esUnoConFactores = (cAbs.num === 1n && cAbs.den === 1n && i > 0);
        const cLatex = esUnoConFactores ? "" : cAbs.toLatex();
        const cPlano = esUnoConFactores ? "" : (cAbs.den === 1n ? cAbs.num.toString() : `(${cAbs.toString()})`);

        let factoresLatex = "";
        let factoresPlanos = "";

        for (let j = 0; j < i; j++) {
            const xj = X[j];
            if (xj.isZero()) {
                factoresLatex += "x";
                factoresPlanos += "x";
            } else if (xj.isNegative()) {
                const xjAbs = xj.abs();
                factoresLatex += `(x + ${xjAbs.toLatex()})`;
                factoresPlanos += `(x + ${xjAbs.toString()})`;
            } else {
                factoresLatex += `(x - ${xj.toLatex()})`;
                factoresPlanos += `(x - ${xj.toString()})`;
            }
        }

        const terminoLatex = (factoresLatex === "") ? cLatex : `${cLatex}${factoresLatex}`;
        const terminoPlano = (factoresPlanos === "") ? cPlano : `${cPlano}${factoresPlanos}`;

        if (i === 0) {
            partesLatex.push(c.isNegative() ? `-${terminoLatex}` : terminoLatex);
            partesPlanas.push(c.isNegative() ? `-${terminoPlano}` : terminoPlano);
        } else {
            const signo = c.isNegative() ? "-" : "+";
            partesLatex.push(`${signo} ${terminoLatex}`);
            partesPlanas.push(`${signo} ${terminoPlano}`);
        }
    }

    const latex = `P_{${n - 1}}(x) = ` + (partesLatex.join(" ") || "0");
    const plano = `P(x) = ` + (partesPlanas.join(" ") || "0");
    return { latex, plano };
}

/**
 * Genera el string LaTeX y texto plano para la forma estándar con fracciones exactas.
 */
function generarFormaEstandar(polinomioEstandar) {
    const n = polinomioEstandar.length - 1;
    const partesLatex = [];
    const partesPlanas = [];

    for (let i = n; i >= 0; i--) {
        const coef = polinomioEstandar[i];
        if (coef.isZero()) continue;

        const coefAbs = coef.abs();
        const esUno = coefAbs.num === 1n && coefAbs.den === 1n;

        let coefLatex = esUno && i > 0 ? "" : coefAbs.toLatex();
        let coefPlano = esUno && i > 0 ? "" : (coefAbs.den === 1n ? coefAbs.num.toString() : `(${coefAbs.toString()})`);

        let varLatex = "";
        let varPlana = "";

        if (i === 1) {
            varLatex = "x";
            varPlana = "x";
        } else if (i > 1) {
            varLatex = `x^{${i}}`;
            varPlana = `x^${i}`;
        }

        const terminoLatex = `${coefLatex}${varLatex}`;
        const terminoPlano = `${coefPlano}${varPlana}`;

        const esPrimerTermino = partesLatex.length === 0;

        if (esPrimerTermino) {
            partesLatex.push(coef.isNegative() ? `-${terminoLatex}` : terminoLatex);
            partesPlanas.push(coef.isNegative() ? `-${terminoPlano}` : terminoPlano);
        } else {
            const signo = coef.isNegative() ? "-" : "+";
            partesLatex.push(`${signo} ${terminoLatex}`);
            partesPlanas.push(`${signo} ${terminoPlano}`);
        }
    }

    if (partesLatex.length === 0) {
        return { latex: `P_{${n}}(x) = 0`, plano: `P(x) = 0` };
    }

    const latex = `P_{${n}}(x) = ` + partesLatex.join(" ");
    const plano = `P(x) = ` + partesPlanas.join(" ");
    return { latex, plano };
}

function renderizarFormulaMath(contenedorKatex, contenedorFallback, latex, plano) {
    if (window.katex) {
        try {
            window.katex.render(latex, contenedorKatex, {
                displayMode: true,
                throwOnError: false
            });
            contenedorKatex.classList.remove("hidden");
            contenedorFallback.classList.add("hidden");
            return;
        } catch (err) {
            console.warn("Error renderizando con KaTeX:", err);
        }
    }
    contenedorKatex.classList.add("hidden");
    contenedorFallback.classList.remove("hidden");
    contenedorFallback.textContent = plano;
}

/* ==========================================================================
   5. RENDERIZADO DE TABLAS
   ========================================================================== */

function renderizarTablaDiferencias(X, tabla) {
    const thead = el.tablaDiferencias.querySelector("thead");
    const tbody = el.tablaDiferencias.querySelector("tbody");

    thead.innerHTML = "";
    tbody.innerHTML = "";

    const trHead = document.createElement("tr");

    const thIndice = document.createElement("th");
    thIndice.textContent = "i";
    trHead.appendChild(thIndice);

    const thX = document.createElement("th");
    thX.textContent = "xᵢ";
    trHead.appendChild(thX);

    for (let orden = 0; orden < X.length; orden++) {
        const th = document.createElement("th");
        th.textContent = (orden === 0) ? "f[xᵢ]" : `${orden}.ª diferencia`;
        trHead.appendChild(th);
    }
    thead.appendChild(trHead);

    for (let i = 0; i < X.length; i++) {
        const tr = document.createElement("tr");

        const tdIdx = document.createElement("td");
        tdIdx.textContent = i;
        tr.appendChild(tdIdx);

        const tdX = document.createElement("td");
        tdX.textContent = X[i].toString();
        if (X[i].den !== 1n) {
            tdX.title = `≈ ${X[i].toDecimalString(6)}`;
        }
        tr.appendChild(tdX);

        for (let orden = 0; orden < X.length; orden++) {
            const td = document.createElement("td");
            const val = tabla[i][orden];

            if (val === null || val === undefined) {
                td.textContent = "—";
                td.className = "empty-cell";
            } else {
                td.textContent = val.toString();
                if (val.den !== 1n) {
                    td.title = `≈ ${val.toDecimalString(6)}`;
                }
                // Si es la fila 0, resaltar porque es el coeficiente c_orden de Newton
                if (i === 0) {
                    td.classList.add("coeff-cell");
                    td.title = `Coeficiente c_${orden} = ${val.toString()}` + (val.den !== 1n ? ` (≈ ${val.toDecimalString(6)})` : "");
                }
            }
            tr.appendChild(td);
        }

        tbody.appendChild(tr);
    }
}

function renderizarTablaValidacion(X, Y, coeficientes) {
    const tbody = el.tablaValidacion.querySelector("tbody");
    tbody.innerHTML = "";

    let todoExacto = true;

    for (let i = 0; i < X.length; i++) {
        const xi = X[i];
        const yiOriginal = Y[i];
        const yiCalculado = evaluarNewton(X, coeficientes, xi);
        const error = yiOriginal.sub(yiCalculado);
        const esExacto = error.isZero();

        if (!esExacto) todoExacto = false;

        const tr = document.createElement("tr");

        tr.innerHTML = `
            <td>${i}</td>
            <td>${xi.toString()}</td>
            <td>${yiOriginal.toString()}</td>
            <td>${yiCalculado.toString()}</td>
            <td>${error.isZero() ? "0" : error.abs().toString()}</td>
            <td>
                <span class="${esExacto ? 'status-cell-pass' : 'status-cell-fail'}">
                    ${esExacto ? '✓ Exacto (error = 0)' : '✗ Discrepancia'}
                </span>
            </td>
        `;

        tbody.appendChild(tr);
    }

    if (todoExacto) {
        el.badgeValidacionGlobal.textContent = "Validación Exacta";
        el.badgeValidacionGlobal.className = "badge-success";
        el.mensajeValidacionTexto.textContent = 
            `El polinomio reproduce con exactitud matemática absoluta todos los ${X.length} nodos (error = 0 sin pérdida de precisión).`;
    } else {
        el.badgeValidacionGlobal.textContent = "Revisar datos";
        el.badgeValidacionGlobal.className = "detail-badge warning";
        el.mensajeValidacionTexto.textContent = 
            `Se detectaron diferencias en los nodos. Verifique la entrada.`;
    }
}

/* ==========================================================================
   6. GRÁFICA CANVAS INTERACTIVA (HIDPI + TOOLTIP + GUÍAS)
   ========================================================================== */

function configurarCanvasHiDPI(canvas) {
    const dpr = window.devicePixelRatio || 1;
    const rect = canvas.getBoundingClientRect();
    const w = rect.width;
    const h = rect.height;

    canvas.width = Math.round(w * dpr);
    canvas.height = Math.round(h * dpr);

    const ctx = canvas.getContext("2d");
    ctx.resetTransform?.();
    if (ctx.scale) {
        ctx.scale(dpr, dpr);
    }

    return { ctx, w, h };
}

function prepararDatosGrafica(X, Y, coeficientes, valorEvaluar) {
    const xNums = X.map(x => x.toNumber());
    const yNums = Y.map(y => y.toNumber());
    const evalNum = valorEvaluar.toNumber();

    const xMinDatos = Math.min(...xNums);
    const xMaxDatos = Math.max(...xNums);
    const margenX = Math.max((xMaxDatos - xMinDatos) * 0.12, 0.5);

    const xMin = Math.min(xMinDatos, evalNum) - margenX;
    const xMax = Math.max(xMaxDatos, evalNum) + margenX;

    const muestras = [];
    const numPuntos = 260;

    for (let i = 0; i <= numPuntos; i++) {
        const xVal = xMin + (xMax - xMin) * (i / numPuntos);
        // Evaluar con aproximación decimal para el Canvas
        const xFrac = parsearFraccion(xVal.toFixed(10));
        const yFrac = evaluarNewton(X, coeficientes, xFrac);
        muestras.push({ x: xVal, y: yFrac.toNumber() });
    }

    const yValores = [...yNums, evaluarNewton(X, coeficientes, valorEvaluar).toNumber(), ...muestras.map(m => m.y)];
    const yMinDatos = Math.min(...yValores);
    const yMaxDatos = Math.max(...yValores);
    const margenY = Math.max((yMaxDatos - yMinDatos) * 0.14, 1);

    const yMin = yMinDatos - margenY;
    const yMax = yMaxDatos + margenY;

    chartState = {
        ...chartState,
        X,
        Y,
        coeficientes,
        valorEvaluar,
        muestras,
        xMin,
        xMax,
        yMin,
        yMax
    };
}

function redibujarGrafica() {
    if (!chartState.X || chartState.X.length < 2) return;

    const canvas = el.canvas;
    const { ctx, w, h } = configurarCanvasHiDPI(canvas);

    const m = chartState.margen;
    const plotW = w - m.izq - m.der;
    const plotH = h - m.sup - m.inf;

    const toPxX = (x) => m.izq + ((x - chartState.xMin) / (chartState.xMax - chartState.xMin)) * plotW;
    const toPxY = (y) => h - m.inf - ((y - chartState.yMin) / (chartState.yMax - chartState.yMin)) * plotH;

    ctx.clearRect(0, 0, w, h);

    // 1. Rejilla tenue de fondo
    ctx.strokeStyle = "#f1f5f9";
    ctx.lineWidth = 1;

    // Cuadrícula horizontal (eje Y)
    const pasosY = 5;
    for (let i = 0; i <= pasosY; i++) {
        const valY = chartState.yMin + (chartState.yMax - chartState.yMin) * (i / pasosY);
        const py = toPxY(valY);

        ctx.beginPath();
        ctx.moveTo(m.izq, py);
        ctx.lineTo(w - m.der, py);
        ctx.stroke();

        ctx.fillStyle = "#94a3b8";
        ctx.font = "11px Inter, sans-serif";
        ctx.textAlign = "right";
        ctx.textBaseline = "middle";
        ctx.fillText(valY.toLocaleString("es-PE", { maximumFractionDigits: 3 }), m.izq - 8, py);
    }

    // Cuadrícula vertical (eje X)
    const pasosX = 6;
    for (let i = 0; i <= pasosX; i++) {
        const valX = chartState.xMin + (chartState.xMax - chartState.xMin) * (i / pasosX);
        const px = toPxX(valX);

        ctx.beginPath();
        ctx.moveTo(px, m.sup);
        ctx.lineTo(px, h - m.inf);
        ctx.stroke();

        ctx.fillStyle = "#94a3b8";
        ctx.font = "11px Inter, sans-serif";
        ctx.textAlign = "center";
        ctx.textBaseline = "top";
        ctx.fillText(valX.toLocaleString("es-PE", { maximumFractionDigits: 3 }), px, h - m.inf + 8);
    }

    // 2. Ejes principales
    ctx.strokeStyle = "#cbd5e1";
    ctx.lineWidth = 1.2;

    ctx.beginPath();
    ctx.moveTo(m.izq, h - m.inf);
    ctx.lineTo(w - m.der, h - m.inf);
    ctx.stroke();

    ctx.beginPath();
    ctx.moveTo(m.izq, m.sup);
    ctx.lineTo(m.izq, h - m.inf);
    ctx.stroke();

    // Títulos de ejes
    ctx.fillStyle = "#64748b";
    ctx.font = "500 11.5px Inter, sans-serif";
    ctx.textAlign = "center";
    ctx.fillText("Variable x", m.izq + plotW / 2, h - 14);

    ctx.save();
    ctx.translate(16, m.sup + plotH / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.textAlign = "center";
    ctx.fillText("y = P(x)", 0, 0);
    ctx.restore();

    // 3. Trazo de la curva continua del polinomio
    ctx.strokeStyle = "#2563eb";
    ctx.lineWidth = 2.4;
    ctx.lineCap = "round";
    ctx.lineJoin = "round";

    ctx.beginPath();
    chartState.muestras.forEach((punto, idx) => {
        const px = toPxX(punto.x);
        const py = toPxY(punto.y);
        if (idx === 0) ctx.moveTo(px, py);
        else ctx.lineTo(px, py);
    });
    ctx.stroke();

    // 4. Guías punteadas al punto evaluado
    const yEvalFrac = evaluarNewton(chartState.X, chartState.coeficientes, chartState.valorEvaluar);
    const pxEval = toPxX(chartState.valorEvaluar.toNumber());
    const pyEval = toPxY(yEvalFrac.toNumber());

    ctx.save();
    ctx.setLineDash([4, 4]);
    ctx.strokeStyle = "rgba(16, 185, 129, 0.6)";
    ctx.lineWidth = 1.2;

    ctx.beginPath();
    ctx.moveTo(pxEval, h - m.inf);
    ctx.lineTo(pxEval, pyEval);
    ctx.lineTo(m.izq, pyEval);
    ctx.stroke();
    ctx.restore();

    // 5. Nodos de interpolación
    chartState.X.forEach((xi, i) => {
        const yi = chartState.Y[i];
        const px = toPxX(xi.toNumber());
        const py = toPxY(yi.toNumber());

        ctx.fillStyle = "#ffffff";
        ctx.beginPath();
        ctx.arc(px, py, 6, 0, Math.PI * 2);
        ctx.fill();

        ctx.fillStyle = "#ef4444";
        ctx.beginPath();
        ctx.arc(px, py, 4.5, 0, Math.PI * 2);
        ctx.fill();

        ctx.fillStyle = "#475569";
        ctx.font = "500 11px Inter, sans-serif";
        ctx.textAlign = "center";
        ctx.fillText(`(${xi.toString()}, ${yi.toString()})`, px, py - 10);
    });

    // 6. Punto evaluado destacado (verde)
    ctx.fillStyle = "#ffffff";
    ctx.beginPath();
    ctx.arc(pxEval, pyEval, 7.5, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "#10b981";
    ctx.beginPath();
    ctx.arc(pxEval, pyEval, 5.5, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "#047857";
    ctx.font = "600 12px Inter, sans-serif";
    ctx.textAlign = "left";
    ctx.fillText(
        `P(${chartState.valorEvaluar.toString()}) = ${yEvalFrac.toString()}`,
        pxEval + 9,
        pyEval - 8
    );

    // 7. Hover interactivo sobre la curva
    if (chartState.isHovering && chartState.hoverPoint) {
        const hp = chartState.hoverPoint;
        const hpx = toPxX(hp.x);
        const hpy = toPxY(hp.y);

        ctx.strokeStyle = "rgba(100, 116, 139, 0.4)";
        ctx.setLineDash([2, 2]);
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(hpx, m.sup);
        ctx.lineTo(hpx, h - m.inf);
        ctx.stroke();

        ctx.fillStyle = "#0f172a";
        ctx.beginPath();
        ctx.arc(hpx, hpy, 4, 0, Math.PI * 2);
        ctx.fill();
    }
}

// Interacción con cursor / hover sobre el canvas
el.canvas.addEventListener("mousemove", (e) => {
    if (!chartState.muestras || chartState.muestras.length === 0) return;

    const rect = el.canvas.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    const m = chartState.margen;
    const plotW = rect.width - m.izq - m.der;

    if (mouseX < m.izq || mouseX > rect.width - m.der) {
        chartState.isHovering = false;
        el.chartTooltip.classList.add("hidden");
        redibujarGrafica();
        return;
    }

    const xVal = chartState.xMin + ((mouseX - m.izq) / plotW) * (chartState.xMax - chartState.xMin);
    const xFrac = parsearFraccion(xVal.toFixed(8));
    const yFrac = evaluarNewton(chartState.X, chartState.coeficientes, xFrac);

    chartState.isHovering = true;
    chartState.hoverPoint = { x: xVal, y: yFrac.toNumber() };

    el.chartTooltip.style.left = `${mouseX}px`;
    el.chartTooltip.style.top = `${mouseY}px`;
    el.chartTooltip.innerHTML = `<strong>x:</strong> ${xVal.toFixed(4)}<br><strong>P(x):</strong> ${yFrac.toString()}` +
        (yFrac.den !== 1n ? ` (≈ ${yFrac.toDecimalString(5)})` : "");
    el.chartTooltip.classList.remove("hidden");

    redibujarGrafica();
});

el.canvas.addEventListener("mouseleave", () => {
    chartState.isHovering = false;
    chartState.hoverPoint = null;
    el.chartTooltip.classList.add("hidden");
    redibujarGrafica();
});

window.addEventListener("resize", () => {
    redibujarGrafica();
});

/* ==========================================================================
   7. CONTROLADOR PRINCIPAL: RESOLUCIÓN Y ACTUALIZACIÓN
   ========================================================================== */

function mostrarMensajeError(msg) {
    el.mensajeAlerta.textContent = msg;
    el.mensajeAlerta.className = "alert-message error";
    el.mensajeAlerta.classList.remove("hidden");
}

function ocultarMensajeAlerta() {
    el.mensajeAlerta.classList.add("hidden");
}

function resolverInterpolacion() {
    ocultarMensajeAlerta();

    try {
        let X = parsearVector(el.vectorX.value);
        let Y = parsearVector(el.vectorY.value);
        const valorEvaluar = parsearFraccion(el.valorEvaluar.value);

        // 1. Validaciones
        validarEntradas(X, Y, valorEvaluar);

        // 2. Ordenamiento opcional por x creciente
        if (el.checkOrdenarX && el.checkOrdenarX.checked) {
            const pares = X.map((xVal, idx) => ({ x: xVal, y: Y[idx] }));
            pares.sort((a, b) => {
                const diff = a.x.sub(b.x);
                return diff.isNegative() ? -1 : diff.isZero() ? 0 : 1;
            });
            X = pares.map(p => p.x);
            Y = pares.map(p => p.y);
            // Reflejar campos ordenados con formato de fracción
            el.vectorX.value = X.map(x => x.toString()).join(", ");
            el.vectorY.value = Y.map(y => y.toString()).join(", ");
        }

        // 3. Tabla de diferencias divididas con fracciones exactas
        const tabla = calcularDiferenciasDivididas(X, Y);

        // Coeficientes de Newton (primera fila c_j = tabla[0][j])
        const coeficientes = tabla[0].slice(0, X.length);

        // 4. Evaluación en el punto solicitado x
        const valorInterpolado = evaluarNewton(X, coeficientes, valorEvaluar);

        // 5. Polinomio estándar expandido con fracciones
        const polinomioEstandar = obtenerPolinomioEstandar(X, coeficientes);

        // 6. Actualizar métricas destacadas
        const grado = X.length - 1;
        el.badgeGrado.textContent = `Grado n = ${grado}`;

        // Mostrar fracción en KaTeX o texto en la tarjeta destacada
        if (valorInterpolado.den === 1n) {
            el.resultadoLatencia.textContent = valorInterpolado.num.toString();
        } else if (window.katex) {
            try {
                window.katex.render(valorInterpolado.toLatex(), el.resultadoLatencia, {
                    displayMode: false,
                    throwOnError: false
                });
            } catch (err) {
                el.resultadoLatencia.textContent = valorInterpolado.toString();
            }
        } else {
            el.resultadoLatencia.textContent = valorInterpolado.toString();
        }

        const evalDecStr = valorInterpolado.den !== 1n ? ` (≈ ${valorInterpolado.toDecimalString(6)})` : "";
        el.resultadoCarga.textContent = `x = ${valorEvaluar.toString()}${evalDecStr}`;

        const xNums = X.map(x => x.toNumber());
        const xMinDatos = Math.min(...xNums);
        const xMaxDatos = Math.max(...xNums);
        const evalNum = valorEvaluar.toNumber();
        const esInterpolacion = (evalNum >= xMinDatos && evalNum <= xMaxDatos);

        el.badgeTipoEvaluacion.textContent = esInterpolacion ? "Interpolación" : "Extrapolación";
        el.badgeTipoEvaluacion.className = `detail-badge ${esInterpolacion ? "success" : "warning"}`;

        el.explicacionResultado.textContent = esInterpolacion
            ? `Para x = ${valorEvaluar.toString()}, el polinomio interpolante exacto de grado ${grado} obtiene P(${valorEvaluar.toString()}) = ${valorInterpolado.toString()}${evalDecStr}. Se encuentra dentro del rango de nodos [${X[0].toString()}, ${X[X.length - 1].toString()}].`
            : `Para x = ${valorEvaluar.toString()}, el polinomio obtiene P(${valorEvaluar.toString()}) = ${valorInterpolado.toString()}${evalDecStr}. Nota: se encuentra fuera del intervalo [${X[0].toString()}, ${X[X.length - 1].toString()}], por lo que corresponde a una extrapolación polinómica.`;

        // 7. Fórmulas Matemáticas con KaTeX y fallback
        const formaNewton = generarFormaNewton(X, coeficientes);
        renderizarFormulaMath(
            el.polinomioNewtonKatex,
            el.polinomioNewtonFallback,
            formaNewton.latex,
            formaNewton.plano
        );

        const formaEstandar = generarFormaEstandar(polinomioEstandar);
        renderizarFormulaMath(
            el.polinomioEstandarKatex,
            el.polinomioEstandarFallback,
            formaEstandar.latex,
            formaEstandar.plano
        );

        // 8. Tablas de detalle
        renderizarTablaDiferencias(X, tabla);
        renderizarTablaValidacion(X, Y, coeficientes);

        // 9. Gráfica Interactiva
        prepararDatosGrafica(X, Y, coeficientes, valorEvaluar);
        redibujarGrafica();

    } catch (error) {
        mostrarMensajeError(error.message);
        console.error("Error al resolver:", error);
    }
}

function cargarEjemplo() {
    el.vectorX.value = "1, 2, 4, 7";
    el.vectorY.value = "45, 65, 110, 220";
    el.valorEvaluar.value = "5";
    resolverInterpolacion();
}

function limpiarCampos() {
    el.vectorX.value = "";
    el.vectorY.value = "";
    el.valorEvaluar.value = "";
    ocultarMensajeAlerta();
    el.vectorX.focus();
}

// Inicializar la aplicación al cargar
document.addEventListener("DOMContentLoaded", () => {
    resolverInterpolacion();
});

if (document.readyState === "complete" || document.readyState === "interactive") {
    setTimeout(resolverInterpolacion, 50);
}
