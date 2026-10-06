/**
 * ============================================================================
 * INTERPOLACIÓN POLINOMIAL DE NEWTON (DIFERENCIAS DIVIDIDAS)
 * Solucionador General para Métodos Numéricos
 * ============================================================================
 */

"use strict";

const EPSILON = 1e-9;

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
    valorEvaluar: 0,
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
   1. PARSEO Y VALIDACIÓN DE DATOS (FLEXIBLE PARA CUALQUIER PROBLEMA)
   ========================================================================== */

/**
 * Parsea un vector numérico aceptando comas, espacios, punto y coma, tabuladores y saltos de línea.
 */
function parsearVector(cadena) {
    if (!cadena || typeof cadena !== "string") return [];
    return cadena
        .trim()
        .split(/[\s,;\n\t]+/)
        .filter(v => v !== "")
        .map(v => Number(v));
}

function validarEntradas(X, Y, valorEvaluar) {
    if (!Array.isArray(X) || X.length < 2) {
        throw new Error("Se requieren al menos 2 nodos para construir un polinomio interpolante (grado n ≥ 1).");
    }

    if (X.length !== Y.length) {
        throw new Error(`Los vectores deben tener la misma cantidad de elementos: el vector X tiene ${X.length} nodos y el vector Y tiene ${Y.length} valores.`);
    }

    if (X.some(val => !Number.isFinite(val))) {
        throw new Error("El vector X contiene elementos no numéricos, caracteres inválidos o valores infinitos.");
    }

    if (Y.some(val => !Number.isFinite(val))) {
        throw new Error("El vector Y contiene elementos no numéricos, caracteres inválidos o valores infinitos.");
    }

    if (!Number.isFinite(valorEvaluar)) {
        throw new Error("El punto a evaluar x no es un número válido.");
    }

    // Verificar nodos duplicados en X (división entre cero en diferencias divididas)
    const setX = new Set(X);
    if (setX.size !== X.length) {
        throw new Error("El vector X contiene nodos repetidos. En la interpolación de Newton, todos los x_i deben ser distintos para evitar división entre cero en las diferencias divididas.");
    }
}

/* ==========================================================================
   2. ALGORITMOS NUMÉRICOS DE NEWTON
   ========================================================================== */

/**
 * Construye la tabla triangular de diferencias divididas de orden O(n^2).
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
            const numerador = tabla[i + 1][orden - 1] - tabla[i][orden - 1];
            const denominador = X[i + orden] - X[i];
            tabla[i][orden] = numerador / denominador;
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
        resultado = coeficientes[i] + (x - X[i]) * resultado;
    }

    return resultado;
}

/**
 * Expansión algebraica del polinomio a forma estándar:
 * P(x) = a_n * x^n + ... + a_1 * x + a_0
 */
function sumarPolinomios(p1, p2) {
    const longitud = Math.max(p1.length, p2.length);
    const resultado = Array(longitud).fill(0);
    for (let i = 0; i < longitud; i++) {
        resultado[i] = (p1[i] || 0) + (p2[i] || 0);
    }
    return resultado;
}

function multiplicarPorFactor(polinomio, raiz) {
    // Multiplica polinomio por (x - raiz)
    const resultado = Array(polinomio.length + 1).fill(0);
    for (let i = 0; i < polinomio.length; i++) {
        resultado[i] += -raiz * polinomio[i];
        resultado[i + 1] += polinomio[i];
    }
    return resultado;
}

function obtenerPolinomioEstandar(X, coeficientes) {
    let acumulado = [0];
    let productoBase = [1];

    for (let i = 0; i < coeficientes.length; i++) {
        const ci = coeficientes[i];
        const termino = productoBase.map(c => c * ci);
        acumulado = sumarPolinomios(acumulado, termino);
        productoBase = multiplicarPorFactor(productoBase, X[i]);
    }

    return acumulado; // [a_0, a_1, a_2, ..., a_n]
}

/* ==========================================================================
   3. FORMATEO MATEMÁTICO INTELIGENTE (6 DECIMALES FIJOS)
   ========================================================================== */

function limpiarCero(num) {
    return Math.abs(num) < EPSILON ? 0 : num;
}

/**
 * Formateo inteligente adaptable: 6 decimales fijos o notación científica para valores extremos.
 */
function formatearNumero(num, maxDec = 6) {
    const limpio = limpiarCero(num);
    if (limpio === 0) return "0";
    if (Number.isInteger(limpio)) return limpio.toString();

    const absVal = Math.abs(limpio);
    if (absVal < 1e-5 || absVal >= 1e7) {
        return limpio.toExponential(4).replace("e+", "e");
    }

    return parseFloat(limpio.toFixed(maxDec)).toString();
}

/**
 * Genera el string LaTeX y texto plano para la forma de Newton.
 */
function generarFormaNewton(X, coeficientes) {
    const n = coeficientes.length;
    const partesLatex = [];
    const partesPlanas = [];

    for (let i = 0; i < n; i++) {
        const c = limpiarCero(coeficientes[i]);
        if (c === 0 && i > 0) continue;

        const cAbs = Math.abs(c);
        const cStr = formatearNumero(cAbs);

        let factoresLatex = "";
        let factoresPlanos = "";

        for (let j = 0; j < i; j++) {
            const xj = limpiarCero(X[j]);
            if (xj === 0) {
                factoresLatex += "x";
                factoresPlanos += "x";
            } else if (xj > 0) {
                factoresLatex += `(x - ${formatearNumero(xj)})`;
                factoresPlanos += `(x - ${formatearNumero(xj)})`;
            } else {
                factoresLatex += `(x + ${formatearNumero(Math.abs(xj))})`;
                factoresPlanos += `(x + ${formatearNumero(Math.abs(xj))})`;
            }
        }

        const terminoLatex = (factoresLatex === "") ? cStr : `${cStr}${factoresLatex}`;
        const terminoPlano = (factoresPlanos === "") ? cStr : `${cStr} ${factoresPlanos}`;

        if (i === 0) {
            partesLatex.push(c < 0 ? `-${terminoLatex}` : terminoLatex);
            partesPlanas.push(c < 0 ? `-${terminoPlano}` : terminoPlano);
        } else {
            const signo = c < 0 ? "-" : "+";
            partesLatex.push(`${signo} ${terminoLatex}`);
            partesPlanas.push(`${signo} ${terminoPlano}`);
        }
    }

    const latex = `P_{${n - 1}}(x) = ` + (partesLatex.join(" ") || "0");
    const plano = `P(x) = ` + (partesPlanas.join(" ") || "0");
    return { latex, plano };
}

/**
 * Genera el string LaTeX y texto plano para la forma estándar.
 */
function generarFormaEstandar(polinomioEstandar) {
    const n = polinomioEstandar.length - 1;
    const partesLatex = [];
    const partesPlanas = [];

    for (let i = n; i >= 0; i--) {
        const coef = limpiarCero(polinomioEstandar[i]);
        if (coef === 0) continue;

        const coefAbs = Math.abs(coef);
        let coefStr = formatearNumero(coefAbs);
        if (coefAbs === 1 && i > 0) coefStr = "";

        let varLatex = "";
        let varPlana = "";

        if (i === 1) {
            varLatex = "x";
            varPlana = "x";
        } else if (i > 1) {
            varLatex = `x^{${i}}`;
            varPlana = `x^${i}`;
        }

        const terminoLatex = `${coefStr}${varLatex}`;
        const terminoPlano = `${coefStr}${varPlana}`;

        const esPrimerTermino = partesLatex.length === 0;

        if (esPrimerTermino) {
            partesLatex.push(coef < 0 ? `-${terminoLatex}` : terminoLatex);
            partesPlanas.push(coef < 0 ? `-${terminoPlano}` : terminoPlano);
        } else {
            const signo = coef < 0 ? "-" : "+";
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
   4. RENDERIZADO DE TABLAS
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
        tdX.textContent = formatearNumero(X[i]);
        tr.appendChild(tdX);

        for (let orden = 0; orden < X.length; orden++) {
            const td = document.createElement("td");
            const val = tabla[i][orden];

            if (val === null || val === undefined) {
                td.textContent = "—";
                td.className = "empty-cell";
            } else {
                td.textContent = formatearNumero(val);
                // Si es la fila 0, resaltar porque es el coeficiente de Newton c_orden
                if (i === 0) {
                    td.classList.add("coeff-cell");
                    td.title = `Coeficiente c_${orden} de Newton`;
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
    let maxError = 0;

    for (let i = 0; i < X.length; i++) {
        const xi = X[i];
        const yiOriginal = Y[i];
        const yiCalculado = evaluarNewton(X, coeficientes, xi);
        const errorAbs = Math.abs(yiOriginal - yiCalculado);

        if (errorAbs > maxError) maxError = errorAbs;

        const esExacto = errorAbs < 1e-7;
        if (!esExacto) todoExacto = false;

        const tr = document.createElement("tr");

        tr.innerHTML = `
            <td>${i}</td>
            <td>${formatearNumero(xi)}</td>
            <td>${formatearNumero(yiOriginal)}</td>
            <td>${formatearNumero(yiCalculado)}</td>
            <td>${errorAbs < 1e-12 ? "0" : errorAbs.toExponential(2)}</td>
            <td>
                <span class="${esExacto ? 'status-cell-pass' : 'status-cell-fail'}">
                    ${esExacto ? '✓ Coincide exacto' : '✗ Discrepancia'}
                </span>
            </td>
        `;

        tbody.appendChild(tr);
    }

    if (todoExacto) {
        el.badgeValidacionGlobal.textContent = "Validación Exitosa";
        el.badgeValidacionGlobal.className = "badge-success";
        el.mensajeValidacionTexto.textContent = 
            `El polinomio pasa exactamente por todos los ${X.length} puntos ingresados (|P_n(x_i) - y_i| < 1e-7). Comprobación superada.`;
    } else {
        el.badgeValidacionGlobal.textContent = "Revisar datos";
        el.badgeValidacionGlobal.className = "detail-badge warning";
        el.mensajeValidacionTexto.textContent = 
            `Se detectaron discrepancias mayores a la tolerancia en los nodos. Verifique la entrada.`;
    }
}

/* ==========================================================================
   5. GRÁFICA CANVAS INTERACTIVA (HIDPI + TOOLTIP + GUÍAS)
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
    const xMinDatos = Math.min(...X);
    const xMaxDatos = Math.max(...X);
    const margenX = Math.max((xMaxDatos - xMinDatos) * 0.12, 0.5);

    const xMin = Math.min(xMinDatos, valorEvaluar) - margenX;
    const xMax = Math.max(xMaxDatos, valorEvaluar) + margenX;

    const muestras = [];
    const numPuntos = 250;

    for (let i = 0; i <= numPuntos; i++) {
        const x = xMin + (xMax - xMin) * (i / numPuntos);
        const y = evaluarNewton(X, coeficientes, x);
        muestras.push({ x, y });
    }

    const yValores = [...Y, evaluarNewton(X, coeficientes, valorEvaluar), ...muestras.map(m => m.y)];
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
        ctx.fillText(formatearNumero(valY), m.izq - 8, py);
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
        ctx.fillText(formatearNumero(valX), px, h - m.inf + 8);
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

    // Títulos de ejes generales
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
    const yEval = evaluarNewton(chartState.X, chartState.coeficientes, chartState.valorEvaluar);
    const pxEval = toPxX(chartState.valorEvaluar);
    const pyEval = toPxY(yEval);

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

    // 5. Nodos de interpolación (rojo con borde blanco)
    chartState.X.forEach((xi, i) => {
        const yi = chartState.Y[i];
        const px = toPxX(xi);
        const py = toPxY(yi);

        // Aro exterior
        ctx.fillStyle = "#ffffff";
        ctx.beginPath();
        ctx.arc(px, py, 6, 0, Math.PI * 2);
        ctx.fill();

        // Relleno
        ctx.fillStyle = "#ef4444";
        ctx.beginPath();
        ctx.arc(px, py, 4.5, 0, Math.PI * 2);
        ctx.fill();

        // Etiqueta
        ctx.fillStyle = "#475569";
        ctx.font = "500 11px Inter, sans-serif";
        ctx.textAlign = "center";
        ctx.fillText(`(${formatearNumero(xi)}, ${formatearNumero(yi)})`, px, py - 10);
    });

    // 6. Punto evaluado destacado (verde esmeralda)
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
        `P(${formatearNumero(chartState.valorEvaluar)}) = ${formatearNumero(yEval)}`,
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
    const yVal = evaluarNewton(chartState.X, chartState.coeficientes, xVal);

    chartState.isHovering = true;
    chartState.hoverPoint = { x: xVal, y: yVal };

    el.chartTooltip.style.left = `${mouseX}px`;
    el.chartTooltip.style.top = `${mouseY}px`;
    el.chartTooltip.innerHTML = `<strong>x:</strong> ${formatearNumero(xVal)}<br><strong>P(x):</strong> ${formatearNumero(yVal)}`;
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
   6. CONTROLADOR PRINCIPAL: RESOLUCIÓN Y ACTUALIZACIÓN
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
        const valorEvaluar = Number(el.valorEvaluar.value);

        // 1. Validaciones
        validarEntradas(X, Y, valorEvaluar);

        // 2. Ordenamiento opcional por x creciente
        if (el.checkOrdenarX && el.checkOrdenarX.checked) {
            const pares = X.map((xVal, idx) => ({ x: xVal, y: Y[idx] }));
            pares.sort((a, b) => a.x - b.x);
            X = pares.map(p => p.x);
            Y = pares.map(p => p.y);
            // Actualizar campos si se ordenaron
            el.vectorX.value = X.join(", ");
            el.vectorY.value = Y.join(", ");
        }

        // 3. Tabla de diferencias divididas
        const tabla = calcularDiferenciasDivididas(X, Y);

        // Coeficientes de Newton (primera fila c_j = tabla[0][j])
        const coeficientes = tabla[0].slice(0, X.length);

        // 4. Evaluación en el punto solicitado x
        const valorInterpolado = evaluarNewton(X, coeficientes, valorEvaluar);

        // 5. Polinomio estándar expandido
        const polinomioEstandar = obtenerPolinomioEstandar(X, coeficientes);

        // 6. Actualizar métricas destacadas
        const grado = X.length - 1;
        el.badgeGrado.textContent = `Grado n = ${grado}`;
        el.resultadoLatencia.textContent = formatearNumero(valorInterpolado);
        el.resultadoCarga.textContent = `x = ${formatearNumero(valorEvaluar)}`;

        const xMinDatos = Math.min(...X);
        const xMaxDatos = Math.max(...X);
        const esInterpolacion = (valorEvaluar >= xMinDatos && valorEvaluar <= xMaxDatos);

        el.badgeTipoEvaluacion.textContent = esInterpolacion ? "Interpolación" : "Extrapolación";
        el.badgeTipoEvaluacion.className = `detail-badge ${esInterpolacion ? "success" : "warning"}`;

        el.explicacionResultado.textContent = esInterpolacion
            ? `Para x = ${formatearNumero(valorEvaluar)}, el polinomio interpolante de grado ${grado} obtiene P(${formatearNumero(valorEvaluar)}) = ${formatearNumero(valorInterpolado)}. Se encuentra dentro del rango de nodos [${formatearNumero(xMinDatos)}, ${formatearNumero(xMaxDatos)}].`
            : `Para x = ${formatearNumero(valorEvaluar)}, el polinomio obtiene P(${formatearNumero(valorEvaluar)}) = ${formatearNumero(valorInterpolado)}. Nota: se encuentra fuera del intervalo [${formatearNumero(xMinDatos)}, ${formatearNumero(xMaxDatos)}], por lo que corresponde a una extrapolación polinómica.`;

        // 7. Fórmulas Matemáticas
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
