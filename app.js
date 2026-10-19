/**
 * ============================================================================
 * INTERPOLACIÓN POLINOMIAL: NEWTON Y NEWTON-GREGORY (ARITMÉTICA EXACTA)
 * Solucionador General para Métodos Numéricos con Fracciones (BigInt)
 * ============================================================================
 */

"use strict";

// Elementos del DOM
const el = {
    // Formulario y opciones
    vectorX: document.getElementById("vectorX"),
    vectorY: document.getElementById("vectorY"),
    valorEvaluar: document.getElementById("valorEvaluar"),
    checkOrdenarX: document.getElementById("checkOrdenarX"),
    btnResolver: document.getElementById("btnResolver"),
    btnEjemplo: document.getElementById("btnEjemplo"),
    btnEjemploEqui: document.getElementById("btnEjemploEqui"),
    btnEjemploError: document.getElementById("btnEjemploError"),
    btnLimpiar: document.getElementById("btnLimpiar"),
    mensajeAlerta: document.getElementById("mensajeAlerta"),
    
    // Función analítica opcional y cota de derivada
    btnToggleOpcional: document.getElementById("btnToggleOpcional"),
    iconoToggleOpcional: document.getElementById("iconoToggleOpcional"),
    contenidoOpcional: document.getElementById("contenidoOpcional"),
    funcionFx: document.getElementById("funcionFx"),
    btnGenerarY: document.getElementById("btnGenerarY"),
    cotaDerivadaM: document.getElementById("cotaDerivadaM"),

    // Selector de método e indicador de paso h
    selectorMetodo: document.getElementById("selectorMetodo"),
    badgePasoH: document.getElementById("badgePasoH"),
    textoPasoH: document.getElementById("textoPasoH"),

    // Resultados
    panelResultado: document.getElementById("panelResultado"),
    badgeGrado: document.getElementById("badgeGrado"),
    resultadoLatencia: document.getElementById("resultadoLatencia"),
    resultadoCarga: document.getElementById("resultadoCarga"),
    badgeParametroS: document.getElementById("badgeParametroS"),
    badgeTipoEvaluacion: document.getElementById("badgeTipoEvaluacion"),
    explicacionResultado: document.getElementById("explicacionResultado"),

    // Límite Superior del Error (Teorema del Residuo)
    panelLimiteError: document.getElementById("panelLimiteError"),
    badgeEstadoError: document.getElementById("badgeEstadoError"),
    formulaErrorTeoremaKatex: document.getElementById("formulaErrorTeoremaKatex"),
    formulaErrorSustituidaKatex: document.getElementById("formulaErrorSustituidaKatex"),
    valTerminoNodos: document.getElementById("valTerminoNodos"),
    subTerminoNodos: document.getElementById("subTerminoNodos"),
    valCotaDerivada: document.getElementById("valCotaDerivada"),
    subCotaDerivada: document.getElementById("subCotaDerivada"),
    valCotaTeorica: document.getElementById("valCotaTeorica"),
    subCotaTeorica: document.getElementById("subCotaTeorica"),
    valErrorReal: document.getElementById("valErrorReal"),
    subErrorReal: document.getElementById("subErrorReal"),
    cardErrorReal: document.getElementById("cardErrorReal"),
    desglosePasosError: document.getElementById("desglosePasosError"),
    listaFactoresError: document.getElementById("listaFactoresError"),
    textoDigitosSignificativos: document.getElementById("textoDigitosSignificativos"),

    // Polinomios
    subtituloPolinomios: document.getElementById("subtituloPolinomios"),
    tituloPolinomioNewton: document.getElementById("tituloPolinomioNewton"),
    polinomioNewtonKatex: document.getElementById("polinomioNewtonKatex"),
    polinomioNewtonFallback: document.getElementById("polinomioNewtonFallback"),
    polinomioEstandarKatex: document.getElementById("polinomioEstandarKatex"),
    polinomioEstandarFallback: document.getElementById("polinomioEstandarFallback"),

    // Tablas
    tituloTablaDiferencias: document.getElementById("tituloTablaDiferencias"),
    subtituloTablaDiferencias: document.getElementById("subtituloTablaDiferencias"),
    tablaDiferencias: document.getElementById("tablaDiferencias"),
    tablaValidacion: document.getElementById("tablaValidacion"),
    badgeValidacionGlobal: document.getElementById("badgeValidacionGlobal"),
    mensajeValidacionTexto: document.getElementById("mensajeValidacionTexto"),

    // Gráfica
    canvas: document.getElementById("graficaLatencia"),
    chartTooltip: document.getElementById("chartTooltip")
};

// Estado global de la aplicación
let appState = {
    metodo: "divididas", // "divididas" | "ng-adelante" | "ng-atras" | "auto"
    metodoActivo: "divididas"
};

let chartState = {
    X: [],
    Y: [],
    coeficientesNewton: [],
    valorEvaluar: null,
    muestras: [],
    xMin: 0,
    xMax: 0,
    yMin: 0,
    yMax: 0,
    margen: { izq: 60, der: 24, sup: 24, inf: 48 },
    hoverPoint: null,
    isHovering: false,
    evaluador: null
};

/* ==========================================================================
   1. CLASE FRACCIÓN PARA ARITMÉTICA RACIONAL EXACTA (BIGINT)
   ========================================================================== */

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

function factorial(k) {
    let res = 1n;
    for (let i = 2n; i <= BigInt(k); i++) {
        res *= i;
    }
    return new Fraccion(res, 1n);
}

/* ==========================================================================
   2. PARSEO DE FRACCIONES Y NÚMEROS ARBITRARIOS (SIN PÉRDIDA DE PRECISIÓN)
   ========================================================================== */

function parsearFraccion(texto) {
    if (!texto || typeof texto !== "string") {
        throw new Error("Valor vacío o inválido.");
    }
    texto = texto.trim();

    if (texto.includes("/")) {
        const partes = texto.split("/");
        if (partes.length !== 2) {
            throw new Error(`Fracción mal formada: "${texto}".`);
        }
        const fNum = parsearFraccion(partes[0]);
        const fDen = parsearFraccion(partes[1]);
        return fNum.div(fDen);
    }

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

    return new Fraccion(BigInt(texto), 1n);
}

function parsearVector(cadena) {
    if (!cadena || typeof cadena !== "string") return [];
    const normalizada = cadena.replace(/\s*\/\s*/g, "/");
    return normalizada
        .trim()
        .split(/[\s,;\n\t]+/)
        .filter(v => v !== "")
        .map(v => parsearFraccion(v));
}

function verificarEquiespaciado(X) {
    if (!Array.isArray(X) || X.length < 2) {
        return { esEquiespaciado: false, h: null };
    }
    const h = X[1].sub(X[0]);
    if (h.isZero()) {
        return { esEquiespaciado: false, h: null };
    }
    for (let i = 1; i < X.length - 1; i++) {
        const paso = X[i + 1].sub(X[i]);
        if (!paso.equals(h)) {
            return { esEquiespaciado: false, h: null };
        }
    }
    return { esEquiespaciado: true, h };
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

    for (let i = 0; i < X.length; i++) {
        for (let j = i + 1; j < X.length; j++) {
            if (X[i].equals(X[j])) {
                throw new Error(`El vector X contiene nodos repetidos (${X[i].toString()}). Todos los nodos x_i deben ser distintos para evitar división entre cero.`);
            }
        }
    }
}

/* ==========================================================================
   3. ALGORITMOS NUMÉRICOS: DIFERENCIAS DIVIDIDAS Y FINITAS (NEWTON-GREGORY)
   ========================================================================== */

/**
 * Tabla de Diferencias Divididas f[x_i, ..., x_{i+k}]
 */
function calcularDiferenciasDivididas(X, Y) {
    const n = X.length;
    const tabla = Array.from({ length: n }, () => Array(n).fill(null));

    for (let i = 0; i < n; i++) tabla[i][0] = Y[i];

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
 * Tabla de Diferencias Finitas Ordinarias Δ^k y_i
 * (Sin dividir entre h; empleada en Newton-Gregory)
 */
function calcularDiferenciasFinitas(X, Y) {
    const n = X.length;
    const tabla = Array.from({ length: n }, () => Array(n).fill(null));

    for (let i = 0; i < n; i++) tabla[i][0] = Y[i];

    for (let orden = 1; orden < n; orden++) {
        for (let i = 0; i < n - orden; i++) {
            tabla[i][orden] = tabla[i + 1][orden - 1].sub(tabla[i][orden - 1]);
        }
    }
    return tabla;
}

/**
 * Evaluación de Newton Divididas con Horner
 */
function evaluarNewtonDivididas(X, coeficientes, x) {
    const n = coeficientes.length;
    let resultado = coeficientes[n - 1];

    for (let i = n - 2; i >= 0; i--) {
        const factor = x.sub(X[i]);
        resultado = coeficientes[i].add(factor.mul(resultado));
    }
    return resultado;
}

/**
 * Evaluación de Newton-Gregory Hacia Adelante (Progresivo con parámetro s)
 * P(s) = y0 + s*Δy0 + s(s-1)/2! * Δ^2y0 + ...
 */
function evaluarNewtonGregoryAdelante(Y, tablaDelta, h, x0, x) {
    const n = Y.length;
    const s = x.sub(x0).div(h);
    let resultado = new Fraccion(0n);
    let productoS = new Fraccion(1n);

    for (let k = 0; k < n; k++) {
        const deltaK = tablaDelta[0][k];
        const factK = factorial(k);
        const coef = deltaK.div(factK);
        resultado = resultado.add(coef.mul(productoS));
        productoS = productoS.mul(s.sub(new Fraccion(k)));
    }
    return { valor: resultado, s };
}

/**
 * Evaluación de Newton-Gregory Hacia Atrás (Regresivo con parámetro s)
 * P(s) = yn + s*∇yn + s(s+1)/2! * ∇^2yn + ...
 * Donde ∇^k yn = tablaDelta[n - 1 - k][k]
 */
function evaluarNewtonGregoryAtras(Y, tablaDelta, h, xn, x) {
    const n = Y.length;
    const s = x.sub(xn).div(h);
    let resultado = new Fraccion(0n);
    let productoS = new Fraccion(1n);

    for (let k = 0; k < n; k++) {
        const nablaK = tablaDelta[n - 1 - k][k];
        const factK = factorial(k);
        const coef = nablaK.div(factK);
        resultado = resultado.add(coef.mul(productoS));
        productoS = productoS.mul(s.add(new Fraccion(k)));
    }
    return { valor: resultado, s };
}

/**
 * Expansión algebraica del polinomio a forma estándar P(x) = a_n*x^n + ... + a_0
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

    return acumulado;
}

/* ==========================================================================
   4. FORMATEO MATEMÁTICO EN LATEX / KATEX Y TEXTO PLANO
   ========================================================================== */

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

function generarFormaNewtonGregoryAdelante(X, Y, tablaDelta, h) {
    const n = X.length;
    const x0 = X[0];
    const partesLatex = [];
    const partesPlanas = [];

    for (let k = 0; k < n; k++) {
        const deltaK = tablaDelta[0][k];
        if (deltaK.isZero() && k > 0) continue;

        const factK = factorial(k);
        const coef = deltaK.div(factK);
        const coefAbs = coef.abs();
        const esUnoConFactores = (coefAbs.num === 1n && coefAbs.den === 1n && k > 0);

        const coefLatex = esUnoConFactores ? "" : coefAbs.toLatex();
        const coefPlano = esUnoConFactores ? "" : (coefAbs.den === 1n ? coefAbs.num.toString() : `(${coefAbs.toString()})`);

        let factoresLatex = "";
        let factoresPlanos = "";

        for (let j = 0; j < k; j++) {
            if (j === 0) {
                factoresLatex += "s";
                factoresPlanos += "s";
            } else {
                factoresLatex += `(s - ${j})`;
                factoresPlanos += `(s - ${j})`;
            }
        }

        const terminoLatex = (factoresLatex === "") ? coefLatex : `${coefLatex}${factoresLatex}`;
        const terminoPlano = (factoresPlanos === "") ? coefPlano : `${coefPlano}${factoresPlanos}`;

        if (k === 0) {
            partesLatex.push(coef.isNegative() ? `-${terminoLatex}` : terminoLatex);
            partesPlanas.push(coef.isNegative() ? `-${terminoPlano}` : terminoPlano);
        } else {
            const signo = coef.isNegative() ? "-" : "+";
            partesLatex.push(`${signo} ${terminoLatex}`);
            partesPlanas.push(`${signo} ${terminoPlano}`);
        }
    }

    const formulaS_Latex = `s = \\frac{x - ${x0.toLatex()}}{${h.toLatex()}}, \\quad P_{${n - 1}}(s) = ` + (partesLatex.join(" ") || "0");
    const formulaS_Plano = `s = (x - ${x0.toString()})/${h.toString()}, P(s) = ` + (partesPlanas.join(" ") || "0");

    return { latex: formulaS_Latex, plano: formulaS_Plano };
}

function generarFormaNewtonGregoryAtras(X, Y, tablaDelta, h) {
    const n = X.length;
    const xn = X[n - 1];
    const partesLatex = [];
    const partesPlanas = [];

    for (let k = 0; k < n; k++) {
        const nablaK = tablaDelta[n - 1 - k][k];
        if (nablaK.isZero() && k > 0) continue;

        const factK = factorial(k);
        const coef = nablaK.div(factK);
        const coefAbs = coef.abs();
        const esUnoConFactores = (coefAbs.num === 1n && coefAbs.den === 1n && k > 0);

        const coefLatex = esUnoConFactores ? "" : coefAbs.toLatex();
        const coefPlano = esUnoConFactores ? "" : (coefAbs.den === 1n ? coefAbs.num.toString() : `(${coefAbs.toString()})`);

        let factoresLatex = "";
        let factoresPlanos = "";

        for (let j = 0; j < k; j++) {
            if (j === 0) {
                factoresLatex += "s";
                factoresPlanos += "s";
            } else {
                factoresLatex += `(s + ${j})`;
                factoresPlanos += `(s + ${j})`;
            }
        }

        const terminoLatex = (factoresLatex === "") ? coefLatex : `${coefLatex}${factoresLatex}`;
        const terminoPlano = (factoresPlanos === "") ? coefPlano : `${coefPlano}${factoresPlanos}`;

        if (k === 0) {
            partesLatex.push(coef.isNegative() ? `-${terminoLatex}` : terminoLatex);
            partesPlanas.push(coef.isNegative() ? `-${terminoPlano}` : terminoPlano);
        } else {
            const signo = coef.isNegative() ? "-" : "+";
            partesLatex.push(`${signo} ${terminoLatex}`);
            partesPlanas.push(`${signo} ${terminoPlano}`);
        }
    }

    const formulaS_Latex = `s = \\frac{x - ${xn.toLatex()}}{${h.toLatex()}}, \\quad P_{${n - 1}}(s) = ` + (partesLatex.join(" ") || "0");
    const formulaS_Plano = `s = (x - ${xn.toString()})/${h.toString()}, P(s) = ` + (partesPlanas.join(" ") || "0");

    return { latex: formulaS_Latex, plano: formulaS_Plano };
}

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
   5. RENDERIZADO DE TABLAS (DIVIDIDAS VS FINITAS ADELANTE / ATRÁS)
   ========================================================================== */

function renderizarTablaDiferencias(X, tabla, metodo) {
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

    const esDivididas = (metodo === "divididas");
    const esAtras = (metodo === "ng-atras");

    for (let orden = 0; orden < X.length; orden++) {
        const th = document.createElement("th");
        if (orden === 0) {
            th.textContent = esDivididas ? "f[xᵢ]" : "yᵢ";
        } else if (esDivididas) {
            th.textContent = `${orden}.ª dividida`;
        } else if (esAtras) {
            th.textContent = (orden === 1) ? "∇yᵢ" : `∇${orden}yᵢ`;
        } else {
            th.textContent = (orden === 1) ? "Δyᵢ" : `Δ${orden}yᵢ`;
        }
        trHead.appendChild(th);
    }
    thead.appendChild(trHead);

    const n = X.length;
    for (let i = 0; i < n; i++) {
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

        for (let orden = 0; orden < n; orden++) {
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

                // Resaltado de coeficientes según el método:
                if (esDivididas && i === 0) {
                    td.classList.add("coeff-cell");
                    td.title = `Coeficiente c_${orden} = ${val.toString()}` + (val.den !== 1n ? ` (≈ ${val.toDecimalString(6)})` : "");
                } else if (!esDivididas && !esAtras && i === 0) {
                    // Newton-Gregory Adelante: primera fila Δ^k y0
                    td.classList.add("coeff-cell");
                    td.title = `Diferencia progresiva Δ^${orden} y0 = ${val.toString()}`;
                } else if (!esDivididas && esAtras && (i === n - 1 - orden)) {
                    // Newton-Gregory Atrás: diagonal regresiva ∇^k yn
                    td.classList.add("coeff-cell-backward");
                    td.title = `Diferencia regresiva ∇^${orden} yn = ${val.toString()}`;
                }
            }
            tr.appendChild(td);
        }

        tbody.appendChild(tr);
    }
}

function renderizarTablaValidacion(X, Y, evaluador) {
    const tbody = el.tablaValidacion.querySelector("tbody");
    tbody.innerHTML = "";

    let todoExacto = true;

    for (let i = 0; i < X.length; i++) {
        const xi = X[i];
        const yiOriginal = Y[i];
        const yiCalculado = evaluador(xi);
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

function prepararDatosGrafica(X, Y, evaluador, valorEvaluar) {
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
        const xFrac = parsearFraccion(xVal.toFixed(8));
        const yFrac = evaluador(xFrac);
        muestras.push({ x: xVal, y: yFrac.toNumber() });
    }

    const yValores = [...yNums, evaluador(valorEvaluar).toNumber(), ...muestras.map(m => m.y)];
    const yMinDatos = Math.min(...yValores);
    const yMaxDatos = Math.max(...yValores);
    const margenY = Math.max((yMaxDatos - yMinDatos) * 0.14, 1);

    const yMin = yMinDatos - margenY;
    const yMax = yMaxDatos + margenY;

    chartState = {
        ...chartState,
        X,
        Y,
        evaluador,
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
    const yEvalFrac = chartState.evaluador(chartState.valorEvaluar);
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

    // 6. Punto evaluado destacado
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

el.canvas.addEventListener("mousemove", (e) => {
    if (!chartState.muestras || chartState.muestras.length === 0 || !chartState.evaluador) return;

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
    const yFrac = chartState.evaluador(xFrac);

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
   8. MOTOR ANALÍTICO Y ESTIMACIÓN DEL LÍMITE SUPERIOR DE ERROR
   ========================================================================== */

function tokenizarExpresion(expr) {
    if (!expr || typeof expr !== "string") {
        throw new Error("Expresión analítica vacía o inválida.");
    }

    let texto = expr.trim().replace(/\s+/g, "");
    const regex = /([0-9]+(?:\.[0-9]+)?|[a-zA-Z_][a-zA-Z0-9_]*|\*\*|\^|[+\-*/(),])/g;
    const tokensCrudos = [];
    let match;
    let indexEsperado = 0;

    while ((match = regex.exec(texto)) !== null) {
        if (match.index !== indexEsperado) {
            const charInvalido = texto.substring(indexEsperado, match.index);
            throw new Error(`Carácter no reconocido en la expresión: "${charInvalido}"`);
        }
        tokensCrudos.push(match[1]);
        indexEsperado = regex.lastIndex;
    }

    if (indexEsperado < texto.length) {
        throw new Error(`Sintaxis inválida al final de la expresión: "${texto.substring(indexEsperado)}"`);
    }

    const tokens = [];
    const esFinFactor = (t) => /^[0-9]+(?:\.[0-9]+)?$/.test(t) || t === ")" || /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(t);
    const esInicioFactor = (t) => /^[0-9]+(?:\.[0-9]+)?$/.test(t) || t === "(" || /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(t);

    for (let i = 0; i < tokensCrudos.length; i++) {
        const actual = tokensCrudos[i];
        tokens.push(actual);

        if (i < tokensCrudos.length - 1) {
            const siguiente = tokensCrudos[i + 1];
            if (esFinFactor(actual) && esInicioFactor(siguiente)) {
                const funcionesConocidas = ["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs"];
                if (!(funcionesConocidas.includes(actual.toLowerCase()) && siguiente === "(")) {
                    tokens.push("*");
                }
            }
        }
    }

    return tokens;
}

function parsearExpresionMatematica(expr) {
    const tokens = tokenizarExpresion(expr);
    let pos = 0;

    function peek() { return tokens[pos]; }
    function consume() { return tokens[pos++]; }

    function parseExpr() {
        let node = parseTerm();
        while (peek() === "+" || peek() === "-") {
            const op = consume();
            const right = parseTerm();
            node = { type: "binary", op, left: node, right };
        }
        return node;
    }

    function parseTerm() {
        let node = parsePower();
        while (peek() === "*" || peek() === "/") {
            const op = consume();
            const right = parsePower();
            node = { type: "binary", op, left: node, right };
        }
        return node;
    }

    function parsePower() {
        let node = parseUnary();
        if (peek() === "^" || peek() === "**") {
            consume();
            const right = parsePower();
            node = { type: "binary", op: "^", left: node, right };
        }
        return node;
    }

    function parseUnary() {
        if (peek() === "-") {
            consume();
            return { type: "unary", op: "-", arg: parseUnary() };
        }
        if (peek() === "+") {
            consume();
            return parseUnary();
        }
        return parsePrimary();
    }

    function parsePrimary() {
        const tok = consume();
        if (!tok) throw new Error("Expresión incompleta. Se esperaba un número, variable o '('");

        if (tok === "(") {
            const subExpr = parseExpr();
            if (consume() !== ")") {
                throw new Error("Paréntesis sin cerrar ')'");
            }
            return subExpr;
        }

        if (/^[0-9]+(?:\.[0-9]+)?$/.test(tok)) {
            return { type: "num", value: parseFloat(tok) };
        }

        const id = tok.toLowerCase();
        if (id === "x" || id === "t") {
            return { type: "var", name: "x" };
        }
        if (id === "pi") return { type: "num", value: Math.PI };
        if (id === "e") return { type: "num", value: Math.E };

        const funcionesConocidas = ["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs"];
        if (funcionesConocidas.includes(id)) {
            if (peek() !== "(") {
                throw new Error(`Se esperaba '(' después del nombre de la función: "${tok}"`);
            }
            consume(); // (
            const arg = parseExpr();
            if (consume() !== ")") {
                throw new Error(`Paréntesis sin cerrar ')' en la función "${tok}"`);
            }
            return { type: "func", name: id, arg };
        }

        throw new Error(`Término no reconocido: "${tok}"`);
    }

    const ast = parseExpr();
    if (pos < tokens.length) {
        throw new Error(`Sintaxis no válida cerca de: "${tokens[pos]}"`);
    }
    return ast;
}

function evaluarAST(ast, x) {
    if (!ast) throw new Error("Árbol de sintaxis nulo.");

    switch (ast.type) {
        case "num":
            return ast.value;

        case "var":
            return x;

        case "unary":
            if (ast.op === "-") return -evaluarAST(ast.arg, x);
            return evaluarAST(ast.arg, x);

        case "binary": {
            const l = evaluarAST(ast.left, x);
            const r = evaluarAST(ast.right, x);
            if (ast.op === "+") return l + r;
            if (ast.op === "-") return l - r;
            if (ast.op === "*") return l * r;
            if (ast.op === "/") {
                if (Math.abs(r) < 1e-15) {
                    throw new Error(`División por cero en f(x) con denominador = 0 en x = ${x}.`);
                }
                return l / r;
            }
            if (ast.op === "^") {
                if (l < 0 && Math.abs(Math.round(r) - r) > 1e-9) {
                    throw new Error(`Potencia no real: base negativa con exponente fraccionario en x = ${x}.`);
                }
                return Math.pow(l, r);
            }
            throw new Error(`Operador binario no soportado: ${ast.op}`);
        }

        case "func": {
            const v = evaluarAST(ast.arg, x);
            switch (ast.name) {
                case "sin": return Math.sin(v);
                case "cos": return Math.cos(v);
                case "tan": {
                    if (Math.abs(Math.cos(v)) < 1e-14) {
                        throw new Error(`Tangente indefinida (asíntota) en x = ${x}.`);
                    }
                    return Math.tan(v);
                }
                case "exp": return Math.exp(v);
                case "ln":
                case "log": {
                    if (v <= 0) {
                        throw new Error(`Logaritmo no definido para argumento no positivo (${v}) en x = ${x}.`);
                    }
                    return Math.log(v);
                }
                case "sqrt": {
                    if (v < 0) {
                        throw new Error(`Raíz cuadrada negativa (${v}) en x = ${x}.`);
                    }
                    return Math.sqrt(v);
                }
                case "abs": return Math.abs(v);
                default:
                    throw new Error(`Función no implementada: ${ast.name}`);
            }
        }

        default:
            throw new Error(`Tipo de nodo AST desconocido: ${ast.type}`);
    }
}

function diferenciarAST(ast) {
    if (!ast) return { type: "num", value: 0 };

    switch (ast.type) {
        case "num":
            return { type: "num", value: 0 };

        case "var":
            return { type: "num", value: 1 };

        case "unary":
            if (ast.op === "-") {
                return { type: "unary", op: "-", arg: diferenciarAST(ast.arg) };
            }
            return diferenciarAST(ast.arg);

        case "binary": {
            const u = ast.left;
            const v = ast.right;
            const du = diferenciarAST(u);
            const dv = diferenciarAST(v);

            if (ast.op === "+" || ast.op === "-") {
                return { type: "binary", op: ast.op, left: du, right: dv };
            }

            if (ast.op === "*") {
                return {
                    type: "binary",
                    op: "+",
                    left: { type: "binary", op: "*", left: du, right: v },
                    right: { type: "binary", op: "*", left: u, right: dv }
                };
            }

            if (ast.op === "/") {
                return {
                    type: "binary",
                    op: "/",
                    left: {
                        type: "binary",
                        op: "-",
                        left: { type: "binary", op: "*", left: du, right: v },
                        right: { type: "binary", op: "*", left: u, right: dv }
                    },
                    right: { type: "binary", op: "^", left: v, right: { type: "num", value: 2 } }
                };
            }

            if (ast.op === "^") {
                if (v.type === "num") {
                    const k = v.value;
                    return {
                        type: "binary",
                        op: "*",
                        left: {
                            type: "binary",
                            op: "*",
                            left: { type: "num", value: k },
                            right: { type: "binary", op: "^", left: u, right: { type: "num", value: k - 1 } }
                        },
                        right: du
                    };
                }
                if (u.type === "num") {
                    return {
                        type: "binary",
                        op: "*",
                        left: {
                            type: "binary",
                            op: "*",
                            left: ast,
                            right: { type: "num", value: Math.log(u.value) }
                        },
                        right: dv
                    };
                }
                return {
                    type: "binary",
                    op: "*",
                    left: ast,
                    right: {
                        type: "binary",
                        op: "+",
                        left: {
                            type: "binary",
                            op: "*",
                            left: dv,
                            right: { type: "func", name: "ln", arg: u }
                        },
                        right: {
                            type: "binary",
                            op: "/",
                            left: { type: "binary", op: "*", left: v, right: du },
                            right: u
                        }
                    }
                };
            }

            throw new Error(`Diferenciación no soportada para operador binario: ${ast.op}`);
        }

        case "func": {
            const u = ast.arg;
            const du = diferenciarAST(u);

            switch (ast.name) {
                case "sin":
                    return {
                        type: "binary",
                        op: "*",
                        left: { type: "func", name: "cos", arg: u },
                        right: du
                    };

                case "cos":
                    return {
                        type: "binary",
                        op: "*",
                        left: { type: "unary", op: "-", arg: { type: "func", name: "sin", arg: u } },
                        right: du
                    };

                case "tan":
                    return {
                        type: "binary",
                        op: "/",
                        left: du,
                        right: {
                            type: "binary",
                            op: "^",
                            left: { type: "func", name: "cos", arg: u },
                            right: { type: "num", value: 2 }
                        }
                    };

                case "exp":
                    return {
                        type: "binary",
                        op: "*",
                        left: ast,
                        right: du
                    };

                case "ln":
                case "log":
                    return {
                        type: "binary",
                        op: "/",
                        left: du,
                        right: u
                    };

                case "sqrt":
                    return {
                        type: "binary",
                        op: "/",
                        left: du,
                        right: {
                            type: "binary",
                            op: "*",
                            left: { type: "num", value: 2 },
                            right: { type: "func", name: "sqrt", arg: u }
                        }
                    };

                case "abs":
                    return {
                        type: "binary",
                        op: "*",
                        left: {
                            type: "binary",
                            op: "/",
                            left: u,
                            right: { type: "func", name: "abs", arg: u }
                        },
                        right: du
                    };

                default:
                    throw new Error(`Diferenciación no soportada para función: ${ast.name}`);
            }
        }

        default:
            throw new Error(`Nodo desconocido en diferenciación: ${ast.type}`);
    }
}

function obtenerDerivadaOrdenK(ast, k) {
    if (k < 0) throw new Error("El orden de la derivada no puede ser negativo.");
    let actual = ast;
    for (let i = 0; i < k; i++) {
        actual = diferenciarAST(actual);
    }
    return actual;
}

function estimarMaximoDerivada(astDerivada, a, b, numMuestras = 300) {
    if (a > b) {
        const temp = a;
        a = b;
        b = temp;
    }

    let maxM = 0;
    let puntoMax = a;
    const muestras = [];
    const paso = (b - a) / numMuestras;

    for (let i = 0; i <= numMuestras; i++) {
        const t = a + i * paso;
        try {
            const val = Math.abs(evaluarAST(astDerivada, t));
            if (!isNaN(val) && isFinite(val)) {
                muestras.push({ t, val });
                if (val > maxM) {
                    maxM = val;
                    puntoMax = t;
                }
            }
        } catch (_) {}
    }

    [a, b].forEach(t => {
        try {
            const val = Math.abs(evaluarAST(astDerivada, t));
            if (!isNaN(val) && isFinite(val) && val > maxM) {
                maxM = val;
                puntoMax = t;
            }
        } catch (_) {}
    });

    return { maxM, puntoMax, muestras };
}

function contarDigitosSignificativos(error) {
    if (error === null || error === undefined || isNaN(error)) return null;
    if (error === 0 || error < 1e-15) return 15;
    const str = Math.abs(error).toFixed(12);
    const partes = str.split(".");
    if (partes.length < 2) return 0;
    const decimales = partes[1];
    let ceros = 0;
    for (const ch of decimales) {
        if (ch === '0') ceros++;
        else break;
    }
    return ceros;
}

function calcularLimiteSuperiorError({ X, valorEvaluar, valorInterpolado, exprFx, cotaMManual }) {
    const xNums = X.map(x => x.toNumber());
    const xEvalNum = valorEvaluar.toNumber();
    const pEvalNum = valorInterpolado.toNumber();
    const n = X.length - 1; // grado
    const ordenDerivada = n + 1;

    // 1. Factores |x - x_i|
    const factoresNums = xNums.map(xi => Math.abs(xEvalNum - xi));
    const productoFactores = factoresNums.reduce((acc, f) => acc * f, 1);

    // 2. Factorial (n+1)!
    let fact = 1;
    for (let i = 2; i <= ordenDerivada; i++) fact *= i;

    const terminoGeometrico = productoFactores / fact;

    // 3. Intervalo [a, b]
    const a = Math.min(...xNums, xEvalNum);
    const b = Math.max(...xNums, xEvalNum);

    // 4. Determinar M y f(x)
    let M = null;
    let puntoMaxM = null;
    let astFx = null;
    let astDerivada = null;
    let fEvalReal = null;
    let errorRealAbsoluto = null;
    let errorRealRelativo = null;
    let mensajeErrorFx = null;

    if (exprFx && exprFx.trim() !== "") {
        try {
            astFx = parsearExpresionMatematica(exprFx);
            fEvalReal = evaluarAST(astFx, xEvalNum);
            errorRealAbsoluto = Math.abs(fEvalReal - pEvalNum);
            errorRealRelativo = Math.abs(fEvalReal) > 1e-14 
                ? (errorRealAbsoluto / Math.abs(fEvalReal)) * 100 
                : null;

            astDerivada = obtenerDerivadaOrdenK(astFx, ordenDerivada);
            const resM = estimarMaximoDerivada(astDerivada, a, b);
            M = resM.maxM;
            puntoMaxM = resM.puntoMax;
        } catch (err) {
            mensajeErrorFx = err.message;
        }
    }

    // Sobreescritura si se ingresó cota manual
    if (cotaMManual !== null && cotaMManual !== undefined && !isNaN(cotaMManual) && cotaMManual > 0) {
        M = cotaMManual;
    }

    let cotaTeorica = null;
    if (M !== null && !isNaN(M)) {
        cotaTeorica = terminoGeometrico * M;
    }

    const digitosSignificativos = errorRealAbsoluto !== null 
        ? contarDigitosSignificativos(errorRealAbsoluto) 
        : (cotaTeorica !== null ? contarDigitosSignificativos(cotaTeorica) : null);

    return {
        n,
        ordenDerivada,
        xNums,
        xEvalNum,
        pEvalNum,
        factoresNums,
        productoFactores,
        fact,
        terminoGeometrico,
        intervalo: [a, b],
        M,
        puntoMaxM,
        cotaTeorica,
        fEvalReal,
        errorRealAbsoluto,
        errorRealRelativo,
        digitosSignificativos,
        mensajeErrorFx,
        exprFx
    };
}

function renderizarPanelLimiteError(datos, X, valorEvaluar, valorInterpolado) {
    if (!el.panelLimiteError) return;

    const n = datos.n;
    const orden = datos.ordenDerivada;
    const xEvalStr = valorEvaluar.toString();
    const aStr = datos.intervalo[0].toLocaleString("es-PE", { maximumFractionDigits: 4 });
    const bStr = datos.intervalo[1].toLocaleString("es-PE", { maximumFractionDigits: 4 });

    // 1. Renderizar fórmula del Teorema en KaTeX
    const formulaTeorema = `|E_{${n}}(x)| \\le \\frac{\\prod_{i=0}^{${n}} |x - x_i|}{${orden}!} \\cdot \\max_{${aStr} \\le t \\le ${bStr}} \\left| f^{(${orden})}(t) \\right|`;
    
    renderizarFormulaMath(
        el.formulaErrorTeoremaKatex,
        document.createElement("div"),
        formulaTeorema,
        formulaTeorema
    );

    // 2. Renderizar fórmula sustituida
    let formulaSustituida = "";
    if (datos.cotaTeorica !== null) {
        const prodStr = datos.productoFactores < 1e-4 ? datos.productoFactores.toExponential(4) : datos.productoFactores.toFixed(6);
        const mStr = datos.M < 1e-4 ? datos.M.toExponential(4) : datos.M.toFixed(4);
        const cotaStr = datos.cotaTeorica < 1e-4 ? datos.cotaTeorica.toExponential(4) : datos.cotaTeorica.toFixed(6);
        formulaSustituida = `|E_{${n}}(${xEvalStr})| \\le \\frac{${prodStr}}{${datos.fact}} \\cdot (${mStr}) = ${cotaStr}`;
    } else {
        const prodStr = datos.productoFactores < 1e-4 ? datos.productoFactores.toExponential(4) : datos.productoFactores.toFixed(6);
        formulaSustituida = `|E_{${n}}(${xEvalStr})| \\le \\frac{${prodStr}}{${datos.fact}} \\cdot M_{${orden}} \\quad \\text{(Cota } M_{${orden}} \\text{ pendiente)}`;
    }

    renderizarFormulaMath(
        el.formulaErrorSustituidaKatex,
        document.createElement("div"),
        formulaSustituida,
        formulaSustituida
    );

    // 3. Tarjetas métricas
    const geomStr = datos.terminoGeometrico < 1e-4 
        ? datos.terminoGeometrico.toExponential(4) 
        : datos.terminoGeometrico.toFixed(6);
    el.valTerminoNodos.textContent = geomStr;
    el.subTerminoNodos.textContent = `W(${xEvalStr}) / ${datos.fact}!`;

    if (datos.M !== null) {
        el.valCotaDerivada.textContent = datos.M < 1e-4 ? datos.M.toExponential(4) : datos.M.toFixed(4);
        el.subCotaDerivada.textContent = datos.puntoMaxM !== null 
            ? `En t ≈ ${datos.puntoMaxM.toFixed(3)} sobre [${aStr}, ${bStr}]` 
            : `Cota sobre [${aStr}, ${bStr}]`;
    } else {
        el.valCotaDerivada.textContent = "—";
        el.subCotaDerivada.textContent = "Ingrese M o f(x)";
    }

    if (datos.cotaTeorica !== null) {
        const cotaStr = datos.cotaTeorica < 1e-4 
            ? datos.cotaTeorica.toExponential(4) 
            : datos.cotaTeorica.toFixed(6);
        el.valCotaTeorica.textContent = `≤ ${cotaStr}`;
        el.subCotaTeorica.textContent = `|E_${n}(${xEvalStr})| ≤ ${cotaStr}`;
    } else {
        el.valCotaTeorica.textContent = "—";
        el.subCotaTeorica.textContent = "Requiere cota M";
    }

    if (datos.errorRealAbsoluto !== null) {
        const errStr = datos.errorRealAbsoluto < 1e-4 
            ? datos.errorRealAbsoluto.toExponential(4) 
            : datos.errorRealAbsoluto.toFixed(6);
        el.valErrorReal.textContent = errStr;
        el.subErrorReal.textContent = datos.errorRealRelativo !== null 
            ? `Error rel: ${datos.errorRealRelativo.toFixed(4)}%` 
            : `f(${xEvalStr}) = ${datos.fEvalReal.toFixed(6)}`;
    } else {
        el.valErrorReal.textContent = "—";
        el.subErrorReal.textContent = "Requiere f(x) analítica";
    }

    // Badge de estado
    if (datos.cotaTeorica !== null && datos.errorRealAbsoluto !== null) {
        const cumple = datos.errorRealAbsoluto <= (datos.cotaTeorica * 1.000001);
        el.badgeEstadoError.textContent = cumple ? "Teorema verificado" : "Revisar datos";
        el.badgeEstadoError.className = cumple ? "badge-success" : "detail-badge warning";
    } else if (datos.cotaTeorica !== null) {
        el.badgeEstadoError.textContent = "Cota calculada";
        el.badgeEstadoError.className = "badge-info";
    } else {
        el.badgeEstadoError.textContent = "Modo tabular";
        el.badgeEstadoError.className = "detail-tag";
    }

    // 4. Lista de desglose paso a paso
    el.listaFactoresError.innerHTML = "";
    
    const li1 = document.createElement("li");
    li1.innerHTML = `<span class="step-num">1.</span> <strong>Grado:</strong> Polinomio de grado n = ${n} (${X.length} nodos). Derivada de orden n+1 = ${orden}.`;
    el.listaFactoresError.appendChild(li1);

    const li2 = document.createElement("li");
    const factoresDetalle = datos.factoresNums.map((f, idx) => `|${xEvalStr} - ${X[idx].toString()}| = ${f.toLocaleString("es-PE", { maximumFractionDigits: 4 })}`).join(", ");
    li2.innerHTML = `<span class="step-num">2.</span> <strong>Factores de nodos:</strong> ${factoresDetalle}.`;
    el.listaFactoresError.appendChild(li2);

    const li3 = document.createElement("li");
    const prodStr = datos.productoFactores < 1e-4 ? datos.productoFactores.toExponential(4) : datos.productoFactores.toFixed(6);
    li3.innerHTML = `<span class="step-num">3.</span> <strong>Producto W(x):</strong> ∏ |x - xᵢ| = ${prodStr}.`;
    el.listaFactoresError.appendChild(li3);

    const li4 = document.createElement("li");
    li4.innerHTML = `<span class="step-num">4.</span> <strong>Factorial:</strong> (${n} + 1)! = ${orden}! = ${datos.fact}. Cociente geométrico: ${geomStr}.`;
    el.listaFactoresError.appendChild(li4);

    const li5 = document.createElement("li");
    li5.innerHTML = `<span class="step-num">5.</span> <strong>Intervalo de análisis:</strong> [a, b] = [${aStr}, ${bStr}].`;
    el.listaFactoresError.appendChild(li5);

    if (datos.M !== null) {
        const li6 = document.createElement("li");
        const mStr = datos.M < 1e-4 ? datos.M.toExponential(4) : datos.M.toFixed(4);
        li6.innerHTML = `<span class="step-num">6.</span> <strong>Cota de la derivada:</strong> M_${orden} = max |f^(${orden})(t)| = ${mStr}.`;
        el.listaFactoresError.appendChild(li6);
    }

    if (datos.fEvalReal !== null) {
        const li7 = document.createElement("li");
        li7.innerHTML = `<span class="step-num">7.</span> <strong>Evaluación analítica:</strong> f(${xEvalStr}) = ${datos.fEvalReal.toLocaleString("es-PE", { maximumFractionDigits: 6 })}, P(${xEvalStr}) = ${valorInterpolado.toString()} (≈ ${datos.pEvalNum.toLocaleString("es-PE", { maximumFractionDigits: 6 })}). Error real E_a = ${datos.errorRealAbsoluto.toFixed(6)}.`;
        el.listaFactoresError.appendChild(li7);
    }

    // 5. Nota pedagógica de Dígitos Significativos
    let nota = "";
    if (datos.fEvalReal !== null && datos.digitosSignificativos !== null) {
        const ceros = datos.digitosSignificativos;
        nota = `El resultado del error de truncamiento cometido es E_a ≈ ${datos.errorRealAbsoluto.toFixed(6)}. ` +
            `El número de ceros inmediatamente después del punto decimal (${ceros}) garantiza al menos ` +
            `<strong>${ceros} dígitos significativos correctos</strong> en la aproximación calculada (según la teoría de interpolación).`;
    } else if (datos.cotaTeorica !== null && datos.digitosSignificativos !== null) {
        const ceros = datos.digitosSignificativos;
        nota = `La cota teórica calculada es |E_{${n}}(${xEvalStr})| ≤ ${datos.cotaTeorica.toFixed(6)}. ` +
            `El número de ceros inmediatamente después del punto decimal (${ceros}) garantiza una precisión de ` +
            `<strong>${ceros} dígitos significativos correctos</strong>.`;
    } else {
        nota = `<em>Observación:</em> En problemas puramente tabulares sin función conocida, en los nodos tabulados el error es cero (P(xᵢ) = yᵢ). ` +
            `Para estimar la cota superior del error en puntos intermedios, ingrese una función f(x) o la cota M_${orden} de la derivada en la sección opcional.`;
    }

    if (datos.mensajeErrorFx) {
        nota += `<br><span style="color: var(--status-error);">Aviso en función f(x): ${datos.mensajeErrorFx}</span>`;
    }

    el.textoDigitosSignificativos.innerHTML = nota;
}

/* ==========================================================================
   9. CONTROLADOR PRINCIPAL: RESOLUCIÓN Y ACTUALIZACIÓN
   ========================================================================== */

function mostrarMensajeError(msg) {
    el.mensajeAlerta.textContent = msg;
    el.mensajeAlerta.className = "alert-message error";
    el.mensajeAlerta.classList.remove("hidden");
}

function ocultarMensajeAlerta() {
    el.mensajeAlerta.classList.add("hidden");
}

function actualizarIndicadorPaso(X) {
    const { esEquiespaciado, h } = verificarEquiespaciado(X);
    if (!X || X.length < 2) {
        el.badgePasoH.textContent = "Paso h = —";
        el.badgePasoH.className = "badge-step";
        el.textoPasoH.textContent = "Ingrese al menos 2 puntos";
        return;
    }

    if (esEquiespaciado) {
        el.badgePasoH.textContent = `Paso constante h = ${h.toString()}`;
        el.badgePasoH.className = "badge-step equispaced";
        el.textoPasoH.textContent = "Nodos equiespaciados (Newton-Gregory aplicable)";
    } else {
        el.badgePasoH.textContent = "Paso variable";
        el.badgePasoH.className = "badge-step non-equispaced";
        el.textoPasoH.textContent = "Nodos no equiespaciados (use Newton Divididas)";
    }
}

function resolverInterpolacion() {
    ocultarMensajeAlerta();

    try {
        let X = parsearVector(el.vectorX.value);
        let Y = parsearVector(el.vectorY.value);
        const valorEvaluar = parsearFraccion(el.valorEvaluar.value);

        // 1. Validaciones generales
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
            el.vectorX.value = X.map(x => x.toString()).join(", ");
            el.vectorY.value = Y.map(y => y.toString()).join(", ");
        }

        // 3. Verificar si son equiespaciados
        const { esEquiespaciado, h } = verificarEquiespaciado(X);
        actualizarIndicadorPaso(X);

        // 4. Determinar método activo
        let metodoEfectivo = appState.metodo;

        if (metodoEfectivo === "auto") {
            if (esEquiespaciado) {
                // Si x está más cerca de x0 -> adelante, si más cerca de xn -> atrás
                const dInicio = valorEvaluar.sub(X[0]).abs();
                const dFin = valorEvaluar.sub(X[X.length - 1]).abs();
                metodoEfectivo = dInicio.sub(dFin).isNegative() ? "ng-adelante" : "ng-atras";
            } else {
                metodoEfectivo = "divididas";
            }
        }

        // Validar si usuario forzó Newton-Gregory con nodos no equiespaciados
        if ((metodoEfectivo === "ng-adelante" || metodoEfectivo === "ng-atras") && !esEquiespaciado) {
            mostrarMensajeError(
                "El método de Newton-Gregory requiere nodos equiespaciados (paso constante h). " +
                "Los nodos actuales tienen pasos variables. Se ha utilizado Newton con Diferencias Divididas para garantizar la exactitud matemática."
            );
            metodoEfectivo = "divididas";
        }

        appState.metodoActivo = metodoEfectivo;

        // 5. Cálculos según el método
        let tablaCalculo;
        let evaluadorFn;
        let valorInterpolado;
        let coeficientesNewtonStandard = [];
        let formaOriginal;
        let paramS = null;

        const n = X.length;
        const x0 = X[0];
        const xn = X[n - 1];

        if (metodoEfectivo === "divididas") {
            tablaCalculo = calcularDiferenciasDivididas(X, Y);
            coeficientesNewtonStandard = tablaCalculo[0].slice(0, n);
            evaluadorFn = (x) => evaluarNewtonDivididas(X, coeficientesNewtonStandard, x);
            valorInterpolado = evaluadorFn(valorEvaluar);
            formaOriginal = generarFormaNewton(X, coeficientesNewtonStandard);

            el.tituloPolinomioNewton.textContent = "Forma de Newton con Diferencias Divididas";
            el.tituloTablaDiferencias.textContent = "5. Tabla de Diferencias Divididas";
            el.subtituloTablaDiferencias.textContent = "La primera fila define los coeficientes c_i = f[x_0, ..., x_i]";
            el.badgeParametroS.classList.add("hidden");

        } else if (metodoEfectivo === "ng-adelante") {
            tablaCalculo = calcularDiferenciasFinitas(X, Y);
            evaluadorFn = (x) => evaluarNewtonGregoryAdelante(Y, tablaCalculo, h, x0, x).valor;
            const evalObj = evaluarNewtonGregoryAdelante(Y, tablaCalculo, h, x0, valorEvaluar);
            valorInterpolado = evalObj.valor;
            paramS = evalObj.s;

            // Coeficientes divididos por h^k y k! para la forma estándar
            let hPotencia = new Fraccion(1n);
            for (let k = 0; k < n; k++) {
                const c_k = tablaCalculo[0][k].div(factorial(k).mul(hPotencia));
                coeficientesNewtonStandard.push(c_k);
                hPotencia = hPotencia.mul(h);
            }

            formaOriginal = generarFormaNewtonGregoryAdelante(X, Y, tablaCalculo, h);

            el.tituloPolinomioNewton.textContent = "Forma de Newton-Gregory Hacia Adelante (Δ)";
            el.tituloTablaDiferencias.textContent = "5. Tabla de Diferencias Finitas Progresivas (Δ)";
            el.subtituloTablaDiferencias.textContent = "La primera fila (resaltada) define las diferencias Δ^k y_0";

            el.badgeParametroS.textContent = `s = (x - x₀)/h = ${paramS.toString()}` + (paramS.den !== 1n ? ` (≈ ${paramS.toDecimalString(4)})` : "");
            el.badgeParametroS.classList.remove("hidden");

        } else if (metodoEfectivo === "ng-atras") {
            tablaCalculo = calcularDiferenciasFinitas(X, Y);
            evaluadorFn = (x) => evaluarNewtonGregoryAtras(Y, tablaCalculo, h, xn, x).valor;
            const evalObj = evaluarNewtonGregoryAtras(Y, tablaCalculo, h, xn, valorEvaluar);
            valorInterpolado = evalObj.valor;
            paramS = evalObj.s;

            // Para la forma estándar, los coeficientes en potencias de (x - x_i) coinciden con Newton
            const tablaDiv = calcularDiferenciasDivididas(X, Y);
            coeficientesNewtonStandard = tablaDiv[0].slice(0, n);

            formaOriginal = generarFormaNewtonGregoryAtras(X, Y, tablaCalculo, h);

            el.tituloPolinomioNewton.textContent = "Forma de Newton-Gregory Hacia Atrás (∇)";
            el.tituloTablaDiferencias.textContent = "5. Tabla de Diferencias Finitas Regresivas (∇)";
            el.subtituloTablaDiferencias.textContent = "La diagonal inferior (resaltada en morado) define las diferencias ∇^k y_n";

            el.badgeParametroS.textContent = `s = (x - xₙ)/h = ${paramS.toString()}` + (paramS.den !== 1n ? ` (≈ ${paramS.toDecimalString(4)})` : "");
            el.badgeParametroS.classList.remove("hidden");
        }

        // 6. Polinomio estándar expandido
        const polinomioEstandar = obtenerPolinomioEstandar(X, coeficientesNewtonStandard);

        // 7. Actualizar métricas destacadas
        const grado = n - 1;
        el.badgeGrado.textContent = `Grado n = ${grado}`;

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

        let nombreMetodo = "Newton con Diferencias Divididas";
        if (metodoEfectivo === "ng-adelante") nombreMetodo = "Newton-Gregory Hacia Adelante (Δ)";
        if (metodoEfectivo === "ng-atras") nombreMetodo = "Newton-Gregory Hacia Atrás (∇)";

        el.explicacionResultado.textContent = esInterpolacion
            ? `Calculado mediante ${nombreMetodo}. Para x = ${valorEvaluar.toString()}, el polinomio interpolante exacto de grado ${grado} obtiene P(${valorEvaluar.toString()}) = ${valorInterpolado.toString()}${evalDecStr} (dentro del rango de nodos [${X[0].toString()}, ${X[X.length - 1].toString()}]).`
            : `Calculado mediante ${nombreMetodo}. Para x = ${valorEvaluar.toString()}, el polinomio obtiene P(${valorEvaluar.toString()}) = ${valorInterpolado.toString()}${evalDecStr} (extrapolación fuera del rango [${X[0].toString()}, ${X[X.length - 1].toString()}]).`;

        // 8. Fórmulas Matemáticas con KaTeX y fallback
        renderizarFormulaMath(
            el.polinomioNewtonKatex,
            el.polinomioNewtonFallback,
            formaOriginal.latex,
            formaOriginal.plano
        );

        const formaEstandar = generarFormaEstandar(polinomioEstandar);
        renderizarFormulaMath(
            el.polinomioEstandarKatex,
            el.polinomioEstandarFallback,
            formaEstandar.latex,
            formaEstandar.plano
        );

        // 9. Estimación del Límite Superior de Error (Teorema del Residuo)
        const exprFx = el.funcionFx ? el.funcionFx.value.trim() : "";
        const cotaMTexto = el.cotaDerivadaM ? el.cotaDerivadaM.value.trim() : "";
        let cotaMManual = null;
        if (cotaMTexto !== "") {
            try {
                const cotaMFrac = parsearFraccion(cotaMTexto);
                cotaMManual = cotaMFrac.toNumber();
            } catch (_) {
                cotaMManual = parseFloat(cotaMTexto);
            }
        }

        const datosError = calcularLimiteSuperiorError({
            X,
            valorEvaluar,
            valorInterpolado,
            exprFx,
            cotaMManual
        });

        renderizarPanelLimiteError(datosError, X, valorEvaluar, valorInterpolado);

        // 10. Tablas de detalle
        renderizarTablaDiferencias(X, tablaCalculo, metodoEfectivo);
        renderizarTablaValidacion(X, Y, evaluadorFn);

        // 11. Gráfica Interactiva
        prepararDatosGrafica(X, Y, evaluadorFn, valorEvaluar);
        redibujarGrafica();

    } catch (error) {
        mostrarMensajeError(error.message);
        console.error("Error al resolver:", error);
    }
}

// Configuración de botones del selector de método
if (el.selectorMetodo) {
    const botonesMetodo = el.selectorMetodo.querySelectorAll(".method-btn");
    botonesMetodo.forEach(btn => {
        btn.addEventListener("click", () => {
            botonesMetodo.forEach(b => b.classList.remove("active"));
            btn.classList.add("active");
            appState.metodo = btn.getAttribute("data-method");
            resolverInterpolacion();
        });
    });
}

// Desplegable de función analítica opcional
if (el.btnToggleOpcional && el.contenidoOpcional) {
    el.btnToggleOpcional.addEventListener("click", () => {
        const estaOculto = el.contenidoOpcional.classList.contains("hidden");
        if (estaOculto) {
            el.contenidoOpcional.classList.remove("hidden");
            el.btnToggleOpcional.setAttribute("aria-expanded", "true");
        } else {
            el.contenidoOpcional.classList.add("hidden");
            el.btnToggleOpcional.setAttribute("aria-expanded", "false");
        }
    });
}

// Botón: Generar Y = f(X) a partir de la función analítica
if (el.btnGenerarY) {
    el.btnGenerarY.addEventListener("click", () => {
        const expr = el.funcionFx.value.trim();
        if (!expr) {
            mostrarMensajeError("Ingrese una expresión analítica f(x) (ej: (3+x)/(1+x)) para evaluar el vector Y.");
            return;
        }
        try {
            const X = parsearVector(el.vectorX.value);
            if (X.length === 0) {
                mostrarMensajeError("El vector de nodos X debe tener al menos 2 valores.");
                return;
            }
            const ast = parsearExpresionMatematica(expr);
            const Y_calculados = X.map(xi => {
                const yVal = evaluarAST(ast, xi.toNumber());
                if (Math.abs(Math.round(yVal) - yVal) < 1e-10) {
                    return Math.round(yVal).toString();
                }
                return parseFloat(yVal.toFixed(6)).toString();
            });
            el.vectorY.value = Y_calculados.join(", ");
            resolverInterpolacion();
        } catch (err) {
            mostrarMensajeError(`Error al calcular Y = f(X): ${err.message}`);
        }
    });
}

// Escuchar cambios en X para actualizar en vivo el indicador de paso h
el.vectorX.addEventListener("input", () => {
    try {
        const X = parsearVector(el.vectorX.value);
        actualizarIndicadorPaso(X);
    } catch (_) {}
});

// Botones de ejemplos y limpieza
el.btnResolver.addEventListener("click", () => resolverInterpolacion());

// Botón Ejemplo Cota Error (Slide 3 de la clase)
if (el.btnEjemploError) {
    el.btnEjemploError.addEventListener("click", () => {
        // Ejercicio exacto de la Diapositiva 3:
        // f(x) = (3+x)/(1+x), x = [0.1, 0.2, 0.4], y = [2.82, 2.67, 2.43], x = 0.25
        el.vectorX.value = "0.1, 0.2, 0.4";
        el.vectorY.value = "2.82, 2.67, 2.43";
        el.valorEvaluar.value = "0.25";
        if (el.funcionFx) el.funcionFx.value = "(3 + x) / (1 + x)";
        if (el.cotaDerivadaM) el.cotaDerivadaM.value = ""; // Auto-estimar derivada f'''(t)

        // Abrir panel opcional para visualizar f(x)
        if (el.contenidoOpcional) {
            el.contenidoOpcional.classList.remove("hidden");
            if (el.btnToggleOpcional) el.btnToggleOpcional.setAttribute("aria-expanded", "true");
        }

        if (el.selectorMetodo) {
            const btnDiv = el.selectorMetodo.querySelector('[data-method="divididas"]');
            if (btnDiv) {
                el.selectorMetodo.querySelectorAll(".method-btn").forEach(b => b.classList.remove("active"));
                btnDiv.classList.add("active");
                appState.metodo = "divididas";
            }
        }

        resolverInterpolacion();
    });
}

el.btnEjemplo.addEventListener("click", () => {
    el.vectorX.value = "1, 2, 4, 7";
    el.vectorY.value = "45, 65, 110, 220";
    el.valorEvaluar.value = "5";
    if (el.funcionFx) el.funcionFx.value = "";
    if (el.cotaDerivadaM) el.cotaDerivadaM.value = "";
    resolverInterpolacion();
});

if (el.btnEjemploEqui) {
    el.btnEjemploEqui.addEventListener("click", () => {
        el.vectorX.value = "1, 2, 3, 4, 5";
        el.vectorY.value = "0, 5, 22, 57, 116";
        el.valorEvaluar.value = "2.5";
        if (el.funcionFx) el.funcionFx.value = "x^3 - 2x + 1";
        if (el.cotaDerivadaM) el.cotaDerivadaM.value = "";
        if (el.selectorMetodo) {
            const btnAdelante = el.selectorMetodo.querySelector('[data-method="ng-adelante"]');
            if (btnAdelante) {
                el.selectorMetodo.querySelectorAll(".method-btn").forEach(b => b.classList.remove("active"));
                btnAdelante.classList.add("active");
                appState.metodo = "ng-adelante";
            }
        }
        resolverInterpolacion();
    });
}

if (el.btnLimpiar) {
    el.btnLimpiar.addEventListener("click", () => {
        el.vectorX.value = "";
        el.vectorY.value = "";
        el.valorEvaluar.value = "";
        if (el.funcionFx) el.funcionFx.value = "";
        if (el.cotaDerivadaM) el.cotaDerivadaM.value = "";
        ocultarMensajeAlerta();
        actualizarIndicadorPaso([]);
        el.vectorX.focus();
    });
}

if (el.checkOrdenarX) {
    el.checkOrdenarX.addEventListener("change", () => resolverInterpolacion());
}

[el.vectorX, el.vectorY, el.valorEvaluar, el.funcionFx, el.cotaDerivadaM].forEach(input => {
    if (input) {
        input.addEventListener("keydown", (e) => {
            if (e.key === "Enter") resolverInterpolacion();
        });
    }
});

// Inicialización
document.addEventListener("DOMContentLoaded", () => {
    resolverInterpolacion();
});

if (typeof window !== "undefined") {
    window.appState = appState;
    window.resolverInterpolacion = resolverInterpolacion;
}

if (document.readyState === "complete" || document.readyState === "interactive") {
    setTimeout(resolverInterpolacion, 50);
}

