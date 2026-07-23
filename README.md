# Codigo de la tesina

Este repositorio contiene la formalización en F* desarrollada para la tesina. El objetivo del código es modelar un lenguaje imperativo pequeño, definir una lógica de incorrectitud para razonar sobre ejecuciones que llegan a estados de error, extenderla con ideas de lógica de separación para programas con heap, y demostrar propiedades de corrección metateorica y ejemplos de uso.

## Idea general

El proyecto trabaja con programas representados como datos en F*. Sobre esos programas se definen:

1. Una sintaxis de expresiones y sentencias.
2. Una semántica operacional, expresada como una relación `runsto p s0 s1`.
3. Una lógica de incorrectitud, expresada como triples que describen estados alcanzables.
4. Una demostración de solidez: si se prueba un triple y el postestado satisface la postcondición, entonces existe una ejecución real del programa desde algún preestado que satisface la precondición.
5. En la versión con heap, predicados de separación, regla de marco, huellas (`footprint`) y una descomposición de ejecuciones en huellas enmarcadas.

En terminos prácticos: los archivos principales definen el lenguaje y la lógica; los archivos dentro de `proofs/` muestran programas concretos y sus pruebas.

## Estructura

```text
.
|-- IncLogicOne.fst          # Logica de incorrectitud sin heap
|-- IncSepLogicOne.fst       # Logica de incorrectitud con heap y separacion
|-- proofs/
|   |-- AllocFree.fst        # Ejemplo use-after-free: alloc, free, store
|   |-- RandomLoop.fst       # Ejemplo con loop no determinista y assert fallido
|   |-- ListSumLen.fst       # Ejemplo sobre una lista enlazada en memoria
|   |-- PushBack.fst         # Ejemplo con mutacion de estructura apuntada
|   `-- ISLPrograms.fst      # Version previa/alternativa; ver nota de estado
|-- Makefile                 # Verificacion con F*
|-- fstar.sh                 # Wrapper para llamar a F* con los flags del repo
|-- .fst.config.json         # Configuracion para herramientas/editor de F*
`-- .github/workflows/ci.yml # CI que instala F* nightly y ejecuta make
```

## Modulos principales

### `IncLogicOne.fst`

Es la versión base, sin memoria dinámica.

Define:

- `expr`: expresiones aritméticas y booleanas codificadas como naturales.
- `stmt`: sentencias del lenguaje: asignación, no determinismo, `Skip`, `Error`, `Assume`, secuencia, elección y clausura de Kleene.
- `state`: estado compuesto por store y modo de terminación (`Ok` o `Er`).
- `runsto`: semántica operacional de los programas.
- `il_triple`: reglas de la lógica de incorrectitud.
- `soundness`: prueba principal de solidez de la lógica.

Este archivo es el mejor punto de entrada si se quiere entender la construcción antes de mirar heap y separación.

### `IncSepLogicOne.fst`

Es el núcleo actual del trabajo con heap.

Extiende la versión base con:

- Valores `Nat` y `Loc`.
- Heap modelado como `loc -> cell`, donde una celda puede ser `Full`, `Empty` o `Unknown`.
- Operaciones de memoria: `Alloc`, `Free`, `Load` y `Store`.
- Predicados de separacion: `emp`, `points_to`, `points_to_empty` y el operador `(**)`.
- Regla de marco `ISL_Frame`.
- Reglas de error para accesos inválidos: free/load/store sobre celda vacía o dirección nula.
- `soundness`, que conecta los triples `isl_triple` con la semántica `runsto`.
- `footprint`, `framed_footprint` y pruebas que relacionan huellas locales con ejecuciones globales.
- `runsto_decompose`, que descompone una ejecución operacional en una huella enmarcada.

Si el objetivo es leer el aporte principal de la tesina, este es el archivo central.

## Ejemplos y pruebas

### `proofs/AllocFree.fst`

Prueba un caso clasico de use-after-free:

```c
x = alloc();
free(x);
*x = 1;
```

El programa `prog_uaf` termina en error porque intenta escribir en una ubicación que fue liberada. La prueba principal es `proof_uaf`.

### `proofs/RandomLoop.fst`

Modela un programa con un loop y una rama no determinista:

```c
n := 1000000;
i, j := 0;
while (i < n) {
  i++;
  if (random()) j++;
}
assert(j != n);
```

La lógica de incorrectitud permite demostrar que existe una ejecución que llega al error del `assert`, concretamente la ejecución donde `j` se incrementa en todas las iteraciones. La prueba principal es `proof_prog1`.

### `proofs/ListSumLen.fst`

Trabaja sobre una lista enlazada representada en heap. El programa recorre la lista, suma valores y cuenta nodos; luego fuerza un assert donde `sum == len`. Para una lista de unos, eso permite probar una ejecución que llega al error.

Elementos importantes:

- `list_seg`: predicado inductivo para segmentos de lista.
- `prefix_seg`: segmento ya recorrido.
- `variant`: invariante parametrizado por cantidad de iteraciones.
- `proof_prog_list_sum_len`: prueba completa del programa.

### `proofs/PushBack.fst`

Define un cliente que lee punteros, ejecuta una operación `push_back` simplificada y luego intenta escribir a traves de un puntero que puede quedar apuntando a una celda vacía. La prueba principal es `proof_client`.

## Orden recomendado de lectura

1. Leer `IncLogicOne.fst` hasta la definición de `soundness` para entender el lenguaje, la semántica y la forma de los triples.
2. Leer en `IncSepLogicOne.fst` las secciones de sintaxis, heap y semántica operacional.
3. Leer en `IncSepLogicOne.fst` la sección `Incorrectness Separation Logic`, donde aparecen `emp`, `points_to`, `(**)` e `isl_triple`.
4. Leer la prueba `soundness` de `IncSepLogicOne.fst` para ver como cada regla lógica se justifica operacionalmente.
5. Leer `proofs/AllocFree.fst` como primer ejemplo concreto.
6. Leer `proofs/RandomLoop.fst` para ver el uso de invariantes/variantes con `Kleene`.
7. Leer `proofs/ListSumLen.fst` y `proofs/PushBack.fst` como ejemplos mas ricos con heap.
8. Volver a las secciones de `footprint` y `runsto_decompose` de `IncSepLogicOne.fst` para entender la parte metateorica de huellas.

## Como verificar

El proyecto usa F* y un `Makefile`.

Requisitos:

- F* instalado y disponible como `fstar.exe`.
- `make`.

Para verificar todo lo incluido por el `Makefile`:

```bash
make -skj$(nproc)
```

Para ver el comando de F* que construye el `Makefile`:

```bash
make echo-fstar V=1
```

Para limpiar artefactos generados:

```bash
make clean
```

El archivo `fstar.sh` sirve como wrapper para herramientas de editor: llama a `make echo-fstar` y ejecuta F* con los mismos flags que usa el repositorio. `.fst.config.json` apunta a ese wrapper.

## Notas sobre el estado actual

- La CI instala F* nightly y ejecuta `make -skj$(nproc)`.
- Al regenerar dependencias, F* advierte que `proofs/ISLPrograms.fst` referencia `IncSepLogic`, modulo que no esta presente como fuente en el árbol actual.
- El directorio `obj/` y el archivo `.dep` son artefactos de verificación/cache generados por F* y `make`.

## Convenciones del código

- Las condiciones (`cond`) son predicados sobre estados.
- Los triples de incorrectitud se leen al revés de una lógica de corrección total: describen postestados alcanzables, y la solidez reconstruye algun preestado y una ejecución que llega a ese postestado.
- `Assume e` continua solo cuando la condición codificada por `e` es verdadera, las comparaciones devuelven `1` cuando se consideran satisfechas.
- `Unknown` representa heap no poseido por la condición local; esto permite expresar separación y enmarcar heap ajeno.
- `points_to l v` describe una porción singleton del heap donde `l` contiene `v`.
- `emp` describe ausencia de heap propio.

## Glosario minimo

- `runsto p s0 s1`: el programa `p` puede ejecutar desde `s0` hasta `s1`.
- `Ok`: ejecución normal.
- `Er`: ejecución que alcanzo un error.
- `isl_triple pre p post`: triple de lógica de incorrectitud con separación.
- `soundness`: teorema que prueba que un triple lógico describe ejecuciones reales de la semántica.
- `footprint`: huella mínima/local de heap necesaria para una ejecución.
- `framed_footprint`: huella local extendida con un marco de heap disjunto.
