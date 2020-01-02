# Algorithms in Representation Theory

This thesis deals with implementation of algorithm for computation of generator of almost split sequences ending at an 
indecomposable nonprojective module of path algebra over finite quiver. Algorithm is implemented in algebra system GAP
(Groups, Algorithms, Programming) with additional package QPA (Quivers and Path Algebras).

Department of Algebra, Faculty of Mathematics and Physics, Charles University
<br />
**Author**: Marek Trunkát, **Supervisor**: RNDr. Jan Šťovíček, Ph.D., Department of Algebra

## How to run

### Prerequisites

1. Install **GAP** following this tutorial [http://www.gap-system.org/Download/index.html](http://www.gap-system.org/Download/index.html)
2. Install **QPA** package pas described at [http://www.math.ntnu.no/~oyvinso/QPA/](http://www.math.ntnu.no/~oyvinso/QPA/)

### Execution

1. Run **GAP**
2. Load  **QPA** package via `LoadPackage("QPA");`
3. Copy whole `src/alghorirm.g` to command line to register `AlmostSplitSequence2` function along with other helper functions.
4. Now you can use this function to compute a generator of `DTr(X) → E → X`:

```
K := Rationals;
Q := Quiver(3, [[1, 2, "a"], [2, 3, "b"],[1, 3, "c"]]);
KQ := PathAlgebra(K,Q);
A := KQ;
matrices := [ ["a", [[1,0,0],[0,1,0]]], 
              ["b", [[0,1],[1,0],[0,1]]], 
              ["c", [[0,0],[1,0]]] ];
mX := RightModuleOverPathAlgebra(A,matrices);

E := AlmostSplitSequence2( mX );
```

To compute just an E module add following line:

```
E := Range(E[1]);
```
