GetModule := function(i)
  local K, Q, KQ, A, mat, mX, gen, a, b, c, d, e, rels;

  K := Rationals;
  Q := Quiver(3,[[1,2,"a"],[1,2,"b"],[2,2,"c"],[2,3,"d"],[3,1,"e"]]);
  KQ := PathAlgebra(K, Q);
  gen := GeneratorsOfAlgebra(KQ);
  a := gen[4];
  b := gen[5];
  c := gen[6];
  d := gen[7];
  e := gen[8];
  rels := [c^2,a*c*d-b*d,e*a, e*b];
  A := KQ/rels;
  mat :=[["a", One(K) * [[0,1],[1,1]]],
         ["b", One(K) * [[1,0],[1,0]]],
         ["c", One(K) * [[0,0],[1,0]]],
         ["d", One(K) * [[1,1],[0,1]]],
         ["e", One(K) * [[0,0],[0,0]]]
        ];
  mX := RightModuleOverPathAlgebra(A,mat);

  return mX;
 end;

# Otestujeme správnost výsledku:
mX := GetModule(1);
E1 := AlmostSplitSequence( mX );
E1 := Range(E1[1]);
E2 := AlmostSplitSequence2( mX );
E2 := Range(E2[1]);
IsomorphicModules(E1, E2);

# Otestujeme dobu běhu:
TestPerformance(20);
