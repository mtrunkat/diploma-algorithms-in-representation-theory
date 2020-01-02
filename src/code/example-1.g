GetModule := function(i)
  local K, Q, KQ, A, matrices, mX;

  K := Rationals;
  Q := Quiver(3, [[1, 2, "a"], [2, 3, "b"],[1, 3, "c"]]);
  KQ := PathAlgebra(K,Q);
  A := KQ;
  matrices := [ ["a", [[1,0],[0,1]]], ["b", [[0],[1]]], ["c", [[1],[0]]] ];
  mX := RightModuleOverPathAlgebra(A, matrices);

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
TestPerformance(100);
