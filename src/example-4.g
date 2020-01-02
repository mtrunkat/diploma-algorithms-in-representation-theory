#################################################################
### 1. srovnání rychlosti se zvyšujícím se počtem vrcholů i hran.
#################################################################

GetModule := function(count)
  local K, Q, KQ, els, A, mX, i, arrows;

  arrows := [];

  for i in [2..count] do
    Add(arrows, [1, i]);
  od;

  K := GF(13);
  Q := Quiver(count, arrows);
  KQ := PathAlgebra(K, Q);
  rels := [];
  A := KQ/rels;
  mX := IndecInjectiveModules(A)[1];

  return mX;
end;

# Rychlost algoritmu AlmostSplitSequence:
for i in [2..20] do
  mX := GetModule(i);

  time := Runtime();
  AlmostSplitSequence( mX );
  time := Float(Runtime() - time);

  Print("(", i, ",", time, ")", "\n");
od;

# Rychlost algoritmu AlmostSplitSequence2:
for i in [2..20] do
  mX := GetModule(i);

  time := Runtime();
  AlmostSplitSequence2( mX );
  time := Float(Runtime() - time);

  Print("(", i, ",", time, ")", "\n");
od;


#################################################################
### 2. srovnání rychlosti se zvyšujícím se počtem vrcholů.
#################################################################

GetModule := function(count)
  local K, Q, KQ, rels, A, mX, i, j, arrows;

  arrows := [];

  for i in [2..3] do
    for j in [1..count] do
      Add(arrows, [1, i]);
    od;
  od;

  K := GF(13);
  Q := Quiver(3, arrows);
  KQ := PathAlgebra(K, Q);
  rels := [];
  A := KQ/rels;
  mX := IndecInjectiveModules(A)[1];

  return mX;
end;

# Rychlost algoritmu AlmostSplitSequence:
for i in [1..4] do
  mX := GetModule(i);

  time := Runtime();
  AlmostSplitSequence( mX );
  time := Float(Runtime() - time);

  Print("(", i, ",", time, ")", "\n");
od;

# Rychlost algoritmu AlmostSplitSequence2:
for i in [1..4] do
  mX := GetModule(i);

  time := Runtime();
  AlmostSplitSequence2( mX );
  time := Float(Runtime() - time);

  Print("(", i, ",", time, ")", "\n");
od;
