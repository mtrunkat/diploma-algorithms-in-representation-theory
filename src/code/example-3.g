K := GF(13);
Q := Quiver(4, [[1, 2], [1, 3], [1, 4]]);
KQ := PathAlgebra(K, Q);
rels := [];
A := KQ/rels;
mX := IndecInjectiveModules(A)[1];

# Nyní budeme počítat všechny nerozložitelné moduly.
buffer := [mX]; #Začínáme s jedním modulem.
position := 1;
repeat
  current := buffer[position];

  # Projektivní přeskočíme.
  if IsProjectiveModule(current) then
    position := position + 1;
    continue;
  fi;

  # Spočteme generátor skoro štěpitelných posloupností a
  # rozložíme ho na nerozložitelné direktní sčítance.
  mE := Range( AlmostSplitSequence2(current)[1] );
  summands := DecomposeModuleWithMultiplicities(mE)[1];

  # Jdeme přes všechny sčítance.
  for summand in summands do
    # Zjistíme jestli není izomorfní nějakému již objevenému modulu.
    isNew := true;
    for old in buffer do
      if IsomorphicModules(summand, old) then
        isNew := false;
        break;
      fi;
    od;

    # Pokud ne, tak ho přidáme do zásobníku.
    if isNew then
      Add(buffer, summand);
    fi;
  od;

  position := position + 1;
until Length(buffer) < position or Length(buffer) >= 60;

# Zobrazíme výsledek.
Print(buffer);
