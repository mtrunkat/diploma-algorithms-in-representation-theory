TestPerformance := function(iter)
  local i, time;

  time := Runtime();
  for i in [1..iter] do
    AlmostSplitSequence( GetModule(i) );
  od;
  time := Float((Runtime() - time) / iter / 1000);
  Print("Doba běhu AlmostSplitSequence: ", time, "s \n");

  time := Runtime();
  for i in [1..iter] do
    AlmostSplitSequence2( GetModule(i) );
  od;
  time := Float((Runtime() - time) / iter / 1000);
  Print("Doba běhu AlmostSplitSequence2: ", time, "s \n");
end;
