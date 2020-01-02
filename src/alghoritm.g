##############################################################
# Část 4.4 ###################################################
##############################################################

SuppProjModule := function(mP)
  local A, PP, mPs, n, common, i, j, diff,
        in_multiplicities, ou_multiplicities;

  A := RightActingAlgebra(mP);
  PP:= IndecProjectiveModules(A);
  in_multiplicities := [];
  ou_multiplicities := [];
  n := 0;

  # Přes všechny moduly e_iA.
  for i in [1..Length(PP)] do
    Add(in_multiplicities, 0);

    # Zkoušíme kolikrát je daný e_iA obsažen v P.
    repeat
      common := CommonDirectSummand(mP, PP[i]);
      if IsList(common) then
        in_multiplicities[i] := in_multiplicities[i] + 1;
        mP := common[2];
      fi;
    until IsList(common) = false;

    n := Maximum([n, in_multiplicities[i]]);
  od;

  # Spočteme P`.
  mPs := [];
  for i in [1..Length(PP)] do
    diff := n - in_multiplicities[i];
    ou_multiplicities[i] := diff;

    for j in [1..diff] do
      Add(mPs, PP[i]);
    od;
  od;
  mPs := DirectSumOfModules(mPs);

  return [n, mPs, in_multiplicities, ou_multiplicities];
end;

##############################################################
# Část 4.5 ###################################################
##############################################################

ProjectiveBasisVectorGens := function(PP)
  local A;

  A := RightActingAlgebra(PP[1]);

  return List(BasisOfProjectives(A), b -> Flat(b));
end;

ExtractHomMatrices := function(matrix, mM, mN)
  local A, Q, d_mM, d_mN, used_x, used_y, i, j, k, dx, dy,
    matrices;

  A := RightActingAlgebra(mM);
  Q := QuiverOfPathAlgebra(A);

  matrices := [];
  d_mM := DimensionVector(mM);
  d_mN := DimensionVector(mN);
  used_x := 0;
  used_y := 0;
  for i in [1..NumberOfVertices(Q)] do
    dx := d_mN[i];
    dy := d_mM[i];

    matrices[i] := [];

    if dy = 0 and dx = 0 then
      Add(matrices[i], [0]);
    elif dy = 0 then
      Add(matrices[i], List([1..dx], j -> 0));
    elif dx = 0 then
      Add(matrices[i], List([1..dy], j -> [0]));
    else
      for j in [1+used_y..dy+used_y] do
        Add(matrices[i], List([1+used_x..dx+used_x], k -> matrix[j][k]));
      od;
    fi;

    used_x := used_x + dx;
    used_y := used_y + dy;
  od;

  return matrices;
end;

##############################################################
# Část 4.6 ###################################################
##############################################################

FromHomToProjRep := function(f, mP_star)
  local i, j, incl, incl2, proj, mu, mu_f, pi, mu2,
    A, e_i, e_i_op, fe_i, result, mP, me_iA, PP, mA,
    as_algebra_element, lambda, lambda_op, pi_f_ei, coeffs;

  mP := Source(f);
  mA := Range(f);
  A := RightActingAlgebra(mP);

  # Moduly e_iA.
  PP := IndecProjectiveModules(A);

  incl := DirectSumInclusions(mP);
  incl2:= DirectSumInclusions(mP_star);
  proj := DirectSumProjections(mA);
  as_algebra_element := ProjectiveBasisVectorGens(PP);

  result := Zero(mP_star);

  # Přes všechny inkluze z direktních sčítanců P tedy moduly e_iA.
  for i in [1..Length(incl)] do
    # Slozime s inkluzi na homomorfismus e_iA --> P -> A.
    mu := incl[i];
    mu_f := mu * f;

    # Spočteme e_iA a e_i.
    me_iA := Source(mu_f);
    e_i := MinimalGeneratingSetOfModule(me_iA)[1];

    # Zobrazíme e_i homomorfismem f.
    fe_i := ImageElm(mu_f, e_i);

    # Nyní budeme prvek f(e_i) projektovat do modulů e_iA ...
    # ... k jeho obrazům najdeme korespondující prvek ...
    # ... algebry A a výsledky sečteme.
    lambda := Zero(A);
    for j in [1..Length(proj)] do
      pi := proj[j];
      pi_f_ei := ImageElm(pi, fe_i);
      coeffs  := Coefficients(Basis(PP[j]), pi_f_ei);
      lambda  := lambda + coeffs * as_algebra_element[j];
    od;

    # Spočteme opposite prvek.
    lambda_op := OppositePathAlgebraElement(lambda);

    # Vnoříme do P*.
    mu2 := incl2[i];
    e_i_op := MinimalGeneratingSetOfModule(Source(mu2))[1];
    result := result + ImageElm(mu2, e_i_op ^ lambda_op);
  od;

  return result;
end;


FromProjRepToHom := function(p, mP, mP_star, mA, 1_mA)
  local proj, proj2, i, j, k, Ae_i, e_iA, proj_p, coeffs,
    as_algebra_element, PP, PP_op, A, A_op, lambda,
    lambda_op, v, proj2_v, matrix, as_algebra_element2,
    lambda2, result, K, image, matrices;

  A    := RightActingAlgebra(mP);
  A_op := RightActingAlgebra(mP_star);
  K    := LeftActingDomain(A);

  # Moduly e_iA resp. Ae_i.
  PP    := IndecProjectiveModules(A);
  PP_op := IndecProjectiveModules(A_op);

  # Projekce P*->Ae_i resp. P->e_iA
  proj  := DirectSumProjections(mP_star);
  proj2 := DirectSumProjections(mP);

  as_algebra_element := ProjectiveBasisVectorGens(PP_op);
  as_algebra_element2 := ProjectiveBasisVectorGens(PP);

  result := [];

  # Přes všechny projekce Ae_i->P*.
  for j in [1..Length(proj)] do
    Ae_i := Range(proj[j]);

    # Zjistíme na které Ae_i projektujeme.
    for i in [1..Length(PP_op)] do
      if (IsomorphicModules(PP_op[i], Ae_i)) then
        break;
      fi;
    od;

    # Projektujeme p do Ae_i, spočteme korespondující prvek
    # algebry A_op a k němu opposite prvek algebry A.
    proj_p := ImageElm(proj[j], p);
    coeffs := Coefficients(Basis(Ae_i), proj_p);
    lambda := coeffs * as_algebra_element[i];
    lambda_op := OppositePathAlgebraElement(lambda);

    # Sestavíme matici odpovídající zobrazení P->A.
    matrix := [];
    for v in BasisVectors(Basis(mP)) do
      e_iA := Range(proj2[j]);

      # Projektujeme v do e_iA.
      proj2_v := ImageElm(proj2[j], v);

      # Spočteme odpovídající prvek algebry A.
      coeffs := Coefficients(Basis(e_iA), proj2_v);
      lambda2 := coeffs * as_algebra_element2[i];
      image := (1_mA ^ lambda_op) ^ lambda2;

      Add(matrix, Coefficients(Basis(mA), image));
    od;

    result := result + matrix;
  od;

  matrices := ExtractHomMatrices(result, mP, mA);

  return RightModuleHomOverAlgebra(mP, mA, matrices * One(K));
end;

##############################################################
# Část 4.7 ###################################################
##############################################################

S_Star := function(s, mP0, mP1, mP0_star, mP1_star, mA, 1_mA)
  local v, f, fs, image, matrix, matrices, A, K;

  A := RightActingAlgebra(mP1);
  K := LeftActingDomain(A);

  matrix := [];
  for v in BasisVectors(Basis(mP0_star)) do
    f  := FromProjRepToHom(v, mP0, mP0_star, mA, 1_mA);
    fs := s * f;
    image := FromHomToProjRep(fs, mP1_star);
    Add(matrix, Coefficients(Basis(mP1_star), image));
  od;

  matrices := ExtractHomMatrices(matrix, mP0_star, mP1_star);

  return RightModuleHomOverAlgebra(mP0_star, mP1_star, matrices * One(K));
end;

##############################################################
# Část 4.8 ###################################################
##############################################################

IsomorphismProjAndAn := function(mP1_P2, mAn)
  local iso, used, i, j,
        proj_P1_P2, proj_P1_P2_fin, proj_PX,
        incl_An, incl_An_fin, incl_A,
        f, g;

  # Projekce P1_P2 ->> P1 resp. P1_P2 ->> P2 ...
  proj_P1_P2 := DirectSumProjections(mP1_P2);

  # ... složíme s projekcemi P1 ->> e_iA resp. P2 ->> e_iA.
  proj_P1_P2_fin := [];
  for f in proj_P1_P2 do
    proj_PX := DirectSumProjections( Range(f) );

    for g in proj_PX do
      Add(proj_P1_P2_fin, f * g);
    od;
  od;

  # Inkluze A -> A^n ...
  incl_An := DirectSumInclusions(mAn);

  # ... složíme s inkluzemi e_iA ->> A.
  incl_An_fin := [];
  for f in incl_An do
    incl_A := DirectSumInclusions( Source(f) );

    for g in incl_A do
      Add(incl_An_fin, g * f);
    od;
  od;

  # Nyní spárujeme spočtené projekce a inkluze
  # a vzniklá zobrazení P1_P2 -> A^n sečteme.
  iso := ZeroMapping(mP1_P2, mAn);
  used := [1..Length(incl_An_fin)];
  for g in proj_P1_P2_fin do
    for i in [1..Length(incl_An_fin)] do
      f := incl_An_fin[i];

      if (not used[i] = true) and Source(f) = Range(g) then
        iso := iso + g * f;
        used[i] := true;
        break;
      fi;
    od;
  od;

  return iso;
end;

IsomorphismAnAndProj := function(mP1_P2, mAn)
  local iso, used, i, j,
        incl_P1_P2, incl_P1_P2_fin, incl_PX,
        proj_An, proj_An_fin, proj_A,
        f, g;

  # Projekce P1_P2 ->> P1 resp. P1_P2 ->> P2 ...
  incl_P1_P2 := DirectSumInclusions(mP1_P2);

  # ... složíme s projekcemi P1 ->> e_iA resp. P2 ->> e_iA.
  incl_P1_P2_fin := [];
  for f in incl_P1_P2 do
    incl_PX := DirectSumInclusions( Source(f) );

    for g in incl_PX do
      Add(incl_P1_P2_fin, g * f);
    od;
  od;

  # Inkluze A -> A^n ...
  proj_An := DirectSumProjections(mAn);

  # ... složíme s inkluzemi e_iA ->> A.
  proj_An_fin := [];
  for f in proj_An do
    proj_A := DirectSumProjections( Range(f) );

    for g in proj_A do
      Add(proj_An_fin, f * g);
    od;
  od;

  # Nyní spárujeme spočtené projekce a inkluze
  # a vzniklá zobrazení P1_P2 -> A^n sečteme.
  iso := ZeroMapping(mAn, mP1_P2);
  used := [1..Length(proj_An_fin)];
  for g in incl_P1_P2_fin do
    for i in [1..Length(proj_An_fin)] do
      f := proj_An_fin[i];

      if (not used[i] = true) and Range(f) = Source(g) then
        iso := iso + f * g;
        used[i] := true;
        break;
      fi;
    od;
  od;

  return iso;
end;

##############################################################
# Část 4.11 ##################################################
##############################################################

 TensorProductMap := function(m, n, mM, mN, mDM, B_hom_mN_mDM)
  local coeffs_m, coeffs_f_i_n, i, B_hom_images, f_i_n;

  coeffs_m := Coefficients(Basis(mM), m);
  B_hom_images := [];

  f_i_n := List(B_hom_mN_mDM, f_i -> ImageElm(f_i, n));

  for i in [1..Length(f_i_n)] do
    coeffs_f_i_n := Coefficients(Basis(mDM), f_i_n[i]);

    B_hom_images[i] := coeffs_m * coeffs_f_i_n;
  od;

  return B_hom_images;
end;

##############################################################
# Almost split sequence algorithm ############################
##############################################################

AlmostSplitSequence2 := function(mX)
  local i, j, m, n,

        A, Q, K,

        # Část 4.3
        t, mP0, mOmega, omega, kernel_inc, s, mP1,
        PP, PP_op, A_op, mA,

        # Část 4.4
        supp, mP1s, mP1_mP1s, mAn,

        # Část 4.7
        mP0_star, mP1_star, multiplicities0, multiplicities1,
        s_star, t_hat, mTrX, mDTrX, B_hom_mDTrX_mOmega, 1_mA,

        # Část 4.9
        incl, e_iA, e_i, mu, psi, rho, nu, psi_inv, pi,

        # Část 4.12
        mu_psi_rho, omega_pi_psi_inv_nu, omega_pi_psi_inv_nu_1_A,
        mu_psi_rho_el, psi_omega, t_mu_psi_rho_el,

        # Část 4.13
        mTrX_mOmega, B_mTrX_mOmega, B_mOmega, B_mTrX, n_images, m_n, V, B_V,
        B_V_new, added,

        # Část 4.14
        images, matrices, d_mOmega, d_mDTrX, used_x, used_y, dx, dy, xi,

        # Část 4.15
        mE, generator;

  A := RightActingAlgebra(mX);
  Q := QuiverOfPathAlgebra(A);
  K := LeftActingDomain(A);

  # Část 4.3 #################################################\

  t          := ProjectiveCover(mX);
  mP0        := Source(t);
  mOmega     := Kernel(t);
  omega      := ProjectiveCover(mOmega);
  kernel_inc := KernelInclusion(t);
  s          := omega * kernel_inc;
  mP1        := Source(omega);

  A_op  := OppositePathAlgebra(A);
  PP    := IndecProjectiveModules(A);
  PP_op := IndecProjectiveModules(A_op);

  mA    := DirectSumOfModules(PP);

  # Část 4.4 #################################################

  supp := SuppProjModule(mP1);
  mP1s := supp[2];
  n    := supp[1];
  mP1_mP1s := DirectSumOfModules([mP1, mP1s]);
  mAn := DirectSumOfModules( List([1..n], i -> mA) );

  # Část 4.7 #################################################

  multiplicities0 := SuppProjModule(mP0)[3];
  mP0_star := [];
  for i in [1..Length(multiplicities0)] do
    for j in [1..multiplicities0[i]] do
      Add(mP0_star, PP_op[i]);
    od;
  od;
  mP0_star := DirectSumOfModules(mP0_star);

  multiplicities1 := SuppProjModule(mP1)[3];
  mP1_star := [];
  for i in [1..Length(multiplicities1)] do
    for j in [1..multiplicities1[i]] do
      Add(mP1_star, PP_op[i]);
    od;
  od;
  mP1_star := DirectSumOfModules(mP1_star);

  # Spočteme prvek 1_A reprezentace A  jakožto součet prvků
  # e_i z reprezentací e_iA  vnořených do A.
  1_mA := Zero(mA);
  incl := DirectSumInclusions(mA);
  for i in [1..Length(incl)] do
    e_iA := Source(incl[i]);
    e_i := MinimalGeneratingSetOfModule(e_iA)[1];
    1_mA := 1_mA + ImageElm(incl[i], e_i);
  od;

  s_star := S_Star(s, mP0, mP1, mP0_star, mP1_star, mA, 1_mA);
  t_hat := CoKernelProjection(s_star);
  mTrX   := Range(t_hat);
  mDTrX := DualOfModule(mTrX);
  B_hom_mDTrX_mOmega := HomOverAlgebra(mOmega, mDTrX);

  # Část 4.9 #################################################

  # Levá strana tenzorového součinu
  mu     := DirectSumInclusions(mP1_mP1s)[1];
  psi    := IsomorphismProjAndAn(mP1_mP1s, mAn);
  rho    := DirectSumProjections(mAn);

  # Pravá strana tenzorového součinu
  nu     := DirectSumInclusions(mAn);
  psi_inv:= IsomorphismAnAndProj(mP1_mP1s, mAn); # ~ InverseOfIsomorphism (psi);
  pi     := DirectSumProjections(mP1_mP1s)[1];

  # Část 4.12 ################################################

  mu_psi_rho := mu * psi * rho;
  omega_pi_psi_inv_nu := nu * psi_inv * pi * omega;

  # omega * pi * psi^(-1) * nu(1_A).
  omega_pi_psi_inv_nu_1_A := List(omega_pi_psi_inv_nu, f -> ImageElm(f, 1_mA));

  # Spočteme zobrazení mu_psi_rho jako elementy modulu P1*.
  mu_psi_rho_el := List(mu_psi_rho, f -> FromHomToProjRep(f, mP1_star));
  t_mu_psi_rho_el := List(mu_psi_rho_el, el -> ImageElm(t_hat, el));

  # Spočteme náš hlavní bázovy prvek.
  psi_omega := [];
  for i in [1..Length(t_mu_psi_rho_el)] do
    m := t_mu_psi_rho_el[i];
    n := omega_pi_psi_inv_nu_1_A[i];

    Add(psi_omega, TensorProductMap(m, n, mTrX, mOmega, mDTrX, B_hom_mDTrX_mOmega));
  od;
  psi_omega := Sum(psi_omega);

  # Část 4.13 ################################################

  # Pole obsahující na i-té pozici pole
  # [t_1\otimes\omega_i, ... ,t_n\otimes\omega_i].
  # To využijeme v následující části. Z důvodu
  # efektivnosti si ho ale předpočítáme nyní.
  mTrX_mOmega := [];

  # Pole nenulových prvků t_i\otimes\omega_i.
  B_mTrX_mOmega := [];

  # Spočteme bázi tenzorového součinu TrX a Omega.
  B_mOmega := BasisVectors(Basis(mOmega));
  B_mTrX := BasisVectors(Basis(mTrX));
  for n in B_mOmega do
    n_images := [];

    for m in B_mTrX do
      m_n := TensorProductMap(m, n, mTrX, mOmega, mDTrX, B_hom_mDTrX_mOmega);

      Add(n_images, m_n);
      if not Sum(m_n) = 0 and not Sum(m_n) = Zero(K) then
        Add(B_mTrX_mOmega, m_n);
      fi;
    od;

    Add(mTrX_mOmega, n_images);
  od;

  # Jeden bázový prvek nahradíme význačným prvkem z přechozí sekce.
  V := VectorSpace(K, B_mTrX_mOmega);
  B_V := CanonicalBasis(V);
  B_V_new := [psi_omega];
  added := false;
  for i in [1..Length(B_V)] do
    if not psi_omega[i] = Zero(K) and not added then
      added := true;
    else
      Add(B_V_new, B_V[i]);
    fi;
  od;

  # Část 4.14 ################################################

  # images[i][j] = 1. koeficient t_j\otimes\omega_i vzhledem k bázi B_mDTrX_Omega.
  images := [];
  for i in [1..Length(B_mOmega)] do
    Add(images, List(mTrX_mOmega[i], v -> Coefficients(Basis(V, B_V_new), v)[1] ));
  od;

  matrices := ExtractHomMatrices(images, mOmega, mDTrX);
  xi := RightModuleHomOverAlgebra(mOmega, mDTrX, matrices * One(K));

  # Část 4.15 ################################################

  mE := PushOut(kernel_inc, xi);

  generator := [mE[1], CoKernelProjection(mE[1])];

  return generator;
end;







