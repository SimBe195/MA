/***************************************
*                                      *
* Local unimodular/squarefree lattices *
*                                      *
* 2015 D. Lorch and M. Kirschmer       *
*                                      *
***************************************/

function FindRho(p) // needed for UnimodularLattices
  // See p. 251 in O'Meara. We fix \rho such that \Delta := 1 - 4\rho is a fixed unit of quadratic defect 4\rho.
  // Note that O'Meara writes "\Delta = 1 + 4\rho", but was wrong. Pfeuffer corrected this to 1-4\rho.
  assert Minimum(p) eq 2;
  R:= Order(p); f:= 2*Valuation(R ! 2, p);
  Q, h:= quo< R | p^(f+1) >;
  ok:= exists(x){ x : q in Q | x notin p and QuadraticDefect(x, p) eq f where x:= q @@ h };
  assert ok;
 
  r:= x-1; v:= Valuation(r, p); 
  pi:= PrimitiveElement(p);
  k,h:= ResidueClassField(p);
  while v ne f do
    assert IsEven(v);
    y:= (r / pi^v) @ h;
    ok, s:= IsSquare(y); assert ok;
    x:= x / (1+(s@@h)*pi^(v div 2))^2;
    r:= x-1; v:= Valuation(r, p);
  end while;

  rho:= (1-x)/4;
  assert Valuation(rho, p) eq 0;
  return rho;
end function;

intrinsic IsUnimodular(L::LatMod, p::RngOrdElt) -> BoolElt
{returns true iff L is unimodular when viewed at p}
  require BaseRing(L) cmpeq Order(p) : "Incompatible arguments";
   _,_,E := JordanDecomposition(L, p);
  return Set(E) eq {0};
end intrinsic;



intrinsic LiftUnits(p::RngOrdIdl) -> []
{ Lift unit square class representatives: for each square class, choose a representative u_i that fulfills the condition u_i = 1 + j_i where the quadratic defect of j_i (as defined in O'Meara) is j_i * R.}
  e := Valuation(Order(p)!2, p);
  pi := UniformizingElement(p);

  // p a prime ideal over 2 of a number field K 
  assert Minimum(p) eq 2;

  U := UnitSquareClassReps(p);
  UU := [];
  k, h := ResidueClassField(p);
   while #U gt 0 do
    u := U[#U];
    Prune(~U);

    if IsOne(u) then Append(~UU, u); continue; end if; // treat the trivial square class separately

    ok, s := IsSquare(h(u));
    assert ok;
    assert Valuation((s @@ h)^2, p) eq 0; 
    uu := u / (s @@ h)^2;
    assert IsOne(h(uu));

    // lifting:
    val := Valuation(uu-1, p);
    if (GF(2)!val eq 1) and (val lt 2*e) then
      // an element with odd valuation is its own quadratic defect.
      // Hence, we are finished with uu.
      Append(~UU, uu);
    elif (val lt 2*e) then
      // lifting: cf. O'Meara 63:2
      // see lat.m
      w := Valuation(uu-1, p);
      ok, s:= IsSquare(h((uu - 1) / pi^w)); assert ok;
      uu /:= (1+(s@@h)*pi^(w div 2))^2;
      assert Valuation(uu-1, p) gt w;  
 
      // put the lifted unit to the end of the todo-list:
      Append(~U, uu);
    elif (val eq 2*e) then
      // O'Meara does not say anything about being able to lift further.
      // But since we are walking through square class representatives 
      // and uu cannot be the class of squares, we know that the quadratic
      // defect must have valuation 2*e.
      Append(~UU, uu);
    end if;
  end while;
  return UU;
end intrinsic;

BuildLookupTable := function(UU, p)
  Result := [* *];
  for i in [1..#UU] do 
    Result[i] := [* QuadraticDefect(UU[i] * UU[k], p): k in [1..#UU]| k le i *];
  end for;
  return Result;
end function;

intrinsic UnimodularLattices(p::RngOrdIdl, m::RngIntElt: LowerDimension:=[], Check:=false) -> []
{Returns unimodular lattices of rank m over the completion of Order(p) at p. The lattices returned are pairwise non-isometric.}
  R := Order(p); 
  F := NumberField(R);

  if Check then printf "UnimodularLattices started in Debug mode, dim=%o\n\n", m; end if;

  // p a prime ideal of a number field K 
  // m is the desired dimension.
  // If m in [2, 3, 4], then LowerDimension is ignored, otherwise LowerDimension 
  // should be a list of unimodular lattices in dimension k-2 (of type LatticeModule).
  // If an empty list is given, LowerDimension will be calculated on-the-fly.
  LatModDiagonalJoin := func<A, L | LatticeModule(DiagonalJoin(AA, L`Form) where AA is ChangeRing(A, BaseRing(Parent(L`Form))))>;
 
  if Minimum(p) ne 2 then
    if Check then printf "non-dyadic UnimodularLattices called for dimension %o.\n", m; end if;
    // we use the classification in O'Meara 92:1:
    UU := UnitSquareClassReps(p);
    nonsq := [x: x in UU| not IsOne(x)]; assert #nonsq eq 1; nonsq := nonsq[1];
    return [LatticeModule(MatrixRing(F, m)!DiagonalMatrix([1^^m])), LatticeModule(MatrixRing(F, m)!(DiagonalMatrix([F!1^^(m-1)] cat [nonsq])))];
  end if;  
 
 
 
 
 
 
  A_matrix := func<p, a, b | MatrixRing(NumberField(Order(p)), 2)![a,1,1,b]>;
  
  // if not assigned(LowerDimension) then LowerDimension := []; end if;
 
  
  if (m ge 3) then
    if (#LowerDimension eq 0) then
      LowerDimension := $$(p, m-2: LowerDimension := [], Check:=Check);
	  //printf "%o lattices in dimension %o calculated.\n", #LowerDimension, m-2;
    else
      error if not (Type(LowerDimension[1]) eq LatMod) and &and[Rank(l) eq m-2: l in LowerDimension], Sprintf("LowerDimension must supply LatMods of dimension %o", m-2);
    end if;
  end if;
  
  e := Valuation(Order(p)!2, p);
  pi := UniformizingElement(p);

  UU := LiftUnits(p);
  LookupTable := BuildLookupTable(UU, p);
  
  rho := FindRho(p);
  Result := [];
  Debug := [];
  
  if m eq 1 then
    Result := [LatticeModule(MatrixRing(F, 1)![u]): u in UU];
    Debug := [-1: u in UU];
    if Check then printf "UnimodularLattices finished in Debug mode\n\n"; end if;
    return Result;
  end if;
  
  
//   for i in [1..#UU] do for j in [i+1..#UU] do printf "LT[%o,%o]=%o\n", i,j,LookupTable[j,i]; end for; end for;
  
  
  if m eq 2 then
    debug := 0;
    for norm in [0..e] do // norm = possible valuation of a norm generator
      for weight in [norm..e] do // weight = possible valuation of a weight generator (cf. p. 253 O'Meara) 
        if GF(2)!(norm+weight) eq 0 then if weight ne e then continue; end if; end if;
        if (norm eq weight) then if norm ne e then continue; end if; end if;
        for det_unit in [1..#UU] do
        for a_unit in [1..#UU] do
          // the candidate determinant;
          // u_det runs through the negative determinants of our lattices:
          u_det := UU[det_unit];
          u_a := UU[a_unit];
          
          // Auxiliary existence conditions for a lattice with these weight / norm valuations:
          if Valuation(u_det-1, p) lt norm + weight then continue; end if;
          if (Valuation(u_det-1, p) ne norm + weight) and (weight lt e) then continue; end if;
          

          // each u corresponds to a unique unimodular 2-dimensional 
          // lattice, as follows:
          a := u_a*pi^norm;
          b := (u_det-1)/(-a);        
          A := A_matrix(p, a, b); // = MatrixRing((F), 2)![a, 1, 1, b];
          
          // the new lattice's Hasse invariant:
          // the Hasse invariant of a quadratic space defined by a Gram matrix A_matrix(p, a, b) is 
          // the Hilbert symbol of the diagonalisation of this matrix, i.e. of diag(a, a*Determinant(A_matrix(p, a, b))).
          // Hilbert symbol calculation: (a, det*a) = (a, a)*(a, det) = (a,-1)*(a,det) = (a, -det).
          HasseInv := MyHilbertSymbol(F!a, F!(u_det), p);

          // do not generate isometric lattices:
          // lattices A_matrix(p, u*pi^norm, pi^weight) and A_matrix(p, v*pi^norm, pi^weight) with the same determinant are isometric iff QuadraticDefect(a*a') >= weight -norm, cf. 93:10 and 93:6 O'Meara (v*\pi^norm \cong v'*\pi^norm \mod p^weight   iff   vv' is a square mod \pi^(weight-norm))
          for i in [1..a_unit-1] do if LookupTable[a_unit, i] ge  weight - norm  then 
            if HasseInv eq MyHilbertSymbol(F!(UU[i]*pi^norm), F!(u_det), p) then
              if Check then printf "Skipping unit[%o] because QuadraticDefect(unit[%o]*unit[%o]) = %o >= weight - norm = %o, and these lattices have the same Hasse invariants\n", a_unit, a_unit, i,  LookupTable[a_unit, i], weight-norm; end if;
              continue a_unit; 
            end if;
          end if; end for;   

          
          
          debug +:=1; 
          if Check then printf "debug=%o: norm=%o, a=%o, weight=%o, det_unit=%o, a_unit=%o\n", debug, norm, a, weight, det_unit, a_unit; end if;
//assert not IsLocallyIsometric(LatticeModule(A), AAAA, p);
          
       
          // test the invariants we claim:
          if Check then
            _, ss, ww, aa, _, _ := GenusSymbol(LatticeModule(A), p);
            assert Min(Valuation(a, p) + QuadraticDefect((b)/a, p), e) eq weight;
            assert #ss eq 1;
            assert ss[1] eq 0;
            assert ww[1] eq weight;
            assert IsUnimodular(LatticeModule(A), p); 

            for k in  [1..#Result-1] do if IsLocallyIsometric(Result[k], Result[#Result], p) then printf "[dim=2: debug=%o, %o/%o] ", debug, k, #Result; assert false; end if; end for;
          end if;
          Append(~Result, LatticeModule(A));
          Append(~Debug, 0);
          end for;
        end for;
      end for;
    end for;  
    if Check then printf "UnimodularLattices finished in Debug mode\n\n"; end if;
  	return Result;
  end if;
    
    
    
  if m ge 3 then
    // first we take care of 93:18(ii) O'Meara,
	// i.e. the cases where a hyperbolic plane splits off:
    for L in LowerDimension do
//	  printf "Types: %o -- %o  \n\n\n", Type(A_matrix(p, 0, 0)), Type(GramMatrix(L));
      r := LatModDiagonalJoin(A_matrix(p, 0, 0), L);
	  if m in [3,4] then 
	    // check norm+weight even:
        _, ss, ww, aa, _, _ := GenusSymbol((r), p);
//		printf "aa=%o, ww=%o, types: %o, %o", aa,ww,Type(aa), Type(ww);

		assert #aa eq 1;
		assert #ww eq 1;
		// Only the lattices where  valuation(norm, p) + valuation(weight, p) 
		// is an even number need to be generated here. The others are generated
		// directly below.
		if GF(2)!(Valuation(aa[1], p) + (ww[1])) ne 0 then continue; end if;
        if Check then assert IsUnimodular(r, p); end if;
	  end if;
      Append(~Result, r);
      Append(~Debug, 3);
        if Check then for k in  [1..#Result-1] do if IsLocallyIsometric(Result[k], Result[#Result], p) then printf "[dim >= 3: %o/%o] ", k, #Result; end if; end for;      end if;
      
    end for;
  end if;
	
  
// DebugInvariants := AssociativeArray();


  // The cases in dimensions 3 and 4 where norm + weight is an odd number:
  // cf. 93:18 (iii)/(iv) O'Meara:
  if m in [3,4] then
    for norm in [0..GF(2)!m eq 0 select e else 0] do // norm = possible valuation of a norm generator
      for weight in [norm..e] do // weight = possible valuation of a weight generator (cf. p. 253 O'Meara)
        // these cases assume that valuation(norm) + valuation(weight) is odd:
        if GF(2)!(norm + weight) eq 0 then continue; end if;
        //// if (m eq 3) and (norm gt 0) then continue; end if; 
    
        // run through all the candidate determinants:
        for u in UU do

          NN := #Result;

          if m eq 3 then
            // 93:18 (iv):
            Append(~Result, LatticeModule(DiagonalJoin(A_matrix(p, pi^weight, 0), MatrixRing(F, 1)![-u])));
            Append(~Debug, 1);
            Append(~Result, LatticeModule(DiagonalJoin(A_matrix(p, pi^weight, 4*rho*(pi^(-weight))), MatrixRing(F, 1)![(-u)*(1-4*rho)])));
            Append(~Debug, 2);
            if Check then 
              assert IsUnimodular(r, p) where r is Result[#Result]; 
              assert IsUnimodular(r, p) where r is Result[#Result-1];               
            end if;

          elif m eq 4 then
            // 93:18 (iii):
            for a_unit in [1..#UU] do
              a := UU[a_unit]*pi^norm;

              // do not generate isometric lattices:
              for i in [1..a_unit-1] do if LookupTable[a_unit, i] ge weight - norm then continue a_unit; end if; end for;   

              // E.g. UnimodularLattices(ideal<EquationOrder(Polynomial(\[1, -3, -1, 1])) | \[ 2, 0, 0 ], \[ 1, 1, 0 ]>, 4) fails.
              
              // not all of the lattices in 93:18(iii) are admissible:
              if Valuation((u-1)/a, p) lt weight then continue; end if;   // we must have: v_p(u-1) >= v_p(weight*norm). Der erste orthogonale Summand kümmert sich um die Norm, die zweite um die Weight. Auf dem zweiten Diagonaleintrag steht eine Zahl mit höherer Bewertung -- falls das nicht erfüllt ist, werden die Vorgaben kaputt gemacht.
              
              Append(~Result, LatticeModule(DiagonalJoin(A_matrix(p, a, -(u-1)/a), A_matrix(p, pi^weight, 0))));
              Append(~Debug, 4);
              Append(~Result, LatticeModule(DiagonalJoin(A_matrix(p, a, -(u-1-4*rho)/a), A_matrix(p, pi^weight, 4*rho/(pi^weight)))));
              Append(~Debug, 5);

              if Check then 
                assert IsUnimodular(r, p) where r is Result[#Result]; 
                assert IsUnimodular(r, p) where r is Result[#Result-1];
                theweight := func<L| x[1] where _,_,x is GenusSymbol(L, p)>;
                assert (theweight(L) eq weight) where L is Result[#Result];
                assert (theweight(L) eq weight) where L is Result[#Result-1];
              end if;
            end for;
          end if;

        if Check then 
          for n in [NN..#Result] do for k in  [1..n-1] do 
            if IsLocallyIsometric(Result[k], Result[n], p) then printf "[dim=%o in 3,4 (N=%o): %o/%o] ", m, NN, k, n; 
            printf "two generated lattices are locally isometric (this should not happen!)\n"; 
            printf "methods used to generate: %o/%o\n", Debug[k], Debug[n];
            assert false; 
            end if; 
          end for; end for;         
        end if;
          

        end for;  
      end for;
    end for;
  end if;
  
  if Check then printf "UnimodularLattices finished in Debug mode\n\n"; end if;  
  if Check then return Result, Debug; else return Result; end if;
end intrinsic;

intrinsic SquarefreeLattices(p::RngOrdIdl, m::RngIntElt: IncludeUnimodularLattices:=true, DetVal:= m) -> []
{Returns squarefree lattices of rank m over the completion of Order(p) at p. The lattices returned are pairwise non-isometric. If DetVal is set, then only lattices with a p^1 Jordan component of rank at most DetVal will be returned.}
  // construct primitive lattices in dimension m over the completion 
  // at p of a number field.
  
  UL := [];

  // generate (local) unimodular lattices:
  UL := AssociativeArray();
  for i in [1..m] do 
    UL[i] := [(a): a in UnimodularLattices(p, i: LowerDimension:=X, Check:=false)] where X is i gt 2 select UL[i-2] else []; 

  end for;
  
  // we continue working with the forms only, so we can DiagonalJoin easily:
  for i in [1..m] do UL[i] := [x`Form: x in UL[i]]; end for;
  
  // add a pseudo-lattice for dimension 0:
  UL[0] := [(MatrixRing(BaseRing(UL[1][1]), 0)!0)]; 
  
  printf "Generated %o local unimodular lattices.\n", [#UL[i]: i in [1..m]];
  Result := [];
  
  pi := PrimitiveElement(p);
  n := #RayClassGroup(p);
  
  // generate (local) squarefree lattices:
  thrown_out := 0;
  for dim1 in [(IncludeUnimodularLattices select 0 else 1)..DetVal] do 
    tocheck := 1; // #Result + 1; // only check those lattices for isometry where the p^0 and p^1 components' dimensions are the same 
    for M in UL[dim1] do
	  for L in UL[m-dim1] do
  //    printf "dimensions %o and %o\n", dim1, m-dim1;
        LL := LatticeModule(DiagonalJoin(L, pi*M)); 
        ok := exists(found){i: i in [tocheck..#Result]|IsLocallyIsometric(LL, Result[i], p: CheckIsometricSpaces:=true)};
	    if not ok then Append(~Result, LL); else thrown_out +:= 1; end if;
      end for;
	end for; 
  end for;
  return Result, thrown_out;
end intrinsic;

