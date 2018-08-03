/* 

Generate totally positive definite lattices over a given totally real number field.

Usage:

K := QuadraticField(3);
P2 := Factorization(2*Integers(K))[1][1];
P3 := Factorization(3*Integers(K))[1][1];
// you can specify the dimensions of the p^i valuated components for any number of prime ideals p
// in this example, a 6-dimensional component with scale P2^1, and a 4-dimensional component with scale P3^1.
LatticesWithGivenElementaryDivisors(K, 6, [<P2, [[1,6]]>,<P3,[[0,2],[1,4]]>]) ; // this generates 9 lattices

// if there is an error "degree is too large", call with UseAuto:=false, like this:
LatticesWithGivenElementaryDivisors(K, m, Dims: UseAuto:=false) 

*/

AttachSpec("lat.spec");
Attach("sigfield.m");


GetHasse:= func< D, p | &*[ MyHilbertSymbol( D[i], D[j], p ) : j in [1..i-1], i in [1..#D] ] >;

function Invariants(A)
  R:= Universe(A);
  if ISA(Type(R), Fld) then
    K:= R; R:= Integers(K); ChangeUniverse(~A, K);
  else
    K:= NumberField(R);
  end if;
  D:= R ! (&*A);
  F:= Factorization( (2*D)*R );
  return { PowerIdeal(R) | p[1] : p in F | GetHasse(A, p[1]) eq -1 };
end function;

// Convert the Witt invariant into the Hasse invariant.
function stdinv(K, m, det, Witt)
  if IsEmpty(Witt) then
    WP:= {}; Witt:= [];
  else 
    if Type(Witt) eq SetEnum then Witt:= Setseq(Witt); end if;
    if Type(Universe(Witt)) eq PowIdl then
      WP:= Witt; Witt:= [ <w, -1> : w in Witt ];
    else
      WP:= { w[1]: w in Witt };
    end if;
  end if;
  P:= Type(K) eq FldRat select PrimeDivisors(Integers() ! (2*det)) else [ p[1] : p in Factorization(2*det*Integers(K)) ];
  Witt cat:= [ < p, 1 >: p in P | p notin WP ];		// add back in the missing ones.

  C:= {};
  c:= case < m mod 8 | 0: det, 3: -det, 4: -det, 5: -1, 6: -1, 7: det, default : 1 >;
  for w in Witt do
    if w[2] ne MyHilbertSymbol(K ! -1, K ! c, w[1]) then Include(~C, w[1]); end if;
  end for;

  return C;  
end function;

function IdealsToGenerators(K, P)
  n:= #P;
  V:= VectorSpace(GF(2), n);
  if Type(K) eq FldRat then
    return [ &*[ Integers() | P[i] : i in [1..n] | v[i] ne 0 ] : v in V ];
  end if;

  L:= [];
  Cl, h:= NarrowClassGroup(K);
  trivial:= #Cl eq 1;
  for v in V do
    if IsZero(v) then x:= 1;
    else
      x:= &*[ P[i] : i in [1..n] | v[i] ne 0 ];
      if not trivial and not IsId(x @@ h) then continue; end if;
      ok, x:= IsPrincipal(x); assert ok;
    end if;
    ok, x:= MakeTotallyPositive(K ! x); assert ok;
    L cat:= x;
  end for;
  return L;
end function;

function ConstructSpace(K, n, d, Hasse)
  assert IsEven(#Hasse);

  rat:= Type(K) eq FldRat;
  R:= Integers(K);
  FD:= rat select PrimeDivisors(2*d) else [ f[1] : f in Factorization(2*d*R) ];
  P:= Sort(Setseq( Set(Hasse) join Set(FD) ));

  extra:= 0;
  while true do
    // get possible diagonal entries
    DP:= IdealsToGenerators(K, P);
    C:= CartesianProduct([ [1..#DP] ^^ (n-1) ]); // #C, "candidates";
    for c in C do
      if exists{i: i in [1..n-2] | c[i] gt c[i+1] } then continue; end if;
      A:= [ DP[x] : x in c ];
      Append(~A, (&*A) * d);
      Inv:= Invariants(A);
      if Inv eq Hasse then
        // reduce last entry.
        a:= A[n];
        Norm1:= [ d: d in DP | Norm(d) eq 1] ;
        if exists(x){x: x in Norm1 | IsSquare(a*x) } then
          a:= x;
        else
          while true do
            X:= [ d: d in DP | d notin Norm1 and IsIntegral(a/d^2) ];
            if IsEmpty(X) then break; end if;
            _, i:= Max([ Norm(x): x in X ]);
            a /:= X[i]^2;
          end while;
        end if;
        // now test again
        assert IsIntegral(a);
        A[n]:= a;
        Inv:= Invariants(A);
        assert IsSquare(K ! (&*A * d)) and Inv eq Hasse;
        return DiagonalMatrix(A);
      end if;
    end for;

    extra +:= 1;
    if extra gt 5 then
      error "Could not construct the space.";
    end if;
//    extra, "extra places needed";
    if rat then
      p:= 2; while p in P do p:= NextPrime(p); end while;
    else
      p:= 2;
      repeat ok:= exists(dp){d[1]: d in Decomposition(R, p) | d[1] notin P}; p:= NextPrime(p); until ok; p:= dp;
    end if;
    Append(~P, p);
  end while;
end function;

function RandomSubspace(V, m)

  W := sub< V| >;
  while Rank(W) ne m do    
    repeat v := Random(V); until not IsZero(v);
    W := sub<V| W, v>;
  end while;
  return W;
end function;

/*function IsSquarefreeLattice(L, p)
  // L any LatticeModule
   _,_,E := JordanDecomposition(L, p);
  return Set(E) subset {0, 1};
  // return (IsElementaryAbelian(Q)) and (Order(Q) mod Minimum(p) eq 0) where Q is QuoLat(Dual(L), L);
end function;*/

function MyFindLatticeFromGerstein(L, K, p)
//   KK := Gerstein(....) //  quadratfrei -> global konstruieren
  
return false; 
end function;

/*function MyFindLatticeSF(L, K, p)
printf "MyFindLatticeSF ...";
  assert Minimum(p) ne 2;
  
  g, pi := GenusSymbol(K, p);
  assert #g le 2 and {x[2]: x in g} subset {0,1};
 
  F, h := ResidueClassField(p);

  J,G,E := JordanDecomposition(L, p);
  assert SequenceToSet(E) subset {0,1};

  V := VectorSpace(F, Dimension(L));
  //  SI := [(g[i][2] - E[j]) div 2: i in I]; // i-ter Basisvektor muss mit pi^(g[i][2] - E[j]) div 2 mult. werden.  (Also die Grammatrix mit dem Quadrat davon.)
  GI := DiagonalJoin(<x: x in G>);

    i := 1;
    repeat
      W := RandomSubspace(V, g[i, 1]);
      B := BasisMatrix(W);
      B := ChangeRing(B, h^(-1));
      B:= ChangeRing(B, FieldOfFractions(BaseRing(L)));

      d := Determinant(B*GI*Transpose(B));
    until (Valuation(d, p) eq g[i][1]*g[i][2]) and (IsSquare(h(d/pi^(g[i][1]*g[i][2]))) eq (g[i,3] eq 1));
    J:= HorizontalJoin(<JJ: JJ in J>);
    M:= Module(L);
    LL:= LatticeModule( (Module( Rows( B*J )) + p*M) meet M, L`Form );
  assert IsLocallyIsometric(LL, K, p);
  return LL;
  
  
  

end function;*/


function MyFindLattices(L, Ls, p: UseAuto:=true)
  // L: a global, maximal integral lattice 
  // Ls: a list of local lattices (at the prime p), to be constructed as sublattices of L
  
  assert IsMaximalIntegral(L, p);
  
  
  
  e := Valuation(Order(p)!2, p);

  // filter for those lattices which lie in the same quadratic space as L:
   tmp := #Ls;
  Ls := [x: x in Ls | IsRationallyEquivalent(x, L, p)];

  
  printf "MyFindLattices: %o of the %o lattices given lie in the correct quadratic space.\n", #Ls, tmp; 
  // delete tmp;
  
  if #Ls eq 0 then return [], 0; end if; // the underlying quadratic space of L does not admit any of the Ls
  
  
  // build a forest of lattices, with each non-maximal lattice pointing to a lattice containing it.
  Forest := [* *]; 
  for S in Ls do
    K := S;
    k := -1;
    while true do
      ok, x := IsMaximalIntegral(K, p);
      // does this lattice already exist in the forest?
      ex := exists(t){t: t in [1..#Forest] | IsLocallyIsometric(Forest[t][1], K, p)};
      if ex then
        // append the previous lattice as a successor of this one:
        Append(~Forest[t][2], k);
        break;
      else
        Append(~Forest, [*/* lokales Gitter */ K, /* Nachfolgerindizes */ k eq -1 select [] else [k], /* IsMaximalIntegral */ ok, /* IsWanted */ K in Ls, /* Platzhalter für globales Gitter*/ false*]);
      end if;

      k := #Forest; // the index of K in Forest
      
      if ok then break; end if; // we have arrived at a maximal lattice

      // a superlattice:
      K:= LatticeModule(( Module(K) + Module([x])), K`Form ); 
      
    end while;
  end for;
  
   
  
  // find all the local lattices from the forest inside our given lattice L.
  // N.b. this is possible since the maximal lattices in V form a single genus.
  
  ForestRoots := [i: i in [1..#Forest] | Forest[i][3]];
  // set the global lattice of the forest's roots to L:
  for r in ForestRoots do Forest[r][5] := L; end for;
  
  // printf "Number of roots: %o\n", #ForestRoots; 
  assert &and[IsLocallyIsometric(Forest[i][1], L, p): i in ForestRoots];
  printf "The forest structure: %o\n", [<i, Forest[i][2]>: i in [1..#Forest]];

  k, h:= ResidueClassField(p); hinv:= h^-1;
  FF:= FieldOfFractions( BaseRing(L) );
  
  
  // printf "forest constructed."; 

  // e:= FF ! (Nonsquare(k) @@ h);
  //FFpi:= FF ! pi;
  
  V:= VectorSpace(k, Rank(L));

  generated := 0; tries := 0; 
  
  todo := [r: r in ForestRoots];
  todoindex := 1;
  
  while todoindex le #todo do
    r := todo[todoindex];
    // this local lattice must already have been constructed as a global lattice:
    assert not(false cmpeq Forest[r][5]); 
    printf "working on lattice at a prime over %o with scales %o\n", Minimum(p), &cat[Sprintf("(p^%o)^%o ", E[i], Nrows(G[i])): i in [1..#G]] where _,G,E is JordanDecomposition(Forest[r][5], p);
    
    
    K := Forest[r][1]; // the maximal integral (local) lattice, to which L is isometric at p

    
    // If p is even (and a few gigabytes of memory), we have a chance at using the automorphism groups.
    // If this crashes with "degree is too large", set UseAuto:=false ...
    if (Minimum(p) eq 2) and UseAuto then 
      printf "AutoOrbits for prime ideal over 2 ... ";
        Subm := MaximalSublattices(Forest[r][5], p: AutoOrbits:=true);
        for LL in Subm do
          ex := exists(i){i: i in [1..#Forest[r][2]]| IsLocallyIsometric(Forest[Forest[r][2][i]][1], LL, p) and (false cmpeq Forest[Forest[r][2][i]][5])};
          if ex then
            // mark this child as found:
            Forest[Forest[r][2][i]][5] := LL;
            generated +:= 1;
        
            // if Forest[Forest[r][2][i]][4] then printf "new lattice generated!\n"; end if;
            Append(~todo, Forest[r][2][i]);
          end if;
          
        end for;
      printf "done.\n";
    else

    // Generate random sublattices until all the descendants have been found:
    if Minimum(p) eq 2 then
      BM:= Matrix(LocalBasis(Module(Forest[r][5]), p : Type:= "Submodule"));
      // RankL0 := Nrows(G[1]) where _,G is JordanDecomposition(Forest[r][5], p); 
    else
      J, G := JordanDecomposition(Forest[r][5], p);
      RankL0 := Nrows(G[1]);
      BM := VerticalJoin(<j: j in J>);
    end if;

    J, G := JordanDecomposition(Forest[r][5], p);
    pM:= p*Module(Forest[r][5]);
    tries_old := tries;
    printf "Looking for: %o\n", [GenusSymbol(Forest[c][1], p): c in Forest[r][2]];
    while &or[Forest[c][5] cmpeq false: c in Forest[r][2]] do
      tries +:= 1;

      repeat 
        rand:= Random(V); 
        if Minimum(p) ne 2 then for i in [RankL0+1..Rank(L)] do rand[i] := 0; end for; end if;
      until not IsZero(rand);
      
      
      
      M:= KernelMatrix(Matrix(1, Eltseq(rand)));
      M:= ChangeRing(ChangeRing(M, hinv), FF);

      if Minimum(p) eq 2 then
        LL:= LatticeModule(Module(Rows(M * BM)) + pM, L`Form);
      else
        LL:= LatticeModule((Module(Rows(M * BM)) + pM) meet Module(Forest[r][5]), L`Form);
      end if;      
      // M, Valuation(Volume(LL), p);
      // have we found a yet unknown lattice?
      ex := exists(i){i: i in [1..#Forest[r][2]]| IsLocallyIsometric(Forest[Forest[r][2][i]][1], LL, p) and (false cmpeq Forest[Forest[r][2][i]][5])};
      if not ex then
        printf "%o\n", GenusSymbol(LL, p); 
      end if;

      if ex then
        // mark this child as found:
        Forest[Forest[r][2][i]][5] := LL;
        generated +:= 1;
        
        // if Forest[Forest[r][2][i]][4] then printf "new lattice generated!\n"; end if;
        Append(~todo, Forest[r][2][i]);
      end if;
    end while;
    printf " [%o tries]\n", tries-tries_old;
    end if;
    todoindex +:= 1;
  end while;
  // printf "%o lattices generated.\n", generated;
  
  // return the leaf lattices from the forest:
  assert &and[not(f[5] cmpeq false): f in Forest | f[4]];
  return [f[5]: f in Forest | f[4]], tries;
end function;



function LatticesWithGivenElementaryDivisors(K, m, DIMS: UseAuto:=true)
  // Computes one representative of each genus of totally positive definite lattices over a number field K with given constraints.
  // 
  // K: a totally real number field.
  // m: the dimension of L.
  // Dims: a list of [prime ideal p of Integers(K), list of [i, dimension of the p^i Jordan component]]
  // 
  
  Dims := DIMS; 
  
  error if not(Type(K) in [FldNum, FldQuad]), "K must be a NumberField.";
  error if not IsTotallyReal(K), "K must be totally real.";
  error if not (Type(Dims) eq SeqEnum), "Dims must be a sequence.";

  if Dims ne [] then
    error if not {m} eq {&+[Dims[i][2][j][2]: j in [1..#Dims[i][2]]]: i in [1..#Dims]}, Sprintf("incompatible arguments (dimensions do not add up to m=%o)", m);
    error if &or[#SequenceToSet(X) lt #X where X is [Dims[i][2][j][1]: j in [1..#Dims[i][2]]]: i in [1..#Dims]], "some p^i Jordan component was specified more than once";
    error if not &and[IsPrime(p): p in [* Dims[i][1]: i in [1..#Dims] *]], "incompatible arguments (not prime)";
    error if not &and[Order(p) eq Integers(K): p in [* Dims[i][1]: i in [1..#Dims] *]], "incompatible arguments (K and the prime ideals)";
    error if not &and[p in [Dims[i][1]: i in [1..#Dims]]: p in [y[1]: y in Factorization(2*Integers(K))]], "please specify the decompositions over (at least) all primes over 2.";
    error if not &and[&and[Dims[i][2][j][1] ge 0: j in [1..#Dims[i][2]]]: i in [1..#Dims]], "the lattice must be integral, negative scales are not allowed!";
    error if not &and[&and[Dims[i][2][j][2] gt 0: j in [1..#Dims[i][2]]]: i in [1..#Dims]], "only components with dimension > 0 may be specified!";
  end if;

  Result:= [];
  

    /*if #Dims eq 0 then
      printf "Looking for unimodular lattices.\n\n", K;
      // clumsy but works: insert a trivial Jordan component for any prime ideal, and the unimodular lattices will be found
      Dims :=  [<p, [[0,m]]>] where p is Factorization(3*Integers(K))[1][1];
    end if;*/
      
    // the primes to look at:    
    P:= [p: p in [Dims[i][1]: i in [1..#Dims]]];

    printf "Base field is: %o\nWorking with %o prime ideals dividing the following integers: %o\n\n", K, #P, [Minimum(a): a in P];

    LocalL := AssociativeArray();  // for caching local lattices
    
          printf "constructing local lattices ... ";
         
          for i in [1..#P] do
            UnimodularDimensions := [Dims[i][2][k][2]: k in [1..#Dims[i][2]]];
            Sort(~UnimodularDimensions);
            // we need to generate local unimodular lattices of the dimensions specified in UnimodularDimensions:
            
            if not(P[i] in Keys(LocalL)) then LocalL[P[i]] := AssociativeArray(); end if;
            
            for ud in [1..#UnimodularDimensions] do
              j := UnimodularDimensions[ud];
              if not(j in Keys(LocalL[P[i]])) then 
                printf "prime %o/%o, dimension %o/%o ...\n", i, #P, ud, #UnimodularDimensions;
                LocalL[P[i]][j] := UnimodularLattices(P[i], j: LowerDimension:=j-2 in UnimodularDimensions select LocalL[P[i]][j-2] else []); 
              end if;
            end for;
          end for;
          
          // generate local candidates with the correct Jordan decomposition:
          printf "glueing local lattices together ...\n";
          LocalCandidates := AssociativeArray();
          for i in [1..#P] do
            p := P[i];
            LocalCandidates[p] := [];
            pi := UniformizingElement(p);
            for c in CartesianProduct([[1..#LocalL[p][Dims[i][2][j][2]]]: j in [1..#Dims[i][2]]]) do
              L := LatticeModule(MatrixRing(Integers(K), 0)!0);
              for j in [1..#c] do
                L := DirectSum(L, Rescale(LocalL[p][Dims[i][2][j][2]][c[j]], pi^Dims[i][2][j][1]));
              end for;
              // Do not generate isometric local lattices:
              if not &or[IsLocallyIsometric(l,L,p): l in LocalCandidates[p]] then
                Append(~LocalCandidates[p], L);
              end if;
            end for;
          end for;
          
          printf "\n\nFound %o local candidate lattices at primes over %o.\n", [#LocalCandidates[x]: x in Keys(LocalCandidates)], [Minimum(p): p in P];
          
          
  
    n:= Degree(K);
    R:= Integers(K);
    dK:= Discriminant(R);

    
    // the determinant ideal corresponding to the given constraints:
    DetIdeals := { [ &+[Dims[i][2][j][1]*Dims[i][2][j][2]: j in [1..#Dims[i][2]]] mod 2: i in [1..#Dims]] };
        
    // printf "Calculated %o possible quadratic space determinant ideals (= lattice discriminant valuations mod 2).\n", #DetIdeals;
    
    Cl, h:= ClassGroup(K);
    U:= PowerIdeal(R);

    
    // We browse through the list of possible determinant ideals 
    // by grouping those determinant ideals together which lie in the same enveloping spaces.
    // First, loop through the determinant in DetIdeals (these have been taken mod 2):
    DICount:= 0;
    for DI in DetIdeals do
    
    
      DICount +:= 1;
      
      // pick the even-valuated primes:
      DiscPrimes:= [ U | P[i]: i in [1..#P] | DI[i] ne 0 ];
      det:= &* DiscPrimes;
      
      // generators for the vector space discriminant of the enveloping space:
      // det*(some square in the class group) might have
      // a totally positive generator, and since det matters only mod squares, we have to check
      // for every square c in the class group if det*c has a totally positive generator.
      dets:= [];
      for c in 2*Cl do // 2*Cl = the squares in the class group
        ok, x:= HasTotallyPositiveGenerator(det * (c @ h));
        if ok then dets cat:= x; end if;
      end for;
      if IsEmpty(dets) then continue; end if;
      
      // Get possible Witt invariants:
      // Go through all combinations of places with Witt invariant c_p = -1:
      // (this could be optimized by leaving out some invalid combinations ...)
      V:= VectorSpace(GF(2), #P);
      Witt:= [ {U | P[i] : i in [1..#P] | v[i] eq 1} : v in V ];
      
//      printf "#Witt = %o, #dets = %o\n", #Witt, #dets; 

      // Now get all possible spaces and a maximal integral lattice L in each space.
      // Then we compute reps. of the primitive genera below L that have the correct determinants.
      //
      // dets: all totally positive generators of (subsets of) the current determinant ideal
      
      for didx in [1..#dets] do
        // printf "working on vector space discriminant %o/%o\n", didx, #dets;
        d:= dets[didx];
        
        // convert the Witt invariant to the Hasse invariant:
        Hasse:= [ <W, stdinv(K, m, d, W)>: W in Witt ]; 

        // There must be an even number of places with Hasse invariant -1, cf. (O'Meara, §72.1)
        Hasse:= [ h: h in Hasse | IsEven(#h[2]) ];

        
        for Hidx in [1..#Hasse] do
          printf "Dets: %o/%o, Hasse-Inv: %o/%o, #Result=%o \n", didx, #dets, Hidx, #Hasse, #Result;

          // construct a K-space of rank m with the given invariants, and a maximal integral lattice in that space:
          F:= ConstructSpace(K, m, d, Hasse[Hidx][2]);
          L:= MaximalIntegralLattice(F);
          
         // try to find the local candidates inside this quadratic space:
         GlobalCandidates := AssociativeArray();
         for i in [1..#P] do
            GlobalCandidates[P[i]] := MyFindLattices(L, LocalCandidates[P[i]], P[i]: UseAuto:=UseAuto); 
         end for;
         
         // intersect in all possible ways:
         CC := CartesianProduct([[1..#GlobalCandidates[p]]: p in P]);
         for c in CC do
           L := &meet[GlobalCandidates[P[i]][c[i]]: i in [1..#c]];
           // printf "found a lattice, Jordan decompositions are:\n %o\n\n", [<Minimum(p), E where _,_,E is JordanDecomposition(L, p)>: p in P];
           Append(~Result, L);
         end for;


        end for; // Hidx (current Hasse invariant)
      end for; // didx (current quadratic space discriminant)
    end for; // DI (current determinant ideal for target lattice)
  printf "We have generated %o lattices\n", #Result;
  return Result;
end function;
