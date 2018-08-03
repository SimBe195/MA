declare type LatModHerm : LatMod;
//declare type LatModHermElt : LatModElt;
declare type LatModHerm[LatModElt];

declare attributes LatModHerm:
  Form,
  Module,
//  aut,
//  FixedField,
  Discriminant,
  Norm,
  Scale,
  Definite,
//  Orthogonal,
  Diagonal,
  GenusSymbols,
  Auto;

//declare attributes LatModEltHerm: Parent, Element;

intrinsic PrimitiveElement(I::RngInt) -> RngIntElt
   {A generator of I}
   return Generator(I);
end intrinsic;

intrinsic IsLocalNorm(E::FldAlg, a::RngElt, p::RngOrdIdl) -> BoolElt
{Tests if a is a norm in the completion of p}
  require Degree(E) eq 2: "The first argument must be a field of degree 2";
  K:= BaseField(E);
  ok, a:= IsCoercible(K, a);
  require ok and IsPrime(p) and Order(p) eq Integers(K): "Incompatible arguments";
  x:= PrimitiveElement(E);
  return MyHilbertSymbol(a, K ! ((2*x - Trace(x))^2), p) eq 1;
end intrinsic;

intrinsic IsLocalNorm(E::FldAlg, a::RngElt, p::RngIntElt) -> BoolElt
{"}//"
  require Degree(E) eq 2 and Type(BaseField(E)) eq FldRat: "The first argument must be a field of degree 2 over the rationals";
  ok, a:= IsCoercible(Rationals(), a);
  require ok and IsPrime(p): "Incompatible arguments";
  x:= PrimitiveElement(E);
  return HilbertSymbol(a, Rationals() ! ((2*x - Trace(x))^2), p) eq 1;
end intrinsic;

function NormicDefect(E, a, p)
  R:= Integers(E);
  if IsZero(a) or IsLocalNorm(E, a, p) then return Infinity(); end if;
  return Valuation(a, p) + Valuation(Discriminant(R), p) - 1;
end function;

function GetPrimeAbove(L, p)
  R:= BaseRing(L);
  if Type(p) eq RngIntElt or Order(p) cmpne R then
    return Decomposition(R, p)[1,1];
  end if;
  return p;
end function;

function GetPrimeBelow(L, p)
  R:= BaseRing(L);
  if Type(p) eq RngIntElt or Order(p) cmpne R then
    return p;
  end if;
  S:= BaseRing(L);
  return Type(S) eq RngInt select Minimum(p) else p meet S;
end function;


/* Constructors */

TestHerm:= func< F, a | F eq Transpose(Matrix(Ncols(F), [ a(x): x in Eltseq(F) ])) >;

intrinsic HermitianLattice(M::ModDed, F::Mtrx) -> LatModHerm
{The lattice consisting of the module M and the hermitian form F}
  R:= BaseRing(M);
  require Degree(R) eq 2 : "The base ring must be an extension of degree 2";
  require ISA(Type(R), RngOrd) : "The base ring must be an order in a number field";
  require Ncols(F) eq Dimension(M) : "The arguments must have the same dimensions";
  FF:= FieldOfFractions(R);
  ok, F:= CanChangeRing(F, FF);
  require ok: "The first two arguments must have the same base ring";
  a:= Automorphisms(FF)[2];
  require TestHerm(F, a): "The form must be hermitian";

  L:= New(LatModHerm);
  L`Module:= M;
  L`Form:= F;
//  L`Orthogonal:= false;
//  L`aut:= a;
  return L;
end intrinsic;

intrinsic HermitianLattice(B::Mtrx, F::Mtrx) -> LatModHerm
{The hermitian standard lattice with basis B and form F}
  require Ncols(B) eq Ncols(F) : "The arguments must have the same dimensions";
  R:= BaseRing(F);
  T:= Type(R);
  if ISA(T, FldNum) then
    R:= FieldOfFractions(Integers(R));
    F:= ChangeRing(F, R);
  elif ISA(T, RngOrd) then
    R:= FieldOfFractions(R);
    F:= ChangeRing(F, R);
  else
    require ISA(T, RngOrd) or ISA(T, FldOrd): "Wrong base ring";
  end if;
  ok, B:= CanChangeRing(B, R);
  require ok : "Incompatible base rings";
  return HermitianLattice(Module(Rows(B)), F);
end intrinsic;

function IsHermitian(F)
  K:= BaseRing(F);
  if ISA(Type(K), RngOrd) then K:= NumberField(K); end if;
  if not ISA(Type(K), FldAlg) or Degree(K) ne 2 then
    return false, "The base field of the form must be a quadratic extension";
  end if;
  if not TestHerm(F, Automorphisms(K)[2]) then return false, "The matrix is not hermitian"; end if;
  return true, _;
end function;

intrinsic HermitianLattice(F::Mtrx) -> LatModHerm
{The hermitian standard lattice with form F}
  ok, str:= IsHermitian(F);
  require ok: str;
  return HermitianLattice(F^0, F);
end intrinsic;

forward MyLocalBasis;
function IMI(L, p)
  R:= BaseRing(L);
  FF:= FieldOfFractions(R);
  D:= Decomposition(R, p);
  pi:= #D eq 0 select PrimitiveElement(D[1,1]) else WeakApproximation(D, [1,0]);

  B:= MyLocalBasis(L, p : Type:= Submodule);
  M:= Matrix(B);
  G:= M * L`Form * InternalConjugate(L, M);
  k, h:= ResidueClassField(D[1,1]);
  V:= KernelMatrix(Matrix(Ncols(G), [x @ h: x in Eltseq(G)]));
  if Nrows(V) eq 0 then return true, _; end if;

  val2:= Valuation(Discriminant(R), p);
  PP:= ProjectiveLineProcess(k, Nrows(V));
  x:= Next(PP);
  while not IsZero(x) do
    e:= Eltseq(x * V) @@ h;
    v:= Vector(FF, e);
    valv:= Valuation( ((v*G) * Matrix(FF,1,e))[1], p );
    assert valv ge 1;
    // TODO: Better code depending on whether -1 is a square or not and then take (1,p) or (p,p)
    if valv ge val2+2 then return false, pi*v*M; end if;
    x:= Next(PP);
  end while;
  return true, _;
end function;

function MHL(L)
  assert IsIntegral(Norm(L));
  R:= BaseRing(L);
  FF:= Factorization(Norm(Volume(L)) * Discriminant(R));
  for f in FF do
    repeat
      ok, x:= IMI(L, f[1]);
      L:= LatticeModule( L`Module + R*x, L`Form );
    until ok;
  end for;
  return L;
end function;

intrinsic MaximalHermitianLattice(L::LatModHerm) -> LatModHerm
{A maximal integral lattice over L}
  require IsIntegral(Norm(L)) : "The lattice is not integral";
  return MHL(L);
end intrinsic;

intrinsic MaximalHermitianLattice(F::Mtrx) -> LatModHerm
{A maximal integral lattice with hermitian form F}
  ok, str:= IsHermitian(F);
  require ok: str;
  L:= HermitianLattice(F);
  FF:= Factorization(Scale(L));
  s:= 1;
  while #FF ne 0 do
    ok:= exists(i){i:i in [2..#FF] | Norm(FF[i,1]) eq nrm } where nrm:= Norm(FF[1]);
    if ok then
      assert FF[i,2] eq FF[1,2];
      s *:= FF[1,1]^FF[1,2];
      Remove(~FF, i);
    else
      s *:= FF[1,1]^-(FF[1,2] div 2);
    end if;
    Remove(~FF, 1);
  end while;
  if not IsOne(s) then L:= s*L; end if;
  return MHL(L);
end intrinsic;

/* Basic functions */

intrinsic IsDefinite(L::LatModHerm) -> BoolElt
{Tests if the lattice L is (totally) definite}
  if not assigned L`Definite then
    E:= NumberField(BaseRing(L));
    K:= BaseField(E);
    if not IsTotallyReal(K) or not IsTotallyComplex(E) then
      L`Definite:= false;
    else
      F:= L`Form;
      n:= Ncols(F);
      L`Definite:= true;
      for i in [1..n] do
        if not IsTotallyPositive( K ! F[i,i] ) then L`Definite:= false; break; end if;
        T:= MatrixRing(BaseRing(F), n) ! 1;
        for j in [i+1..n] do
          T[j,i]:= -F[j,i]/F[i,i];
        end for;
        F:= T * F * InternalConjugate(L, T);
      end for;
      assert IsDiagonal(F);
    end if;
  end if;
  return L`Definite;
end intrinsic;

intrinsic Discriminant(L::LatModHerm) -> RngOrdFracIdl
{The discriminant ideal of L}
  if not assigned L`Discriminant then
    P:= PseudoBasis(L`Module);
    T:= Matrix( [ p[2] : p in P ] );
    K:= FixedField(L);
    L`Discriminant:= (K ! Determinant(L`Form)) * Norm(&*[ p[1]: p in P ] * Determinant(T));
  end if;
  return L`Discriminant;
end intrinsic;

intrinsic IsRationallyEquivalent(L1::LatModHerm, L2::LatModHerm, p::RngOrdIdl) -> BoolElt
{Tests if L1 and L2 are equivalent over the completion of their base field at p}
  // In most cases, we have lattices in the same space anyway...
  if L1`Form cmpeq L2`Form then return true; end if;
  R:= BaseRing(L1);
  require R cmpeq BaseRing(L2): "Incompatible lattices";
  require Order(p) cmpeq BaseRing(R) and IsPrime(p):
    "The third argument must be a prime ideal of the base ring of the lattices";
  return Degree(L1) eq Degree(L2) and IsLocalNorm( NumberField(R),  Determinant(L1`Form) * Determinant(L2`Form), p );
end intrinsic;

intrinsic IsRationallyEquivalent(L1::LatModHerm, L2::LatModHerm, p::RngIntElt) -> BoolElt
{"} //"
  if L1`Form cmpeq L2`Form then return true; end if;
  R:= BaseRing(L1);
  require R cmpeq BaseRing(L2): "Incompatible lattices";
  require Type(BaseRing(R)) eq RngInt and IsPrime(p):
    "The third argument must be a prime ideal of the base ring of the lattices";
  return Degree(L1) eq Degree(L2) and IsLocalNorm( NumberField(R),  Determinant(L1`Form) * Determinant(L2`Form), p );
end intrinsic;

intrinsic IsRationallyEquivalent(L1::LatModHerm, L2::LatModHerm) -> BoolElt
{Tests if L1 and L2 are equivalent over their base field}
  if L1`Form cmpeq L2`Form then return true; end if;
  require BaseRing(L1) cmpeq BaseRing(L2): "Incompatible lattices";

  K:= FixedField(L1);
  E:= NumberField(BaseRing(L1));
  return Degree(L1) eq Degree(L2) and NormEquation(E, K ! (Determinant(L1`Form) * Determinant(L2`Form)) );
end intrinsic;

rat_gens:= function(S)
  if Type(Universe(S)) eq RngInt then
    return GCD(S);
  end if;
  d:= LCM({ Denominator(x) : x in S });
  return GCD({Integers() | x*d: x in S })/d;
end function;

ideal_gens:= function(I)
  O:= Order(I);
  if IsAbsoluteOrder(O) then return Basis(I); end if;
  F:= FieldOfFractions(O);
  G:= Generators(Module(I));
  G:= [ F | Eltseq(g) : g in G ];
  assert I eq ideal< O | G >;
  return G;
end function;

ideal_trace:= function(I)
  Gens:= [ Trace(g) : g in ideal_gens(I) ];
  R:= Order(I);
  return IsAbsoluteOrder(R) select rat_gens(Gens) else ideal< R | Gens >;
end function;

// Get a local unit at P such that T(u)=1.
SpecialUnit:= function(P)
  R:= Order(P);
  E:= NumberField(R);
  assert Degree(E) eq 2;
  K:= BaseField(E);
  p:= P meet Integers(K);
  if Type(p) eq RngInt then p:= Generator(p); end if;
  x:= PrimitiveElement(E);
  x:= x - Trace(x/2);
  a:= K ! (x^2);
  v:= Valuation(a, p);
  if v ne 0 then
    pi:= PrimitiveElement(P);
    x/:= pi^v;
  end if;
  u:= (1+x)/2;
  assert Valuation(u, P) eq 0;
  assert Trace(u) eq 1;
  return u;
end function;

intrinsic Scale(L::LatModHerm) -> RngOrdFracIdl
{The scale of the lattice L}
  if not assigned L`Scale then
    P:= PseudoBasis(Module(L));
    B:= Matrix( [ p[2] : p in P ] );
    F:= B * L`Form * InternalConjugate(L, B);
    a:= Involution(L);
    L`Scale:= &+{ F[i,j] * P[i,1] * a(P[j,1]) : i, j in [1..#P] | F[i,j] ne 0 };
    assert L`Scale eq a(L`Scale);
  end if;
  return L`Scale;
end intrinsic;

intrinsic Norm(L::LatModHerm) -> RngOrdFracIdl
{The norm of the lattice L}
  if not assigned L`Norm then
    P:= PseudoBasis(Module(L));
    B:= Matrix( [ p[2] : p in P ] );
    F:= B * L`Form * InternalConjugate(L, B);
    Gens:= { F[i,i] * Norm(P[i,1]) : i in [1..#P] | F[i,i] ne 0 } join { ideal_trace(P[i,1] * F[i,j] * P[j,1]) : i in [1..j-1], j in [1..#P] | F[i,j] ne 0 };
    L`Norm:= IsAbsoluteOrder(BaseRing(L)) select rat_gens(Gens) else &+Gens;
  end if;
  return L`Norm;
end intrinsic;

// A free submodule of Module(L), coinciding at p with L.
function MyLocalBasis(L, p: Type:= "")
  R:= BaseRing(L);
  if Order(p) cmpeq R then
    S:= IsSplit(p) select [ p, Involution(L)(p) ] else [p];
  else
    S:= [p[1]: p in Decomposition(R, p)];
  end if;
  B:= [];
  for pp in PseudoBasis(Module(L)) do
    g:= Generators(pp[1]);
    if #g eq 1 then x:= g[1];
    elif Type eq "" then x:= WeakApproximation(S, [ Valuation(pp[1], P) : P in S ]);
    else
      Fact:= Factorization(pp[1]);
      Fact:= Type eq "Submodule" select [ f: f in Fact | f[1] in S or f[2] gt 0 ]
                                   else [ f: f in Fact | f[1] in S or f[2] lt 0 ];
      for p in S do
        if forall{ f: f in Fact | f[1] ne p } then Append(~Fact, <p, 0>); end if;
      end for;
      x:= WeakApproximation([ f[1] : f in Fact ], [ f[2] : f in Fact ]);
    end if;
    Append(~B, pp[2]*x);
  end for;
  return B;
end function;


function JordanSplitting(L, p)
  R:= BaseRing(L);
  K:= FixedField(L);
  aut:= Involution(L);
  even:= Minimum(p) eq 2;

  D:= Decomposition(R, p);
  split:= #D eq 2;
  ram:= D[1,2] eq 2;
  D:= [ d[1]: d in D ];
  P:= PseudoBasis(Module(L));
  S:= Matrix([ x[2] * WeakApproximation( D, [ Valuation(x[1], d) : d in D ] ) : x in P ]);
  n:= #P;

  if split then
    pi:= WeakApproximation(D, [1,0]);
  else
    pi:= PrimitiveElement(D[1]);
    if not ram then 
      su:= even select SpecialUnit(D[1]) else 1;
    end if;
  end if;
  P:= D[1];

  oldval:= Infinity();
  Blocks:= []; Exponents:= [];

  F:= L`Form;
  k:= 1;
  while k lt n do
    G:= S * F * InternalConjugate(L, S);
    X:= [ Valuation(G[i,i], P): i in [k..n] ];

    m, ii:= Minimum( X ); ii +:= k-1;
    pair:= <ii, ii>;
    for i,j in [k..n] do
      tmp:= Valuation(G[i,j], P);
      if tmp lt m then m:= tmp; pair:= <i,j>; end if;
    end for;
    if m ne oldval then Append(~Blocks, k); oldval:= m; Append(~Exponents, m); end if;
    i,j:= Explode(pair);

    if (i ne j) and not (ram and even) then
      a:= G[i,j];
      if split then
        lambda:= Valuation( pi*a, P ) eq m select pi else aut(pi);
      elif ram then
        assert IsEven(m);
        lambda:= Norm(pi)^(m div 2) / a; 
      else
        lambda:= Norm(pi)^m / a * su;
      end if;
      S[i] +:= aut(lambda) * S[j];
      G:= S * F * InternalConjugate(L, S);
      j:= i;
    end if;

    if i ne j then
      assert i lt j;
      SwapRows(~S, i, k);
      SwapRows(~S, j, k+1);
      SF:= S*F;
      X1:= Eltseq(SF * InternalConjugate(L, S[k  ]));
      X2:= Eltseq(SF * InternalConjugate(L, S[k+1]));
      for l in [k+2..n] do
        den:= Norm(X2[k])-X1[k]*X2[k+1];
        S[l] -:= (X2[l]*X1[k+1]-X1[l]*X2[k+1])/den*S[k] + (X1[l]*X2[k] -X2[l]*X1[k])/den*S[k+1];
      end for;
      k+:= 2;
    else
      SwapRows(~S, i, k);
      X:= Eltseq(S * F * InternalConjugate(L, S[k]));
      for l in [k+1..n] do S[l] -:= X[l]/X[k] * S[k]; end for;
      k+:= 1;
    end if;
  end while;

  G:= S * F * InternalConjugate(L, S);
  assert (even and ram) or IsDiagonal(G);

  Append(~Blocks, n+1);
  Matrices:= [* RowSubmatrix(S, Blocks[i], Blocks[i+1] - Blocks[i]) : i in [1..#Blocks-1] *];
  return Matrices, [* m*F*InternalConjugate(L, m): m in Matrices *], Exponents;
end function;

function TraceIdeal(L, p)
  R:= Order(p);
  v:= Valuation(Different(R), p);
  X:= [ 2*((l+v) div 2) : l in L ];
  return Min(X);
end function;

function GetNorm(G, P)
  n:= Ncols(G);
  Elts:= Append([ Valuation(G[i,i], P) : i in [1..n] ] , TraceIdeal([ G[i,j]: j in [i+1..n], i in [1..n] ], P));
  return Min( Elts );
end function;

function GS(L, p)
  if not assigned L`GenusSymbols then
    L`GenusSymbols:= AssociativeArray();
  end if;
  ok, sym:= IsDefined(L`GenusSymbols, p);
  if ok then return sym; end if; 

  B, G, S:= JordanSplitting(L, p);
  R:= BaseRing(L);
  E:= NumberField(R);
  K:= BaseField(E);
  bad:= Minimum(p) eq 2 and IsRamified(p, R);
  if not bad then
    sym:= [ < Nrows(B[i]), S[i], IsLocalNorm(E, K ! Determinant(G[i]), p) > : i in [1..#B] ];
  else
    P:= Decomposition(R, p)[1,1];
    pp:= PrimitiveElement(P);
    sym:= [];
    for i in [1..#B] do
      normal:= GetNorm(G[i], P) eq S[i];
      v:= GetNorm(DiagonalJoin(< pp^Max(0, S[i]-S[j]) * G[j] : j in [1..#B] >), P);
      s:= < Nrows(B[i]), S[i], normal, v, K ! Determinant( DiagonalJoin(< G[j] : j in [1..i]>) ) >;
      Append(~sym, s);
    end for;
  end if;
// TODO: Enable cache
//  L`GenusSymbols[p]:= sym;
  return sym;
end function;

intrinsic GenusSymbol(L::LatModHerm, p::RngOrdIdl) -> []
{The genus symbol of L at p}
  require IsPrime(p) and Order(p) cmpeq Integers(FixedField(L)) : "Incompatible arguments";
  return GS(L, p);
end intrinsic;

intrinsic GenusSymbol(L::LatModHerm, p::RngIntElt) -> []
{"} //"
  require IsPrime(p) and Type(FixedField(L)) eq FldRat : "Incompatible arguments";
  return GS(L, p);
end intrinsic;

function IsLocIso(L1, L2, p)
  R:= BaseRing(L1);
  E:= NumberField(R);
  S1:= GenusSymbol(L1, p);
  S2:= GenusSymbol(L2, p);
  if Minimum(p) ne 2 or not IsRamified(p, R) then 
    return S1 eq S2;
  end if;
  t:= #S1;
  // number of blocks:
  if t ne #S2 then return false; end if;
  // test ranks, scales , normal property and fundamental norm ideals
  if exists{<i, k>: i in [1..t], k in [1..4] | S1[i,k] ne S2[i,k] } then return false; end if;
  // Test if spaces are equivalent, i.e. Det matches
  if not IsLocalNorm(NumberField(R), S1[t,5] / S2[t,5], p) then return false; end if;
  for i in [1..t-1] do
    assert Valuation(S1[i,5], p) eq Valuation(S2[i,5], p);
    x:= (S1[i,5] / S2[i,5]);
    n:= 2*NormicDefect(E, x, p);
    if n lt (S1[i, 4] + S1[i+1, 4]) - 2*S1[i, 2] then return false; end if;
  end for;
  return true;
end function;

intrinsic IsLocallyIsometric(L1::LatModHerm, L2::LatModHerm, p::RngOrdIdl) -> BoolElt
{Returns true if and only if the p-adic completions of L1 and L2 are isometric}
  require BaseRing(L1) eq BaseRing(L2): "Incompatible lattices";
  require IsPrime(p) and Order(p) cmpeq Integers(FixedField(L1)) : "Incompatible arguments";
  return IsLocIso(L1,L2,p);
end intrinsic;

intrinsic IsLocallyIsometric(L1::LatModHerm, L2::LatModHerm, p::RngIntElt) -> BoolElt
{"}//"
  require BaseRing(L1) eq BaseRing(L2): "Incompatible lattices";
  require IsPrime(p) and Type(FixedField(L1)) eq FldRat : "Incompatible arguments";
  return IsLocIso(L1,L2,p);
end intrinsic;

// L=lattice, P=prime, C=Inv(P), B=local basis at P \cap C, G=Gem(B) mod C,
// split=(P ne C), x=global vector, h=epi mod C.
function Neighbour(L, B, xG, x, h, P, C, split)
  R:= Order(P);
  n:= #B;
  if C cmpeq 0 then 
    C:= split select Involution(L)(P) else P;
  end if;
  I:= [ i: i in [1..n] | xG[i] ne 0 ];
  assert #I ne 0;
  i:= I[1];
  Gens:= [ < 1*R, B[j] > : j in {1..n} diff Set(I) ] cat [ < 1*R, B[j] - (xG[j]/xG[i]) @@ h * B[i] > : j in I | j ne i ] cat [ < P, B[i] >, < C^-1, x > ];
  M:= Module(Gens) + (split select P*C else P)*L`Module;
  LL:= HermitianLattice(M, L`Form);

  //test
  p:= Type(S) eq RngInt select Minimum(P) else P meet S where S:= BaseRing(R);
  assert IsLocallyIsometric(L, LL, p);

  return LL;
end function;

function Neighbours(L, P: AutoOrbits:= true, Max:= Infinity())
  R:= BaseRing(L);
  F:= FieldOfFractions(R);
  C:= Involution(L)(P);
  B:= MyLocalBasis(L, P: Type:= "Submodule");
  T:= Matrix(B);
  k, h:= ResidueClassField(C);
  n:= Rank(L);
  G:= Matrix(k, n, [ h(e) : e in Eltseq(T * L`Form * InternalConjugate(L, T)) ]);
  W:= VectorSpace(k, n);
  if AutoOrbits cmpne false then
    A:= AutoOrbits cmpeq true select AutomorphismGroup(L) else ChangeRing(AutoOrbits, F);
    A:= [ Matrix(n, [ x @ h : x in Eltseq(T * A.i * TI) ]) : i in [1..Ngens(A)] ] where TI:= T^-1;
    // If A mod p is a scalar group, we should ignore it
    AutoOrbits:= exists{g: g in A | not IsScalar(g)};
  end if;
  if AutoOrbits then
    A:= sub< GL(n, k) | A >;
    LO:= IsPrimeField(k) select [ l[2].1: l in OrbitsOfSpaces(A, 1) ] else [ l[1].1: l in LineOrbits(A) ];
  else
    LO:= ProjectiveLineProcess(W);
  end if;

  Result:= [];
//  keep:= true; cont:= true; found:= false;
  if P ne C then
    pi:= WeakApproximation([P, C], [1,0]);
    pih:= h(pi);
    for i in [1..Min(#LO, Max)] do
      w:= AutoOrbits select W ! LO[i] else Next(LO);
      x:= &+[ B[i] * (w[i] @@ h): i in [1..n] | w[i] ne 0 ];
      LL:= Neighbour(L, B, pih * w * G, pi * x, h, P, C, true); 
      Append(~Result, LL);
    end for;
  else
    ram:= IsRamified(P);
    if ram then
      pi:= PrimitiveElement(P);
      S:= [x @@ h : x in k];
    else
      p:= P meet BaseRing(R);
      pi:= PrimitiveElement(p);
      kp, hp:= ResidueClassField(p);
      alpha:= k.1 @@ h;
      // k/kp has basis [1,alpha] and T is the relative trace:
      T:= Matrix(kp, 1, [2, Trace(alpha) @ hp ]);
    end if;
    for i in [1..#LO] do
      w:= AutoOrbits select W ! LO[i] else Next(LO);
      x:= &+[ B[i] * (w[i] @@ h) : i in [1..n] | w[i] ne 0 ];
      nrm:= Norm(L ! x);
      if nrm notin P then continue; end if;
      wG:= w*G;
      ok:= exists(j){j: j in [1..n] | wG[j] ne 0};
      assert ok;
      NL:= [];
      if not ram then
        s, V:= Solution(T, Vector(kp, [hp(-nrm/pi)]));
        l:= Involution(L)((1/wG[j]) @@ h);
        S:= [ l*( x[1] @@ h + (x[2] @@ h)*alpha ) where x:= s+v : v in V ];
      end if;
      for s in S do
        Append(~Result, Neighbour(L, B, wG, x+pi*s*B[j], h, P, P, false));
        if #Result ge Max then break i; end if;
      end for;
    end for;
  end if;
  return Result;
end function;

intrinsic IteratedNeighbours(L::LatModHerm, P::RngOrdIdl: AutoOrbits:= true, CallBack:= false) -> []
{The iterated P-neighbours of L}
  require Order(P) eq BaseRing(L): "Arguments are incompatible";
  require IsPrime(P): "Second argument must be prime";
  require not IsRamified(P) or Minimum(P) ne 2: "Second argument cannot be a ramified prime over 2";
  require Rank(L) ge 2: "The rank of the lattice must be at least 2";
  require IsDefinite(L): "The lattice must be definite";
  require IsIsotropic(L, P) : "The lattice must be locally isotropic";

  Result:= [ L ];
  i:= 1;
  while i le #Result do
    N:= Neighbours(Result[i], P: AutoOrbits:= AutoOrbits);
    for X in N do
      if forall{Y: Y in Result | not IsIsometric(X, Y) } then Append(~Result, X); end if;
    end for;
    i+:= 1;
  end while;

  return Result;
end intrinsic;

intrinsic GenusRepresentatives(L::LatModHerm : Max:= Infinity()) -> []
{Returns a system of representatives of the isometry classes in the genus of L}
  require Rank(L) ge 2 : "The rank of the lattice must be at least 2";

  R:= BaseRing(L);
  S:= BaseRing(R);
  p:= 1; P:= 1;
  repeat
    p:= NextPrime(p);
    for d in Decomposition(R, p) do
      x:= d[1];
      if (( IsRamified(x) and Minimum(x) ne 2 ) or IsInert(x)) and IsIsotropic(L, x) then
        P:= x;
        break;
      end if; 
    end for;
  until not IsOne(P);
  //TODO:: There might be a smaller P ...

  // Get generators needed to combine special genera
  CR, hR:= ClassGroup(R);
  GensC:= { f[1] @@ hR : f in Factorization(Discriminant(R)*R) };
  if Type(S) ne RngInt then
    CS, hS:= ClassGroup(S);
    GensC join:= { ((c @ hS)*R) @@ hR : c in CS };
  end if;
  C0:= sub< CR | GensC >;
  // The generators from the class group
  Gens:= [];
  p:= 1;
  while #C0 ne #CR do
    p:= NextPrime(p);
    for D in Decomposition(S, p) do
      if IsSplit(D[1,1]) then
        c:= D[1,1] @@ hR;
        if c notin C0 then
          C0:= sub< CR | C0, c>;
          Append(~Gens, [D[1,1]]);
        end if;
      end if;
    end for;
  end while;
  // The generators from the local invariants
  if IsEven(Rank(L)) then
    assert false;
    ///TODO:::
  end if;

  Result:= [ IteratedNeighbours(L, P) ];
  // Orbit enumeration.
  i:= 1;
  while i le #Result do
    for g in Gens do
      LL:= Result[i,1];
      for p in g do
        LL:= Neighbours(LL, p: AutoOrbits:= false, Max:=1)[1];
      end for;
      if forall{X : X in R, R in Result | not IsIsometric(LL, X)} then
        Append(~Result, IteratedNeighbours(LL, P));
      end if;
    end for;
    i+:= 1;
  end while;
  
  Result:= &cat Result;
  assert forall{<i,j>: j in [1..i-1], i in [1..#Result] | not IsIsometric(Result[i], Result[j]) };
  return Result;
end intrinsic;

intrinsic IsIsotropic(L::LatModHerm, p::RngOrdIdl) -> BoolElt
{Tests is L is isotropic at p}
  R:= BaseRing(L);
  S:= BaseRing(R);
  if Order(p) cmpeq R then p:= p meet S; end if;
  require Order(p) eq S and IsPrime(p): "The second argument must be a prime ideal of the basering of the lattice";
  r:= Rank(L);
  if r ge 3 then return true; end if;
  if r eq 0 then return false; end if;
  d:= Determinant(L`Form);
  if r eq 1 then return d eq 0; end if;
  return IsLocalNorm(NumberField(R), -d, p);
end intrinsic;

intrinsic IsIsotropic(L::LatModHerm, p::RngIntElt) -> BoolElt
{"} //"
  R:= BaseRing(L);
  require IsPrime(p) and Type(BaseRing(R)) eq RngInt: "Wrong arguments";
  r:= Rank(L);
  if r ge 3 then return true; end if;
  if r eq 0 then return false; end if;
  M:= Matrix(Basis(L`Module));
  d:= Determinant(M * L`Form * InternalConjugate(L, M));
  if r eq 1 then return d eq 0; end if;
  return IsLocalNorm(NumberField(R), -d, p);
end intrinsic;

intrinsic IsIsotropic(L::LatModHerm) -> BoolElt
{Tests if L is isotropic}
  r:= Rank(L);
  if r ge 3 then return true; end if;
  if r eq 0 then return false; end if;
  M:= Matrix(Basis(L`Module));
  d:= Determinant(M * L`Form * InternalConjugate(L, M));
  if r eq 1 then return d eq 0; end if;
  return IsNorm(NumberField(BaseRing(L)), -d);
end intrinsic;
