////////////////////////////////////////////////////////////////////////////////
/////////////// ExtremalLattices ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// 
// 03/2015
// Please mail any errors to: michael.juergens@math.tu-dortmund.de
//
////////////////////////////////////////////////////////////////////////////////


intrinsic IsModular(L::Lat) -> BoolElt
{ Returns true iff L is a modular lattice (in the sense of Quebbemann).}
 if IsIsometric(L,Dual(L)) then
  return true;
 else 
  return false;
 end if;
end intrinsic;


intrinsic IsStronglyModular(L::Lat) -> BoolElt
{ Returns true iff L is a strongly modular lattice.}
 l:=Level(L);
 return &and[IsIsometric(L,PartialDual(L,p)) : p in PrimeDivisors(l)];
end intrinsic;


intrinsic ModularLattice(n::RngIntElt,l::RngIntElt) -> Lat
{ Constructs a modular lattice of prime level l and dimension n.}

 require IsPrime(l): "l should be prime.";
 require IsEven(n): "n should be prime.";
 require l mod 4 eq 3 or n mod 4 eq 0: "n should be divisible by 4.";
 
 if l mod 4 eq 3 then
  K:=QuadraticField(-l);
  O<w>:=Integers(K);
  L0:=LatticeWithGram(Matrix(Integers(),2,2,[Trace(b1*ComplexConjugate(b2)) : b1,b2 in [1,w]]));
  L:=DirectSum([L0 : i in [1..Integers()!(n/2)]]);
 else
  p:=3;
  while not (&and[KroneckerSymbol(p,q) eq -1 : q in PrimeDivisors(l) | q ne 2] and p mod 8 eq 3) do
   p:=NextPrime(p);
  end while;
  K:=QuaternionAlgebra<Rationals()|-p,-l>;
  O:=MaximalOrder(K);
  L0:=LatticeWithGram(GramMatrix(O));
  L:=DirectSum([L0 : i in [1..Integers()!(n/4)]]);
 end if;
 return L;
end intrinsic;


intrinsic ExtremalModularForm(k::RngIntElt,l::RngIntElt:Genus:="a", Precision:=10) -> RngSerPowElt
{ Returns the extremal modular form of weight k and level l. }

 require l in [1,2,3,5,6,7,11,14,15,23]: "l should be in {1,2,3,5,6,7,11,14,15,23}"; 
 require l mod 4 eq 3 or IsEven(k): "k should be even.";
 require Genus in {"a","b"}: "Genus should be a or b";
 
 Pow<q>:=PowerSeriesRing(Rationals():Precision:=Precision);
 case l:
  when 1:
    L0:=Lattice(LatticeDatabase(),"E8");
  when 2:
    L0:=Lattice(LatticeDatabase(),"D4");
  when 3:
    L0:=LatticeWithGram(Matrix(Integers(),2,2,[2,1,1,2]));
  when 5:
    L0:=Lattice(LatticeDatabase(),"QQF.4.a");
  when 6:
    if Genus eq "a" then 
     L0:=Lattice(LatticeDatabase(),"QQF.4.i");
    else 
     L0:=Lattice(LatticeDatabase(),"QQF.4.g");
    end if;
  when 7:
    L0:=LatticeWithGram(Matrix(Integers(),2,2,[2,1,1,4]));
  when 11:
    L0:=LatticeWithGram(Matrix(Integers(),2,2,[2,1,1,6]));
  when 14:
    L0:=Lattice(LatticeDatabase(),"E(14)");
  when 15:
    L0:=Lattice(LatticeDatabase(),"E(15)");
  when 23:
    L0:=LatticeWithGram(Matrix(Integers(),2,2,[2,1,1,12]));
 end case; 

 n:=2*k;
 k0:=Integers()!(Dimension(L0)/2);
 M:=ThetaSeriesModularFormSpace(L0);
 SetPrecision(M,Precision+1);
 Theta0:=Pow!ThetaSeriesModularForm(L0);
 k1:=12*2^#PrimeDivisors(l)/SumOfDivisors(l); 
 dim:=1+Floor((n/2) /k1); 
 n1:=Integers()!(n/(2*k0));
 k2:=Integers()!(k1/k0);
 // Aufstellen der Basis Reihen von Theta^i * Delta^j
 e:=[];
 for j:=0 to dim-1 do
  e:= Append(e,Theta0^(n1-k2*j)*Delta(l:Precision:=Precision)^j);
 end for;
 e:=Vector(e);
 // Berechnen der Koeffizienten fuer extremale ThetaReihe
 m:=ZeroMatrix(Rationals(),dim,dim);
 for j:=1 to dim do
  for l:=1 to dim do
   m[j,l]:=Coefficient(e[l],j-1);
  end for;
 end for;
 c:=Vector(ColumnSubmatrix((m^(-1)),1,1));
 // Aufstellen der extremalen ThetaReihe
 s:=0;
 for j:=1 to dim do
  s:=s+c[j]*e[j];
 end for;
 return Pow!s+O(q^(Precision+1));
end intrinsic;


intrinsic Delta(l::RngIntElt:Precision:=10) -> RngSerPowElt
{ Computes the function Delta.}

 require l in [1,2,3,5,6,7,11,14,15,23]: "l should be in {1,2,3,5,6,7,11,14,15,23}"; 

 Pow<q>:=PowerSeriesRing(Rationals():Precision:=Precision);
 Eta:=function(m)
  Pow<q>:=PowerSeriesRing(Rationals():Precision:=Precision);
  f<q>:=DedekindEta(q);
  return DedekindEta(q^m)/(q^(m/24));
 end function;

 Del<q>:=Pow!1;
 for i in Divisors(l) do
  Del *:= Eta(i);
 end for;
 return Pow!(q*Del^(24/SumOfDivisors(l))+O(q^(Precision+1)));
end intrinsic;


intrinsic Ausgabe(Genus::SeqEnum : SaveData:="")
{ Internal. }

Sort(~Genus,func<L,M|#AutomorphismGroup(M)-#AutomorphismGroup(L)>);
fprintf SaveData,"/* \n\n";
DB:=LatticeDatabase();
for i := 1 to #Genus do
 fprintf SaveData,"%o. %o", i,Genus[i];
 fprintf SaveData,"\n\n|Aut|    = %o\n", Factorization(#AutomorphismGroup(Genus[i]));
 Name:="-";
 printf "%o Isometrietests..",NumberOfLattices(DB,Dimension(Genus[i]));
 for j:=1 to NumberOfLattices(DB,Dimension(Genus[i])) do
  if Order(AutomorphismGroup(Lattice(DB,Dimension(Genus[i]),j))) eq Order(AutomorphismGroup(Genus[i])) then 
  if IsIsometric(Lattice(DB,Dimension(Genus[i]),j),Genus[i]) then
   Name:=LatticeName(DB,Dimension(Genus[i]),j);
   break;
  end if;
 end if;
 end for;
 printf "Fertig!\n";
if IsPrime(Level(Genus[i])) then  
 fprintf SaveData,"Modular  = %o\n",IsStronglyModular(Genus[i]);
else
 fprintf SaveData,"St.mod.  = %o\n",IsStronglyModular(Genus[i]);
end if;
 fprintf SaveData,"LatDB    = %o\n\n\n",Name; 
end for;
fprintf SaveData,"*/ \n\n";
fprintf SaveData,"// Data \n\n";
fprintf SaveData,"Liste:=%m;",Genus;
end intrinsic;

