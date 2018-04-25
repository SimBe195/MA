////////////////////////////////////////////////////////////////////////////////
/////////////// IdealLattices //////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// 
// 03/2015
// Please mail any errors to: michael.juergens@math.tu-dortmund.de
//
////////////////////////////////////////////////////////////////////////////////



intrinsic DataPreprocessing(E::FldNum) -> Tup
{ Preprocessing for computation of ideal-lattices. }

 z:=PrimitiveElement(E);
 F:=sub< E | z+ComplexConjugate(z), z*ComplexConjugate(z) >;

 vprintf CMNeighbours,2:"Computing class group..";
 // Berechnet die Klassengruppe. Ergebnis wird wg. Bound:=1 nicht verifiziert!
 Cl,mapCl:=ClassGroup(E:Bound:=1);
 vprintf CMNeighbours,2:"done! Class number: %o\n",#Cl;

 vprintf CMNeighbours,2:"Computing operation of Galois group on the class group..";
 ClassesModGalois:=[];
 for a in Cl do
  A:=mapCl(a);
  neu:=true;
  for f in Automorphisms(E) do
   if Inverse(mapCl)(ideal<Integers(E)| [f(x) : x in Generators(A)] >) in ClassesModGalois then neu:=false; break; end if;
  end for;
  if neu then Append(~ClassesModGalois,a); end if;
 end for;
 vprintf CMNeighbours,2:"done! Classes modulo Galois group: %o\n",#ClassesModGalois;

 vprintf CMNeighbours,2:"Computing unit group..";
 if Degree(E) gt 24 then
  // Berechnet aus Rechenzeitgründen eine Untergruppe der Einheitengruppe vom Index, welcher nicht durch
  // p=2 teilbar ist. Dies genügt zur Berechnung der Gruppe U/U^2:
  U,mapU:=pFundamentalUnits(F,2);
 else
  U,mapU:=UnitGroup(F);
 end if;
 // Bestimme Repräsentanten der Quadratklassen der Einheitengruppe von F
 UnitsF:=[mapU(U.i) : i in [1..#Generators(U)]];
 // überflüssig?!
 if -1 notin UnitsF then printf "Fuege -1 hinzu\n"; Append(~UnitsF,-1); end if;

 //Bestimme Matrix der VZ-Verteilung über F_2: -1 -> 1 und +1 -> 0
 M:=ZeroMatrix(GF(2),#UnitsF,Degree(F));
 for i:=1 to #UnitsF do
  r:=RealSigns(F!UnitsF[i]);
  for j:=1 to Degree(F) do
   if r[j] eq 1 then M[i,j]:=0; else M[i,j]:=1; end if;
  end for;
 end for;

 // Bestimme total positive Einheiten <-> Vektoren im Kern der Matrix M
 TotPosUnits:=[];
 for x in Kernel(M) do
  uu:=F!1;
  for i:=1 to #UnitsF do
   if x[i] eq GF(2)!1 then uu*:=UnitsF[i]; end if;
  end for;
  Append(~TotPosUnits,uu);
 end for;
 vprintf CMNeighbours,2:"done! Square classes of totally positive units: %o\n",#TotPosUnits;

 vprintf CMNeighbours,2:"Computing norm residue-classes..";
 // Bestimme nun die Normrestklassen total positiver Einheiten.
 // Nehme dazu das Vertretersystem total positiver Quadratklassen und rechne 
 // modulo Normen, d.h. prüfe für zwei solche Vertreter, ob x/y eine Norm ist. 
 // Hier ist wichtig, dass man die Normgleichung über dem Ganzheitsring und 
 // nicht über dem Körper löst!
 NormClasses:=[];
 for uu in TotPosUnits do
  neu:=true;
  for vv in NormClasses do
   if NormEquation(Integers(RelativeField(F,E)),Integers(RelativeField(F,E))!(uu/vv)) then neu:=false; break; end if;
  end for; 
  if neu then Append(~NormClasses,uu); end if;
 end for;
 vprintf CMNeighbours,2:"done!\n";
 vprintf CMNeighbours,2:"There are %o norm residue-classes of totally positive units.\n",#NormClasses;

 return <Cl,mapCl,ClassesModGalois,U,mapU,NormClasses>;
end intrinsic;



intrinsic IdealLattices(d0::RngIntElt,E::FldNum : Data:=<> ) -> SeqEnum
{ Constructs all ideal lattices of determinant d0 over E. }

 require IsTotallyComplex(E): "Field should be a CM-field.";
 z:=PrimitiveElement(E);
 F:=sub< E | z+ComplexConjugate(z), z*ComplexConjugate(z)>;
 require IsTotallyReal(F): "Field should be a CM-field.";
  
 if d0 ne 1 then l:=&*[p : p in PrimeDivisors(d0)]; else l:=1; end if;
 
 res:=[];

 if #Data eq 0 then
  Data:=DataPreprocessing(E);
 else
  vprintf CMNeighbours,2:"Loading data..\n";
 end if;

 Cl:=Data[1];
 mapCl:=Data[2];
 ClassesModGalois:=Data[3];
 U:=Data[4];
 mapU:=Data[5];
 NormClasses:=Data[6];

 u:=[mapU(U.i) : i in [1..#Generators(U)]];
 if -1 notin u then Append(~u,-1); end if;
 M:=ZeroMatrix(GF(2),#u,Degree(F));
 for i:=1 to #u do
  r:=RealSigns(F!u[i]);
  for j:=1 to Degree(F) do
   if r[j] eq 1 then M[i,j]:=0; else M[i,j]:=1; end if;
  end for;
 end for;
 Array:=AssociativeArray();
 
 vprintf CMNeighbours,2:"There are %o ideal-classes modulo Galois group.\n",#ClassesModGalois;
 vprintf CMNeighbours,2:"There are %o norm residue-classes of totally positive units.\n",#NormClasses;
 vprintf CMNeighbours,2:"There are %o possible ideals B.\n",#[I : I in Divisors(ideal<Integers(E)|l>) | Norm(I) eq d0];

  for B in [I : I in Divisors(ideal<Integers(E)|l>) | Norm(I) eq d0] do
   vprintf CMNeighbours,2:"next B\n";
   for a in ClassesModGalois do
    A:=mapCl(a);
    J:=B/(A*ComplexConjugate(A)*Different(Integers(E)));
    hasShape, ImeetF:=IdealMeetF(J,E);  
    if hasShape then 
     vprintf CMNeighbours,2:"Computing generator..";
     bool,alpha:=IsPrincipal(ImeetF);
     assert bool; // was soll das? 
     vprintf CMNeighbours,2:"done!\n";

     v:=KSpace(GF(2),Degree(F))!0;
     for i:=1 to Degree(F) do
      if RealSigns(alpha)[i] eq -1 then v[i]:=1; end if;
     end for;

     if v in Image(M) then
      uu:=1;
      for i:=1 to #u do
       if Solution(M,v)[i] eq GF(2)!1 then uu*:=u[i]; end if;
      end for;
      alpha*:=uu;
      for uu in NormClasses do
       N:=CoordinateLattice(LLL(Seysen(LLL(TransferLattice(HermLattice(Matrix(E,1,1,[alpha*uu]),[A]))))));
       key:=<#AutomorphismGroup(N),ThetaSeries(N,8)>;
       neu:=true;  
       if IsDefined(Array,key) then
       // Bereits Gitter mit den Invarianten vorhanden
         vprintf CMNeighbours,2:"Isometry tests: %o\n",#Array[key];
         for M in res[Array[key]] do
          if IsIsometric(M,N) then neu:=false; break; end if;
         end for;
        else 
       // Noch kein Gitter mit den Invarianten vorhanden, also Gitter ist neu
        Array[key]:=[];
       end if; 
    
       // Falls Gitter neu, füge es in die Datenstruktur ein
       if neu then 
        vprintf CMNeighbours,2:"New lattice found!\n";
        Append(~res,N);
        Append(~Array[key],#res);
       end if;
      end for;
    else 
     vprintf CMNeighbours,3:"***Warning****, possible mistake if unit group is not correct!\n";
    end if;
   else
    vprintf CMNeighbours,2: "Ideal B not valid!\n";
    break;
   end if;
  end for;
 end for;
 return res;
end intrinsic;


intrinsic IdealLattices(d0::RngIntElt,m::RngIntElt) -> SeqEnum
{ Constructs all ideal lattices of determinant d0 over the m-th cyclotomic field. }
 return IdealLattices(d0,CyclotomicField(m));
end intrinsic;


intrinsic IdealMeetF(I::RngOrdFracIdl,E::FldNum) -> BoolElt,RngOrdFracIdl
{ Internal. }
 
 z:=PrimitiveElement(E);
 F:=sub< E | z+ComplexConjugate(z), z*ComplexConjugate(z)>;
 RelEF:=RelativeField(F,E);

 // Boolscher Wert, der angibt, ob I überhaupt die Form I=(I meet F)O hat
 Shape:=true; 
 // Speichert das Ideal I meet F
 ImeetF:=ideal<Integers(F)|1>;
 SplitIdeals:=[];
 
 for tup in Factorization(I) do
  P:=tup[1];
  nuP:=tup[2];
  
  // Fasse Ideal P als Ideal von der relativen Erweiterung E:F auf
  RelP:=ideal<Integers(RelEF)|Generators(P)>;
  // Berechne die Norm von P: N(P):=P*Conjugate(P) meet F = p^f(P:p) 
  // Für die letzte Gleichheit siehe Marcus S.84 Ü14
  // Das Ideal p erhält man nun für f=1 durch p:=N(P) und im Fall f=2 durch
  // p:=N(P)^1/2.
  Relp:=Norm(RelP);
  
  if IsRelativeInert(P) then
    p:=Factorization(ideal<Integers(F) | Generators(Relp)>)[1][1];
    ImeetF*:=p^nuP; 
  else 
   if IsRelativeRamified(P) then
    if not IsEven(tup[2]) then Shape:=false; break; end if; 
    p:=Factorization(ideal<Integers(F) | Generators(Relp)>)[1][1];
    ImeetF*:=p^Ceiling(nuP/2); 
   else 
    if IsRelativeSplit(P) then
     if Valuation(I,P) ne Valuation(I,ComplexConjugate(P)) then Shape:=false; break; end if; 
     if not ComplexConjugate(P) in SplitIdeals then 
      p:=Factorization(ideal<Integers(F) | Generators(Relp)>)[1][1];
      ImeetF*:=p^nuP; 
      Append(~SplitIdeals,P);
      Append(~SplitIdeals,ComplexConjugate(P)); 
     end if; 
    end if;
   end if;                  
  end if;
 end for;
 if Shape then return true,ImeetF; else return false,_; end if;
end intrinsic;

