load "SubidealLattices.m";

function RestrictAutomorphismTypes(l,n,maxEnumerate)
// Input: l in N; n in N; maxEnumerate in N

// Output: Restricts the possible automorphism types for extremal modular lattices as much as possible by enumerating all genuses of dimension <= maxEnumerate

    min := ExtremalMinimum(l,n);

    Types := AutomorphismTypes(l, Integers() ! (n/2), n, min);

    RestrictedTypes := [* *];

    for type in Types do
        type;
        p := type[1];
        n1 := type[2];
        np := type[3];
        s := type[4];

        Sigma1Orders := [];
        SigmapOrders := [];

        if p gt 2 and IsPrime(l) then

            k1 := type[6];
            kp := type[7];

            K<z> := CyclotomicField(p);
            Kpos := sub<K | z + z^(-1)>;

            if p le 3 then
                f := 1;
            else
                f := InertiaDegree(Factorization(ideal<Integers(Kpos) | l>)[1][1]);
            end if;
            deltap := (-1)^(Integers() ! (kp/f + (p-1)/2 * (Binomial(Integers() ! (np / (p-1) + 1), 2) + Binomial(s, 2))));
            delta1 := deltap * (-1)^(Integers() ! (s*(p-1)/2));

            if l eq 2 then
                if IsDivisibleBy(np + s*(p-1), 8) then
                    epsilonp := deltap;
                else
                    epsilonp := -deltap;
                end if;

                if IsDivisibleBy(n, 8) then
                    epsilon := 1;
                else
                    epsilon := -1;
                end if;
            else
                epsilonp := (-1)^(Integers() ! (kp / f + (l-1)/2*Binomial(kp,2)));

                if IsDivisibleBy(n*(l+1), 16) then
                    epsilon := 1;
                else
                    epsilon := -1;
                end if;
            end if;

            epsilon1 := epsilonp*epsilon;

            Sym1 := [* 2, n1 *];
            Symp := [* 2, np *];
            if l eq 2 then
                Append(~Sym1, <2, k1, epsilon1, 2, 0>);
                Append(~Sym1, <p, s, delta1>);
                Append(~Symp, <2, kp, epsilonp, 2, 0>);
                Append(~Symp, <p, s, deltap>);
            else
                if l lt p then
                    Append(~Sym1, <l, k1, epsilon1>);
                    Append(~Sym1, <p, s, delta1>);
                    Append(~Symp, <l, kp, epsilonp>);
                    Append(~Symp, <p, s, deltap>);
                else
                    Append(~Sym1, <p, s, delta1>);
                    Append(~Sym1, <l, k1, epsilon1>);
                    Append(~Symp, <l, kp, epsilonp>);
                    Append(~Symp, <p, s, deltap>);
                end if;
            end if;

            if n1 le maxEnumerate and n1 gt 0 then
                List1 := [L : L in EnumerateGenusSymbol(Sym1) | Minimum(L) ge min];
                if #List1 eq 0 then
                    continue type;
                end if;

                for L in List1 do
                    for c in ConjugacyClasses(AutomorphismGroup(L)) do
                        if not c[1] in Sigma1Orders then
                            Append(~Sigma1Orders, c[1]);
                        end if;
                    end for;
                end for;
            end if;

            if np le maxEnumerate and np gt 0 then
                Listp := [L : L in EnumerateGenusSymbol(Symp) | Minimum(L) ge min];
                if #Listp eq 0 then
                    continue type;
                end if;

                for L in Listp do
                    for c in ConjugacyClasses(AutomorphismGroup(L)) do
                        if not c[1] in SigmapOrders then
                            Append(~SigmapOrders, c[1]);
                        end if;
                    end for;
                end for;
            end if;

        else

            if n1 le maxEnumerate and n1 gt 0 and (p ne 2 or n1 le np) then
                det1 := p^s;
                for i := 5 to #type by 3 do
                    det1 *:= type[i]^type[i+1];
                end for;

                List1 := [L : L in EnumerateGenusDeterminant(det1, n1, true) | Minimum(L) ge min];
                if #List1 eq 0 then
                    continue type;
                end if;

                for L in List1 do
                    for c in ConjugacyClasses(AutomorphismGroup(L)) do
                        if not c[1] in Sigma1Orders then
                            Append(~Sigma1Orders, c[1]);
                        end if;
                    end for;
                end for;
            end if;

            if np le maxEnumerate and np gt 0 and (p ne 2 or np lt n1) then
                detp := p^s;
                for i := 5 to #type by 3 do
                    detp *:= type[i]^type[i+2];
                end for;

                Listp := [L : L in EnumerateGenusDeterminant(detp, np, true) | Minimum(L) ge min];
                if #Listp eq 0 then
                    continue type;
                end if;

                for L in Listp do
                    for c in ConjugacyClasses(AutomorphismGroup(L)) do
                        if not c[1] in SigmapOrders then
                            Append(~SigmapOrders, c[1]);
                        end if;
                    end for;
                end for;
            end if;

        end if;

        Append(~RestrictedTypes, <type, Sigma1Orders, SigmapOrders>);
    end for;

    return RestrictedTypes;

end function;


function PossibleCharPos(l, n, maxEnumerate)
// Input: l in N; n in N; maxEnumerate in N

// Output: List of all characteristic polynomials of lattices possibly not found by the subideal-lattice algorithm. Format: [<m, [<d_1,c_1>,...,<d_k,c_k>]>, ...] for the exponents c_i > 0 of the Phi_(d_l) for the divisors d_l where m is the order of sigma

    Types := RestrictAutomorphismTypes(l,n, maxEnumerate);

    "Test characteristic polynomials";
    Results := [];

    for phim in [Integers() ! (n/2)+1..n] do
        for m in EulerPhiInverse(phim) do
            Div := Sort(Divisors(m));
            Phi := [EulerPhi(d) : d in Div];
            k := #Div;

            pList := [p : p in PrimeDivisors(m) | Gcd(p,l) eq 1];
            FixDimLists := [];
            for p in pList do
                FixDims := [];
                for i in [1..#Types] do
                    type := Types[i][1];
                    FixDim := type[2];
                    if type[1] eq p then
                        if not FixDim in FixDims then
                            Append(~FixDims, FixDim);
                        end if;
                    end if;
                end for;
                if #FixDims eq 0 then
                    continue m;
                end if;
                Append(~FixDimLists, FixDims);
            end for;

            t := #pList;

            M := ZeroMatrix(Integers(), k, t+1);
            for i in [1..k] do
                for j in [1..t] do
                    if IsDivisibleBy(Integers() ! (m/pList[j]), Div[i]) then
                        M[i,j] := Phi[i];
                    end if;
                end for;
                M[i, t+1] := Phi[i];
            end for;

            if t gt 0 then
                TypeChoice := CartesianProduct([[1..#List]: List in FixDimLists]);

                for IndexList in TypeChoice do
                    N := ZeroMatrix(Integers(), 1, t+1);
                    MaxDim := [];
                    for i in [1..t] do
                        N[1][i] := FixDimLists[i][IndexList[i]];
                    end for;
                    N[1][t+1] := n;

                    MaxDim := [Floor(n/EulerPhi(d)) : d in Div];
                    for i in [1..k] do
                        for j in [1..t] do
                            if IsDivisibleBy(Integers() ! (m / pList[j]), Div[i]) then
                                MaxDim[i] := Minimum(MaxDim[i], Floor(N[1][j] / Phi[i]));
                            else
                                MaxDim[i] := Minimum(MaxDim[i], Floor((n-N[1][j]) / Phi[i]));
                            end if;
                        end for;
                    end for;

                    C := CartesianProduct([[0..MaxDim[i]] : i in [1..k]]);

                    for c in C do
                        if #[ci : ci in c | ci gt 0] le 1 then continue; end if;
                        MiPoDivisors := [Div[i] : i in [1..k] | c[i] gt 0];
                        if not Lcm(MiPoDivisors) eq m then continue; end if;

                        v := Matrix(Integers(), 1, k, [x : x in c]);

                        if v*M ne N then continue; end if;

                        if c[k] eq 1 and &or[IsDivisibleBy(Integers() ! (m/p), Lcm([Div[i] : i in [1..k-1] | c[i] gt 0])) : p in pList] then continue; end if;

                        for p1 in PrimeDivisors(m) do
                            for p2 in [p : p in PrimeDivisors(m) | p gt p1] do

                                if &and[Valuation(d,p1) eq Valuation(m, p1) xor Valuation(d, p2) eq Valuation(m, p2) : d in MiPoDivisors] then
                                    // In this case the induced sublattice of sigma^(m/p1) is the same as the sublattice of sigma^(m/p2) and thus must have index 1.

                                    if p1 in pList and &and[type[1][4] gt 0 : type in Types | type[1][1] eq p1 and type[1][2] eq N[1][Index(pList, p1)]] then continue c; end if;
                                    if p2 in pList and &and[type[1][4] gt 0 : type in Types | type[1][1] eq p2 and type[1][2] eq N[1][Index(pList, p2)]] then continue c; end if;
                                    if not p1 in pList and not p2 in pList then
                                        p1Fix := &+([c[i]*EulerPhi(Div[i]) : i in [1..k] | IsDivisibleBy(Integers() ! (m/p1), Div[i])]);
                                        p2Fix := n - p1Fix;
                                        if p1Fix eq 0 or p2Fix eq 0 then continue; end if;
                                        HermitePossible:=false;
                                        nHalfs := Integers() ! (n/2);
                                        for a in [Max(nHalfs - p2Fix, 0)..Min(nHalfs, p1Fix)] do
                                            for b in [Max(nHalfs - p2Fix, 0)..Min(nHalfs, p1Fix)] do
                                                if ExtremalMinimum(l,n) / (p1^a*p2^b)^(1/p1Fix) lt HermiteBounds[p1Fix]+0.1 and ExtremalMinimum(l,n) / (p1^(nHalfs-a)*p2^(nHalfs-b))^(1/p2Fix) lt HermiteBounds[p2Fix]+0.1 then
                                                    HermitePossible := true;
                                                    break a;
                                                end if;
                                            end for;
                                        end for;
                                        if not HermitePossible then
                                            continue c;
                                        end if;
                                    end if;
                                end if;
                            end for;
                        end for;

                        for p in pList do

                            // At least one fitting fix- or imagelattice must have an automorphism of the right order
                            
                            pFixList := [Div[i] : i in [1..k] | c[i] gt 0 and Valuation(Div[i],p) lt Valuation(m,p)];
                            if #pFixList gt 0 then
                                sigma1Order := Lcm(pFixList);
                                FittingTypes := [type : type in Types | type[1][1] eq p and type[1][2] eq N[1][Index(pList,p)]];
                                if #FittingTypes gt 0 and &and[#type[2] gt 0 : type in FittingTypes] and &and[not (sigma1Order in type[2]) : type in FittingTypes] then continue c; end if;
                            end if;

                            pImList := [Div[i] : i in [1..k] | c[i] gt 0 and Valuation(Div[i],p) eq Valuation(m,p)];
                            if #pImList gt 0 then
                                sigmapOrder := Lcm(pImList);
                                FittingTypes := [type : type in Types | type[1][1] eq p and type[1][2] eq N[1][Index(pList,p)]];
                                if #FittingTypes gt 0 and &and[#type[3] gt 0 : type in FittingTypes] and &and[not (sigmapOrder in type[3]) : type in FittingTypes] then continue c; end if;
                            end if;

                        end for;

                        ExpList := [<Div[i], c[i]> : i in [1..k] | c[i] gt 0];
                        Append(~Results, <m,ExpList>);
                    end for;
                end for;
            else
                C := CartesianProduct([[0..Floor(n/EulerPhi(d))] : d in Div]);
                N := Matrix(Integers(), 1, 1, [n]);
                for c in C do
                    if #[ci : ci in c | ci gt 0] le 1 then continue; end if;
                    MiPoDivisors := [Div[i] : i in [1..k] | c[i] gt 0];
                    if not Lcm(MiPoDivisors) eq m then continue; end if;

                    v := Matrix(Integers(), 1, k, [x : x in c]);

                    if v*M ne N then continue; end if;

                    for p1 in PrimeDivisors(m) do
                        for p2 in [p : p in PrimeDivisors(m) | p gt p1] do

                            if &and[Valuation(d,p1) eq Valuation(m, p1) xor Valuation(d, p2) eq Valuation(m, p2) : d in MiPoDivisors] then
                                // In this case the induced sublattice of sigma^(m/p1) is the same as the sublattice of sigma^(m/p2) and thus must have index 1.
                                p1Fix := &+([c[i]*EulerPhi(Div[i]) : i in [1..k] | IsDivisibleBy(Integers() ! (m/p1), Div[i])]);
                                p2Fix := n - p1Fix;
                                HermitePossible:=false;
                                nHalfs := Integers() ! (n/2);
                                for a in [Max(nHalfs - p2Fix, 0)..Min(nHalfs, p1Fix)] do
                                    for b in [Max(nHalfs - p2Fix, 0)..Min(nHalfs, p1Fix)] do
                                        if ExtremalMinimum(l,n) / (p1^a*p2^b)^(1/p1Fix) lt HermiteBounds[p1Fix]+0.1 and ExtremalMinimum(l,n) / (p1^(nHalfs-a)*p2^(nHalfs-b))^(1/p2Fix) lt HermiteBounds[p2Fix]+0.1 then
                                            HermitePossible := true;
                                            break a;
                                        end if;
                                    end for;
                                end for;
                                if not HermitePossible then
                                    continue c;
                                end if;
                            end if;
                        end for;
                    end for;

                    ExpList := [<Div[i], c[i]> : i in [1..k] | c[i] gt 0];
                    Append(~Results, <m,ExpList>);
                end for;
            end if;
        end for;
    end for;
    
    return Results;

end function;

//<14,20>,<15,20> missing
for ln in [<5,24>,<6,24>,<14,24>,<15,25>,<3,26>,<7,26>,<2,28>,<3,28>,<5,28>,<7,28>,<3,30>,<2,32>,<3,32>,<5,32>,<7,32>,<3,34>,<7,34>,<2,36>,<3,36>,<5,36>] do
    l := ln[1];
    n := ln[2];
    printf "n = %o, l = %o:\n", n, l;
    if l in [6,14,15] then
        maxEnumerate := 6;
    else
        maxEnumerate := 8;
    end if;
    Results := PossibleCharPos(l,n,maxEnumerate);
    ord := [];
    for r in Results do
        large := <r[1],1> eq r[2][#r[2]];
        if r[1] in [o[1] : o in ord] and large then
            ord[Index([o[1] : o in ord], r[1])][2] := true;
        end if;
        if not r[1] in [o[1] : o in ord] then
            Append(~ord, <r[1], large>);
        end if;
    end for;

    printf "\nPossible Orders for l = %o, n = %o:\n\n", l, n;
    ord;
end for;

