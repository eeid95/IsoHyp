// Examples


// Computing the first g components of a rational representation of the multiplication 
// by ell

load "EquadiffSolver_all_genus.m";


SetVerbose("SEA", 1);	


g := 2; p := 7; n:=1;
ell := 140; PadicTimings := [];


repeat

    repeat
        ell := ell +1;
    until ell mod p ne 0;


    PrP :=  32+ Floor(Log(p, 4*g*ell^2));

    "---";
    "- p =", p, ", n =", n, ", ell =", ell, ", degree =", ell^2;
    "-----------------------------------------";

    FF := GF(p); K := pAdicField(p ,PrP);
    _<x> := PolynomialRing(FF); S<z> := PolynomialRing(K);

    repeat

        repeat

            repeat
                hC1 := RandomIrreduciblePolynomial(FF, 2*g+1) ;
                H := HyperellipticCurve(hC1); J := Jacobian(H);
            until #H ne 1;

            repeat
                PtF:=Random(H);
            until PtF[3] ne 0;

            PF := J![x - PtF[1] , PtF[2]]; QF := ell *PF;
           
        until Degree(QF[1]) eq g and Discriminant(QF[1]) ne 0 and Degree(SplittingField(QF[1])) lt g+1;

        f := QF[1]; SF := SplittingField(f); 
        hC:= S!hC1;
        H := HyperellipticCurve(hC); J := Jacobian(H);
        Pt:= Points(H , PtF[1])[1];
        if Valuation(K!PtF[2] - Pt[2]) lt 1 then 
            Pt:= Points(H , PtF[1])[2];
        end if;
        P := J![z - Pt[1] , Pt[2]]; Q := J!DoubleAndAdd(P, ell);
        R := Roots(Q[1]);
       
    until Degree(Q[1]) eq g and Valuation(Discriminant(Q[1])) eq 0 and #R eq g;


    PrP :=  1 + Floor(Log(p, 2*g*ell^2));

    K := pAdicField(p ,PrP);
    if Degree(SF) ne 1 then
        K<u> := UnramifiedExtension(K , DefiningPolynomial(SF));
    end if;
    S<z> := PolynomialRing(K); L<t> := LaurentSeriesRing(K, 2*g*ell^2);
    R := Roots(S!Q[1]);

    RootList := [[i[1]] : i in R];
    yRootList :=  [ [Evaluate(S!Q[2],i[1])] : i in RootList];

    _u0 := K!Evaluate(-S!P[1] ,0) ; _v0 := K!Evaluate( P[2], 0);

    _X0 := Matrix( K , RootList);
    _Y0 := Matrix( K , yRootList);

    _Mij := DiagonalMatrix( K , g , [ell : i in [1..g]]);

    
    X, timings := EquadifSolver(ell^2  , hC , hC , _Mij, _X0, _Y0, _u0 , _v0,PrP);
  
    K := pAdicQuotientRing(p ,PrP); L<t> := LaurentSeriesRing(FF , 2*g*ell^2+1);
    PP<x> := PolynomialRing(L);

    tm := Cputime();

    Xi := [ PadicToFF(X[i,1]) : i in [1..g]];

    time T := Tree(Xi);
    T := T[1]; T := PP!T[#T][1]; coeff := Coefficients(T);

   
    Num, Denom:= FastBerlekampMassey( g*ell^2, L!coeff[1] );
    Nums := [L!Coefficients(Denom)*L!coeff[k] : k in [2..#coeff-1]];


    Append(~PadicTimings, <ell^2,&+timings+Cputime(tm)>) ;

 

until ell gt 150;
