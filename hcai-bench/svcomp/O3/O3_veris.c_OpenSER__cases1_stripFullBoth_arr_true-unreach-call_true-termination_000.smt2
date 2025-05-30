(set-logic HORN)


(declare-fun |main@precall4.split| ( ) Bool)
(declare-fun |main@.preheader| ( Int Int (Array Int Int) Int Int (Array Int Int) Int Int ) Bool)
(declare-fun |main@_bb| ( (Array Int Int) Int Int Int (Array Int Int) Int ) Bool)
(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@.lr.ph| ( Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q Int) (R (Array Int Int)) (S Int) (T Int) (U Int) (V (Array Int Int)) (W Int) (X Int) (Y Int) (Z (Array Int Int)) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 (Array Int Int)) (F1 Int) (G1 Int) (H1 (Array Int Int)) (I1 Int) (J1 Bool) (K1 Int) (L1 (Array Int Int)) (M1 (Array Int Int)) (N1 Int) (O1 Bool) (P1 Bool) (Q1 Int) (R1 (Array Int Int)) (S1 Int) (T1 Int) (U1 Int) (V1 (Array Int Int)) (W1 Int) ) 
    (=>
      (and
        (main@entry D1)
        (and (= J (store F G H))
     (= N (store J K L))
     (= R (store N O P))
     (= V (store R S T))
     (= Z (store V W X))
     (= E1 (store Z A1 B1))
     (= H1 (store E1 F1 G1))
     (= V1 (store H1 I1 0))
     (= A D1)
     (= C W1)
     (= E D1)
     (= G (+ 1 W1))
     (= I D1)
     (= K (+ 2 W1))
     (= M D1)
     (= O (+ 3 W1))
     (= Q D1)
     (= S (+ 4 W1))
     (= U D1)
     (= W (+ 5 W1))
     (= Y D1)
     (= A1 (+ 6 W1))
     (= C1 D1)
     (= F1 (+ 7 W1))
     (= I1 (+ 8 W1))
     (= K1 U1)
     (not (<= U1 0))
     (not (<= W1 0))
     (or (not P1) (not O1) (= M1 L1))
     (or (not P1) (not O1) (= R1 M1))
     (or (not P1) (not O1) (= N1 (- 1)))
     (or (not P1) (not O1) (= Q1 0))
     (or (not P1) (not O1) (= S1 N1))
     (or (not P1) (not O1) (= T1 Q1))
     (or (not (<= K1 0)) (<= U1 0))
     (or (not (<= C 0)) (<= W1 0))
     (or (not (<= G 0)) (<= W1 0))
     (or (not (<= K 0)) (<= W1 0))
     (or (not (<= O 0)) (<= W1 0))
     (or (not (<= S 0)) (<= W1 0))
     (or (not (<= W 0)) (<= W1 0))
     (or (not (<= A1 0)) (<= W1 0))
     (or (not (<= F1 0)) (<= W1 0))
     (or (not (<= I1 0)) (<= W1 0))
     (or (not O1) (and P1 O1))
     (not J1)
     (= O1 true)
     (= F (store B C D)))
      )
      (main@_bb R1 S1 T1 U1 V1 W1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Bool) (J Int) (K Int) (L Bool) (M (Array Int Int)) (N Int) (O Int) (P (Array Int Int)) (Q Int) (R Bool) (S Bool) (T Int) (U (Array Int Int)) (V Int) (W Int) (X Int) (Y (Array Int Int)) (Z Int) ) 
    (=>
      (and
        (main@_bb D A F X Y Z)
        (and (= B (+ Z N))
     (= E (select Y B))
     (= N (+ 1 A))
     (not (<= Z 0))
     (or (not S) (not R) (= P M))
     (or (not S) (not R) (= U P))
     (or (not S) (not R) (= Q N))
     (or (not S) (not R) (= T O))
     (or (not S) (not R) (= V Q))
     (or (not S) (not R) (= W T))
     (or (not I) (not S) (= G D))
     (or (not I) (not S) (= M G))
     (or (not I) (not S) (= J F))
     (or (not I) (not S) (= H E))
     (or (not I) (not S) (= K H))
     (or (not I) (not S) (= O J))
     (or (not I) (not S) (not C))
     (or (not (<= B 0)) (<= Z 0))
     (or (not R) (and S R))
     (or (not S) (= L (= K 0)))
     (or (not S) (and I S))
     (or (not S) (not L))
     (= R true)
     (= C (= E 0)))
      )
      (main@_bb U V W X Y Z)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Bool) (R Int) (S Int) (T Bool) (U Bool) (V Int) (W Bool) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 (Array Int Int)) (H1 Int) (I1 Int) (J1 Int) (K1 (Array Int Int)) (L1 Int) (M1 Int) (N1 (Array Int Int)) (O1 Int) (P1 Bool) (Q1 Int) (R1 Int) (S1 Bool) (T1 (Array Int Int)) (U1 Int) (V1 Int) (W1 (Array Int Int)) (X1 Int) (Y1 Bool) (Z1 Bool) (A2 Int) (B2 (Array Int Int)) (C2 Int) (D2 Int) (E2 Int) (F2 (Array Int Int)) (G2 Int) ) 
    (=>
      (and
        (main@.preheader L U1 G1 I1 E2 F2 G2 J1)
        (let ((a!1 (or (not C) (not (= (<= 32 K) D))))
      (a!2 (or (not U) (not (= (<= I1 0) T))))
      (a!3 (or (not C1) (not (= (<= 2 F1) B1))))
      (a!4 (or (not C1) (= A1 (+ Y (* (- 1) Z))))))
  (and (= K (select F2 A))
       (not (<= G2 0))
       (or (not E) (not D) (not C))
       (or (not G) (not F) (not E))
       (or D (not C) (not H))
       (or (not J) (not I) (not H))
       (or (not N) (and I H) (and F E))
       (or (not U) (not N) (= P M))
       (or (not U) (not N) (= M K))
       (or (not U) (not N) (= O L))
       (or (not U) (not N) (= S O))
       (or (<= G2 0) (not C1) (not (<= X 0)))
       (or (not C1) (not U) (= V I1))
       (or (not C1) (not U) (= Y V))
       (or (not C1) (not U) (not T))
       (or (not Z1) (not Y1) (= W1 T1))
       (or (not Z1) (not Y1) (= B2 W1))
       (or (not Z1) (not Y1) (= X1 U1))
       (or (not Z1) (not Y1) (= A2 V1))
       (or (not Z1) (not Y1) (= C2 X1))
       (or (not Z1) (not Y1) (= D2 A2))
       (or (not P1) (<= E2 0) (not (<= H1 0)))
       (or (not P1) (not C1) D1)
       (or (not P1) (not Z1) (= N1 K1))
       (or (not P1) (not Z1) (= T1 N1))
       (or (not P1) (not Z1) (= Q1 M1))
       (or (not P1) (not Z1) (= O1 L1))
       (or (not P1) (not Z1) (= R1 O1))
       (or (not P1) (not Z1) (= V1 Q1))
       (or (<= G2 0) (not (<= A 0)))
       a!1
       (or (not C) (and C B))
       (or (not E) (= G (= K 32)))
       (or (not E) (and E C))
       (or (not F) E)
       (or (not H) (= J (= K 9)))
       (or (not H) (and H C))
       (or (not I) H)
       a!2
       (or (not U) (= Q (= P 34)))
       (or (not U) (= R (ite Q 1 0)))
       (or (not U) (= Z (+ R S)))
       (or (not U) (and U N))
       a!3
       (or (not C1) (= W (= Y Z)))
       (or (not C1) (not (= B1 E1)))
       (or (not C1) (= X (+ G2 Z)))
       (or (not C1) (= F1 (+ 1 A1)))
       a!4
       (or (not C1) (and C1 U))
       (or (not C1) W)
       (or (not Y1) (and Z1 Y1))
       (or (not Z1) (= S1 (= R1 0)))
       (or (not Z1) (and P1 Z1))
       (or (not P1) (= K1 (store G1 H1 0)))
       (or (not P1) (= H1 (+ E2 F1)))
       (or (not P1) (= L1 (select F2 J1)))
       (or (not P1) (= M1 (+ 2 I1)))
       (or (not P1) (not (<= E2 0)))
       (or (not P1) (not (<= G2 0)))
       (or (not P1) (and P1 C1))
       (or (not P1) (not E1))
       (or (not Z1) (not S1))
       (= Y1 true)
       (= A (+ G2 L))))
      )
      (main@_bb B2 C2 D2 E2 F2 G2)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Bool) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Int) (V Bool) (W Int) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Bool) (E1 Int) (F1 Bool) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Int) (P1 (Array Int Int)) (Q1 Int) (R1 Int) (S1 Int) (T1 (Array Int Int)) (U1 Int) (V1 Int) (W1 (Array Int Int)) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Int) (B2 Bool) (C2 (Array Int Int)) (D2 Int) (E2 Int) (F2 (Array Int Int)) (G2 Int) (H2 Bool) (I2 Bool) (J2 Int) (K2 (Array Int Int)) (L2 Int) (M2 Int) (N2 Int) (O2 (Array Int Int)) (P2 Int) ) 
    (=>
      (and
        (main@.lr.ph D2 P1 R1 N2 O2 P2 S1 I1 U)
        (let ((a!1 (or (not C) (not (= (<= 32 G) D))))
      (a!2 (or (not X) (not (= (<= U 1) V))))
      (a!3 (or (not L1) (not (= (<= 2 O1) K1))))
      (a!4 (or (not L1) (= J1 (+ H1 (* (- 1) I1))))))
  (and (= G (select O2 A))
       (not (<= P2 0))
       (or (not I) (and R F) (and O E))
       (or (not X) (and S R) (and P O))
       (or (not B1) (not X) (= Y W))
       (or (not B1) (not X) (= Z Y))
       (or (not B1) (not X) (not V))
       (or (not O) (not D) (not C))
       (or (not Q) (not O) (not E))
       (or Q (not P) (not O))
       (or (not R) D (not C))
       (or (not R) (not T) (not F))
       (or (not S) (not R) T)
       (or (not D1) (not I) (= H G))
       (or (not D1) (not I) (= K H))
       (or (not D1) (not I) (= N J))
       (or (not D1) (not I) (= J U))
       (or (<= P2 0) (not L1) (not (<= G1 0)))
       (or (not L1) (and L1 D1) (and L1 B1))
       (or (not L1) (not B1) (= C1 Z))
       (or (not L1) (not B1) (= H1 C1))
       (or (not L1) (not D1) (= E1 A1))
       (or (not L1) (not D1) (= H1 E1))
       (or (not I2) (not H2) (= F2 C2))
       (or (not I2) (not H2) (= K2 F2))
       (or (not I2) (not H2) (= G2 D2))
       (or (not I2) (not H2) (= J2 E2))
       (or (not I2) (not H2) (= L2 G2))
       (or (not I2) (not H2) (= M2 J2))
       (or (not Y1) (<= N2 0) (not (<= Q1 0)))
       (or (not Y1) (not L1) M1)
       (or (not Y1) (not I2) (= W1 T1))
       (or (not Y1) (not I2) (= C2 W1))
       (or (not Y1) (not I2) (= Z1 V1))
       (or (not Y1) (not I2) (= X1 U1))
       (or (not Y1) (not I2) (= A2 X1))
       (or (not Y1) (not I2) (= E2 Z1))
       (or (<= P2 0) (not (<= A 0)))
       a!1
       (or (not C) (and C B))
       a!2
       (or (not X) (= W (+ (- 1) U)))
       (or (not B1) (and B1 X))
       (or (not O) (= Q (= G 32)))
       (or (not O) (and O C))
       (or O (not E))
       (or (not P) O)
       (or (not R) (= T (= G 9)))
       (or (not R) (and R C))
       (or R (not F))
       (or (not S) R)
       (or (not D1) (= L (= K 34)))
       (or (not D1) (= M (ite L (- 1) 0)))
       (or (not D1) (= A1 (+ M N)))
       (or (not D1) (and D1 I))
       a!3
       (or (not L1) (= F1 (= H1 I1)))
       (or (not L1) (not (= K1 N1)))
       (or (not L1) (= G1 (+ P2 I1)))
       (or (not L1) (= O1 (+ 1 J1)))
       a!4
       (or (not L1) F1)
       (or (not H2) (and I2 H2))
       (or (not I2) (= B2 (= A2 0)))
       (or (not I2) (and Y1 I2))
       (or (not Y1) (= T1 (store P1 Q1 0)))
       (or (not Y1) (= Q1 (+ N2 O1)))
       (or (not Y1) (= U1 (select O2 S1)))
       (or (not Y1) (= V1 (+ 2 R1)))
       (or (not Y1) (not (<= N2 0)))
       (or (not Y1) (not (<= P2 0)))
       (or (not Y1) (and Y1 L1))
       (or (not Y1) (not N1))
       (or (not I2) (not B2))
       (= H2 true)
       (= A (+ P2 U))))
      )
      (main@_bb K2 L2 M2 N2 O2 P2)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) ) 
    (=>
      (and
        (main@_bb J K D L M N)
        (and (= A (select M O))
     (= I (+ 1 K))
     (= O (+ N I))
     (not (<= N 0))
     (or C (not B) (not F))
     (or (= G D) (not E) (not F))
     (or (= H G) (not E) (not F))
     (or (not (<= O 0)) (<= N 0))
     (or (not F) (and F B))
     (or (not E) (and E F))
     (= E true)
     (= C (= A 0)))
      )
      (main@.preheader H I J K L M N O)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Int) (R Int) (S (Array Int Int)) (T Int) (U Int) (V (Array Int Int)) (W Int) (X Int) ) 
    (=>
      (and
        (main@.preheader L R S T U V W X)
        (let ((a!1 (or (not C) (not (= (<= 32 E) D)))))
  (and (= E (select V A))
       (not (<= W 0))
       (or (not F) (not D) (not C))
       (or D (not I) (not C))
       (or (not G) H (not F))
       (or (not O) (and J I) (and G F))
       (or (not J) K (not I))
       (or (= P M) (not N) (not O))
       (or (= Q P) (not N) (not O))
       (or (<= W 0) (not (<= A 0)))
       a!1
       (or (not C) (and C B))
       (or (not F) (= H (= E 32)))
       (or (not F) (and F C))
       (or (not I) (= K (= E 9)))
       (or (not I) (and I C))
       (or (not G) F)
       (or (not O) (= M (+ 1 L)))
       (or (not J) I)
       (or (not N) (and N O))
       (= N true)
       (= A (+ W L))))
      )
      (main@.preheader Q R S T U V W X)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Bool) (R Int) (S Int) (T Bool) (U Bool) (V Bool) (W Bool) (X Int) (Y Int) (Z (Array Int Int)) (A1 Int) (B1 Int) (C1 (Array Int Int)) (D1 Int) (E1 Int) (F1 Int) (G1 Int) ) 
    (=>
      (and
        (main@.preheader L Y Z A1 B1 C1 D1 E1)
        (let ((a!1 (or (not C) (not (= (<= 32 K) D))))
      (a!2 (or (not T) (not (= (<= A1 0) U)))))
  (and (= K (select C1 A))
       (not (<= D1 0))
       (or (not C) D (not H))
       (or (not E) (not G) (not F))
       (or (not E) (not D) (not C))
       (or (and E F) (not N) (and I H))
       (or (not T) (not N) (= M K))
       (or (not T) (not N) (= P M))
       (or (not T) (not N) (= S O))
       (or (not T) (not N) (= O L))
       (or (not J) (not I) (not H))
       (or (not W) (not V) (= X A1))
       (or (not W) (not V) (= G1 X))
       (or U (not T) (not W))
       (or (<= D1 0) (not (<= A 0)))
       (or (not H) (= J (= K 9)))
       (or (not H) (and C H))
       (or (not I) H)
       a!1
       (or (not C) (and C B))
       (or (not E) (= G (= K 32)))
       (or (not E) (and E C))
       (or E (not F))
       (or (not V) (and W V))
       a!2
       (or (not T) (= Q (= P 34)))
       (or (not T) (= R (ite Q 1 0)))
       (or (not T) (= F1 (+ R S)))
       (or (not T) (and T N))
       (or (not W) (and W T))
       (= V true)
       (= A (+ D1 L))))
      )
      (main@.lr.ph Y Z A1 B1 C1 D1 E1 F1 G1)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Bool) (N Int) (O Bool) (P Bool) (Q Int) (R Int) (S (Array Int Int)) (T Int) (U Int) (V (Array Int Int)) (W Int) (X Int) (Y Int) (Z Int) ) 
    (=>
      (and
        (main@.lr.ph R S T U V W X Y L)
        (let ((a!1 (or (not C) (not (= (<= 32 E) D))))
      (a!2 (or (not P) (not (= (<= L 1) M)))))
  (and (= E (select V A))
       (not (<= W 0))
       (or (not F) H (not G))
       (or (not F) (not C) (not D))
       (or (not I) K (not J))
       (or (not I) (not C) D)
       (or (not P) (and I J) (and F G))
       (or (not P) (not O) (= Q N))
       (or (not P) (not O) (= Z Q))
       (or M (not P) (not O))
       (or (not (<= A 0)) (<= W 0))
       (or (not O) (and P O))
       (or (not F) (= H (= E 32)))
       (or (not F) (and C F))
       (or F (not G))
       a!1
       (or (not C) (and C B))
       (or (not I) (= K (= E 9)))
       (or (not I) (and I C))
       (or I (not J))
       a!2
       (or (not P) (= N (+ (- 1) L)))
       (= O true)
       (= A (+ W L))))
      )
      (main@.lr.ph R S T U V W X Y Z)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Int) (Q Int) (R Int) (S Bool) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Bool) (Z Int) (A1 Bool) (B1 Int) (C1 Bool) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) ) 
    (=>
      (and
        (main@.preheader Q A B Z C E D1 D)
        (let ((a!1 (or (not H) (not (= (<= 32 P) I))))
      (a!2 (or (not M1) (not (= (<= 2 I1) J1))))
      (a!3 (or (not M1) (= H1 (+ F1 (* (- 1) G1)))))
      (a!4 (or (not A1) (not (= (<= Z 0) Y)))))
  (and (= F (+ D1 Q))
       (not (<= D1 0))
       (or (not J) (not I) (not H))
       (or (not M1) (not (<= E1 0)) (<= D1 0))
       (or (not P1) (not M1) (= N1 L1))
       (or (not P1) (not M1) (= O1 N1))
       (or (not P1) (not M1) (not K1))
       (or (not S) (and N M) (and K J))
       (or (not L) (not K) (not J))
       (or (not M) I (not H))
       (or (not O) (not N) (not M))
       (or (= B1 Z) (not A1) (not M1))
       (or (= F1 B1) (not A1) (not M1))
       (or (not A1) (not S) (= T Q))
       (or (not A1) (not S) (= R P))
       (or (not A1) (not S) (= U R))
       (or (not A1) (not S) (= X T))
       (or (not Y) (not A1) (not M1))
       (or (not (<= F 0)) (<= D1 0))
       a!1
       (or (not H) (and G H))
       (or (not J) (= L (= P 32)))
       (or (not J) (and J H))
       (or (not K) J)
       a!2
       (or (not M1) (not (= J1 L1)))
       (or (not M1) (= C1 (= F1 G1)))
       (or (not M1) (= E1 (+ D1 G1)))
       a!3
       (or (not M1) (= I1 (+ 1 H1)))
       (or (not M1) (and A1 M1))
       (or (not P1) (and P1 M1))
       (or (not P1) O1)
       (or (not Q1) (and Q1 P1))
       (or (not M) (= O (= P 9)))
       (or (not M) (and M H))
       (or (not N) M)
       a!4
       (or (not A1) (= V (= U 34)))
       (or (not A1) (= G1 (+ W X)))
       (or (not A1) (= W (ite V 1 0)))
       (or (not A1) (and A1 S))
       (or C1 (not M1))
       (= Q1 true)
       (= P (select E F))))
      )
      main@precall4.split
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Int) (O Bool) (P Int) (Q Int) (R Bool) (S Int) (T Int) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Int) (B1 Bool) (C1 Int) (D1 Bool) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Bool) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) ) 
    (=>
      (and
        (main@.lr.ph A B C D F M1 E P1 A1)
        (let ((a!1 (or (not I) (not (= (<= 32 M) J))))
      (a!2 (or (not V1) (not (= (<= 2 R1) S1))))
      (a!3 (or (not V1) (= Q1 (+ O1 (* (- 1) P1)))))
      (a!4 (or (not D1) (not (= (<= A1 1) B1)))))
  (and (= G (+ M1 A1))
       (not (<= M1 0))
       (or (not O) (and X L) (and U K))
       (or (not V1) (not (<= N1 0)) (<= M1 0))
       (or (not V1) (and J1 V1) (and H1 V1))
       (or (not Y1) (not V1) (= W1 U1))
       (or (not Y1) (not V1) (= X1 W1))
       (or (not Y1) (not V1) (not T1))
       (or (not U) (not J) (not I))
       (or (not W) (not U) (not K))
       (or (not V) W (not U))
       (or (not X) (not Z) (not L))
       (or (not X) Z (not Y))
       (or (not X) J (not I))
       (or (not D1) (and X Y) (and V U))
       (or (= I1 F1) (not H1) (not V1))
       (or (not H1) (= O1 I1) (not V1))
       (or (not H1) (not D1) (= E1 C1))
       (or (not H1) (not D1) (= F1 E1))
       (or (not H1) (not D1) (not B1))
       (or (not J1) (not O) (= Q N))
       (or (not J1) (not O) (= N M))
       (or (not J1) (not O) (= P A1))
       (or (not J1) (not O) (= T P))
       (or (= K1 G1) (not J1) (not V1))
       (or (= O1 K1) (not J1) (not V1))
       (or (not (<= G 0)) (<= M1 0))
       a!1
       (or (not I) (and H I))
       a!2
       (or (not V1) (not (= S1 U1)))
       (or (not V1) (= L1 (= O1 P1)))
       (or (not V1) (= N1 (+ M1 P1)))
       a!3
       (or (not V1) (= R1 (+ 1 Q1)))
       (or (not Y1) (and Y1 V1))
       (or (not Y1) X1)
       (or (not Z1) (and Z1 Y1))
       (or (not U) (= W (= M 32)))
       (or (not U) (and U I))
       (or U (not K))
       (or (not V) U)
       (or (not X) (= Z (= M 9)))
       (or (not X) (and X I))
       (or X (not L))
       (or X (not Y))
       a!4
       (or (not D1) (= C1 (+ (- 1) A1)))
       (or (not H1) (and H1 D1))
       (or (not J1) (= R (= Q 34)))
       (or (not J1) (= S (ite R (- 1) 0)))
       (or (not J1) (= G1 (+ S T)))
       (or (not J1) (and J1 O))
       (or L1 (not V1))
       (= Z1 true)
       (= M (select F G))))
      )
      main@precall4.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@precall4.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
