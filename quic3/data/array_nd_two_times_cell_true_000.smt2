(set-logic HORN)


(declare-fun |main@bb12.i| ( Int (Array Int Int) (Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@entry| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        true
      )
      (main@entry A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C (Array Int Int)) (D (Array Int Int)) (E (Array Int Int)) (F (Array Int Int)) (G Bool) (H Bool) (I Int) (J Int) (K (Array Int Int)) (L (Array Int Int)) (M Int) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (main@entry O Q)
        (and (= A Q)
     (not (<= M 0))
     (not (<= N 0))
     (or (not H) (not G) (= E C))
     (or (not H) (not G) (= F D))
     (or (not H) (not G) (= K E))
     (or (not H) (not G) (= L F))
     (or (not H) (not G) (= I 0))
     (or (not H) (not G) (= J I))
     (or (not G) (and H G))
     (= B true)
     (= G true)
     (not (= (<= P 0) B)))
      )
      (main@bb12.i J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Int) (R Int) (S Int) (T Int) (U (Array Int Int)) (V Int) (W Int) (X (Array Int Int)) (Y (Array Int Int)) (Z Bool) (A1 (Array Int Int)) (B1 Bool) (C1 (Array Int Int)) (D1 Int) (E1 (Array Int Int)) (F1 (Array Int Int)) (G1 Int) (H1 (Array Int Int)) (I1 (Array Int Int)) (J1 Bool) (K1 Bool) (L1 Int) (M1 Int) (N1 (Array Int Int)) (O1 (Array Int Int)) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) ) 
    (=>
      (and
        (main@bb12.i D1 U H P1 Q1 R1 S1 T1)
        (and (= A D1)
     (= B T1)
     (or (not N) (not (<= I 0)) (<= P1 0))
     (or (not (<= L 0)) (not N) (<= P1 0))
     (or (not C) (not N) D)
     (or (not (<= Q 0)) (not Z) (<= P1 0))
     (or (not (<= V 0)) (not Z) (<= Q1 0))
     (or (not Z) (not N) O)
     (or (not (<= M 0)) (not B1) (<= Q1 0))
     (or (not B1) (not O) (not N))
     (or (not K1) (and K1 B1) (and K1 Z))
     (or (not K1) (not Z) (= A1 X))
     (or (not K1) (not Z) (= E1 A1))
     (or (not K1) (not B1) (= C1 Y))
     (or (not K1) (not B1) (= E1 C1))
     (or (not K1) (not J1) (= H1 E1))
     (or (not K1) (not J1) (= I1 F1))
     (or (not K1) (not J1) (= N1 H1))
     (or (not K1) (not J1) (= O1 I1))
     (or (not K1) (not J1) (= L1 G1))
     (or (not K1) (not J1) (= M1 L1))
     (or (not N) (= F1 (store H I J)))
     (or (not N) (= O (= E 0)))
     (or (not N) (= F R1))
     (or (not N) (= G D1))
     (or (not N) (= I (+ P1 G)))
     (or (not N) (= K D1))
     (or (not N) (= L (+ P1 K)))
     (or (not N) (= P D1))
     (or (not N) (= R (select F1 L)))
     (or (not N) (not (<= P1 0)))
     (or (not N) (and N C))
     (or (not Z) (= X (store U V W)))
     (or (not Z) (= Q (+ P1 P)))
     (or (not Z) (= S (select F1 Q)))
     (or (not Z) (= T D1))
     (or (not Z) (= V (+ Q1 T)))
     (or (not Z) (= W (+ R S)))
     (or (not Z) (not (<= P1 0)))
     (or (not Z) (not (<= Q1 0)))
     (or (not Z) (and Z N))
     (or (not B1) (= Y (store U M R)))
     (or (not B1) (= M (+ Q1 P)))
     (or (not B1) (not (<= Q1 0)))
     (or (not B1) (and B1 N))
     (or (not J1) (and K1 J1))
     (or (not K1) (= G1 (+ 1 D1)))
     (= J1 true)
     (not (= (<= S1 A) D)))
      )
      (main@bb12.i M1 N1 O1 P1 Q1 R1 S1 T1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Bool) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T (Array Int Int)) (U Int) (V Int) (W Int) (X Int) (Y (Array Int Int)) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) ) 
    (=>
      (and
        (main@bb12.i B T Y X S A H E)
        (let ((a!1 (or (not L) (not (= (<= H W) J))))
      (a!2 (or (not L) (not (= (<= W (- 1)) I)))))
  (and (= D E)
       (= C B)
       (or (not L) (not G) (not F))
       (or (not R) (<= S 0) (not (<= N 0)))
       (or (not R) (not (<= M 0)) (<= X 0))
       (or (not G1) (not (<= U 0)) (<= S 0))
       (or (not G1) (not (<= Z 0)) (<= X 0))
       a!1
       a!2
       (or (not L) (= K (and J I)))
       (or (not L) (and L F))
       (or (not L) K)
       (or (not R) (= Q (= O P)))
       (or (not R) (= N (+ S W)))
       (or (not R) (= O (select Y M)))
       (or (not R) (= P (select T N)))
       (or (not R) (= M (+ X W)))
       (or (not R) (not (<= S 0)))
       (or (not R) (not (<= X 0)))
       (or (not R) (and R L))
       (or (not R) (not Q))
       (or (not G1) (= F1 (= D1 E1)))
       (or (not G1) (= U (+ S W)))
       (or (not G1) (= V (select T U)))
       (or (not G1) (= Z (+ X W)))
       (or (not G1) (= A1 (select Y Z)))
       (or (not G1) (= D1 V))
       (or (not G1) (= E1 (+ B1 C1)))
       (or (not G1) (= B1 A1))
       (or (not G1) (= C1 A1))
       (or (not G1) (not (<= S 0)))
       (or (not G1) (not (<= X 0)))
       (or (not G1) (and G1 R))
       (or (not G1) (not F1))
       (or (not H1) (and H1 G1))
       (or (not I1) (and I1 H1))
       (or (not J1) (and J1 I1))
       (= J1 true)
       (not (= (<= H C) G))))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
