(set-logic HORN)


(declare-fun |main@.preheader| ( Int (Array Int Int) Int (Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun |main@precall.split| ( ) Bool)
(declare-fun |main@.lr.ph| ( Int (Array Int Int) Int (Array Int Int) Int Int Int Int Int Int ) Bool)
(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@_bb| ( Int (Array Int Int) Int (Array Int Int) Int Int Int Int ) Bool)

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
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q (Array Int Int)) (R Int) (S Int) (T Bool) (U Int) (V (Array Int Int)) (W Int) (X Int) (Y (Array Int Int)) (Z Int) (A1 Int) (B1 Int) (C1 (Array Int Int)) (D1 Int) (E1 Int) (F1 Int) (G1 (Array Int Int)) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 (Array Int Int)) (M1 Int) (N1 Int) (O1 Bool) (P1 Int) (Q1 Bool) (R1 Bool) (S1 Int) (T1 Int) (U1 (Array Int Int)) (V1 Int) (W1 (Array Int Int)) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) ) 
    (=>
      (and
        (main@entry K1)
        (and (= O1 (= N1 0))
     (= E (store B C Y1))
     (= I (store E F G))
     (= M (store I J K))
     (= Q (store M N O))
     (= Y (store V W X1))
     (= C1 (store Y Z A1))
     (= G1 (store C1 D1 E1))
     (= L1 (store G1 H1 I1))
     (= U1 (store Q R S))
     (= W1 (store L1 M1 N1))
     (= A K1)
     (= C T1)
     (= D K1)
     (= F (+ 1 T1))
     (= H K1)
     (= J (+ 2 T1))
     (= L K1)
     (= N (+ 3 T1))
     (= P K1)
     (= R (+ 4 T1))
     (= U K1)
     (= W V1)
     (= X K1)
     (= Z (+ 1 V1))
     (= B1 K1)
     (= D1 (+ 2 V1))
     (= F1 K1)
     (= H1 (+ 3 V1))
     (= J1 K1)
     (= M1 (+ 4 V1))
     (not (<= T1 0))
     (not (<= V1 0))
     (or (not R1) (not Q1) (= P1 Y1))
     (or (not R1) (not Q1) (= S1 0))
     (or (not R1) (not Q1) (= Z1 P1))
     (or (not R1) (not Q1) (= A2 S1))
     (or (not (<= C 0)) (<= T1 0))
     (or (not (<= F 0)) (<= T1 0))
     (or (not (<= J 0)) (<= T1 0))
     (or (not (<= N 0)) (<= T1 0))
     (or (not (<= R 0)) (<= T1 0))
     (or (not (<= W 0)) (<= V1 0))
     (or (not (<= Z 0)) (<= V1 0))
     (or (not (<= D1 0)) (<= V1 0))
     (or (not (<= H1 0)) (<= V1 0))
     (or (not (<= M1 0)) (<= V1 0))
     (or (not Q1) (and R1 Q1))
     (= T true)
     (= O1 true)
     (= Q1 true)
     (= T (= S 0)))
      )
      (main@_bb T1 U1 V1 W1 X1 Y1 Z1 A2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Int) (L Int) (M (Array Int Int)) (N Int) (O (Array Int Int)) (P Int) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (main@_bb L M N O P Q A B)
        (and (= G (+ 1 B))
     (or (not J) (not (<= E 0)) (<= L 0))
     (or (not J) (not I) (= H F))
     (or (not J) (not I) (= K G))
     (or (not J) (not I) (= R H))
     (or (not J) (not I) (= S K))
     (or (not J) (not D) (not C))
     (or (not I) (and J I))
     (or (not J) (= E (+ L G)))
     (or (not J) (= F (select M E)))
     (or (not J) (not (<= L 0)))
     (or (not J) (and C J))
     (= I true)
     (= D (= A 0)))
      )
      (main@_bb L M N O P Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Bool) (F Int) (G Int) (H Bool) (I Bool) (J Int) (K Int) (L (Array Int Int)) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (main@_bb K L M N P Q A D)
        (and (= B (+ 1 D))
     (or (not E) (not I) (= F D))
     (or (not E) (not I) (= O F))
     (or (not E) (not I) C)
     (or (not H) (not I) (= R G))
     (or (not H) (not I) (= G P))
     (or (not H) (not I) (= J 0))
     (or (not H) (not I) (= S J))
     (or (not I) (and E I))
     (or (not H) (and H I))
     (= H true)
     (= C (= A 0)))
      )
      (main@.preheader K L M N O P Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Int) (L Int) (M (Array Int Int)) (N Int) (O (Array Int Int)) (P Int) (Q Int) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (main@.preheader L M N O P Q R A B)
        (and (= G (+ 1 B))
     (or (not J) (not (<= E 0)) (<= N 0))
     (or (not J) (not C) (not D))
     (or (not I) (not J) (= S H))
     (or (not I) (not J) (= H F))
     (or (not I) (not J) (= K G))
     (or (not I) (not J) (= T K))
     (or (not J) (= F (select O E)))
     (or (not J) (= E (+ N G)))
     (or (not J) (not (<= N 0)))
     (or (not J) (and J C))
     (or (not I) (and I J))
     (= I true)
     (= D (= A 0)))
      )
      (main@.preheader L M N O P Q R S T)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Bool) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U (Array Int Int)) (V Int) (W (Array Int Int)) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) ) 
    (=>
      (and
        (main@.preheader T U V W C1 L M A D)
        (let ((a!1 (or (not J) (not (= (<= B1 0) H))))
      (a!2 (or (not J) (not (= (<= C1 0) I))))
      (a!3 (or (not J) (not (= (<= C1 B1) G)))))
  (and (= B (+ 1 D))
       (or (not J) (not E) (= F D))
       (or (not J) (not E) (= B1 F))
       (or (not J) (not E) C)
       (or (not R) K (not J))
       (or (not R) (not Q) (= S 0))
       (or (not R) (not Q) (= O M))
       (or (not R) (not Q) (= P 0))
       (or (not R) (not Q) (= X N))
       (or (not R) (not Q) (= Z P))
       (or (not R) (not Q) (= A1 S))
       (or (not R) (not Q) (= N L))
       (or (not R) (not Q) (= Y O))
       a!1
       a!2
       a!3
       (or (not J) (= K (and I H)))
       (or (not J) (and J E))
       (or (not J) (not G))
       (or (not Q) (and R Q))
       (or (not R) (and R J))
       (= Q true)
       (= C (= A 0))))
      )
      (main@.lr.ph T U V W X Y Z A1 B1 C1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Bool) (X Bool) (Y Int) (Z Int) (A1 (Array Int Int)) (B1 Int) (C1 (Array Int Int)) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) ) 
    (=>
      (and
        (main@.lr.ph Z A1 B1 C1 B A G D H1 I1)
        (and (not (= (<= I1 R) K))
     (= E (= A B))
     (= M (and K J))
     (= C (+ 1 D))
     (= F (* (- 1) D))
     (= H (+ 1 G))
     (= I (ite E 0 F))
     (= R (+ H I))
     (= S (ite E C 0))
     (or (not X) (<= B1 0) (not (<= O 0)))
     (or (not X) (<= Z 0) (not (<= N 0)))
     (or (not X) M (not L))
     (or (not X) (not W) (= Y S))
     (or (not X) (not W) (= U Q))
     (or (not X) (not W) (= V R))
     (or (not X) (not W) (= D1 T))
     (or (not X) (not W) (= F1 V))
     (or (not X) (not W) (= G1 Y))
     (or (not X) (not W) (= T P))
     (or (not X) (not W) (= E1 U))
     (or (not W) (and X W))
     (or (not X) (= O (+ B1 S)))
     (or (not X) (= N (+ Z R)))
     (or (not X) (= P (select C1 O)))
     (or (not X) (= Q (select A1 N)))
     (or (not X) (not (<= B1 0)))
     (or (not X) (not (<= Z 0)))
     (or (not X) (and X L))
     (= W true)
     (not (= (<= H1 S) J)))
      )
      (main@.lr.ph Z A1 B1 C1 D1 E1 F1 G1 H1 I1)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Int) (K Bool) (L Int) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Bool) (Z Int) (A1 Int) (B1 Int) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) ) 
    (=>
      (and
        (main@.preheader A B C D N E F G J)
        (let ((a!1 (or (not T) (not (= (<= N 0) P))))
      (a!2 (or (not T) (not (= (<= N V) M))))
      (a!3 (or (not T) (not (= (<= V 0) O))))
      (a!4 (or (not F1) (not (= (<= W X) Y))))
      (a!5 (and (or (not (= A1 0)) (= B1 0)) (or (= B1 0) (not (= Z 0))))))
  (and (= H (+ 1 J))
       (or (not F1) (not T) (= W U))
       (or (not F1) (not T) (= S 0))
       (or (not F1) (not T) (= R S))
       (or (not F1) (not T) (= U 0))
       (or (not K) (= L J) (not T))
       (or (not K) (= V L) (not T))
       (or (not K) I (not T))
       (or (not Q) (not F1) (not T))
       a!1
       a!2
       a!3
       (or (not T) (= Q (and P O)))
       (or (not T) (and K T))
       a!4
       (or (not F1) (= D1 (= B1 0)))
       (or (not F1) (not (= D1 E1)))
       (or (not F1) (= Z (ite Y 1 0)))
       (or (not F1) (= X (+ (- 1) V)))
       (or (not F1) a!5)
       (or (not F1) (and F1 T))
       (or (not F1) (not C1))
       (or (not F1) E1)
       (or (not G1) (and G1 F1))
       (or (not M) (not T))
       (= G1 true)
       (= I (= G 0))))
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Bool) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Int) (H1 Int) (I1 Int) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) ) 
    (=>
      (and
        (main@.lr.ph A B C D F E K H C1 N)
        (let ((a!1 (or (not M1) (not (= (<= D1 E1) F1))))
      (a!2 (and (or (not (= H1 0)) (= I1 0)) (or (= I1 0) (not (= G1 0))))))
  (and (not (= (<= C1 S) O))
       (= I (= E F))
       (= Q (and P O))
       (= G (+ 1 H))
       (= L (+ 1 K))
       (= J (* (- 1) H))
       (= M (ite I 0 J))
       (= R (+ L M))
       (= S (ite I G 0))
       (or (not M1) (not A1) (= D1 B1))
       (or (not M1) (not A1) (= Z W))
       (or (not M1) (not A1) (= Y Z))
       (or (not M1) (not A1) (= B1 X))
       (or (not U) (= T R) (not A1))
       (or (not U) (= V S) (not A1))
       (or (not U) (= W T) (not A1))
       (or (not U) (= X V) (not A1))
       (or (not U) (not Q) (not A1))
       (or (not A1) (and U A1))
       a!1
       (or (not M1) (= K1 (= I1 0)))
       (or (not M1) (not (= K1 L1)))
       (or (not M1) (= G1 (ite F1 1 0)))
       (or (not M1) (= E1 (+ (- 1) C1)))
       (or (not M1) a!2)
       (or (not M1) (and M1 A1))
       (or (not M1) (not J1))
       (or (not M1) L1)
       (or (not N1) (and N1 M1))
       (= N1 true)
       (not (= (<= N R) P))))
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@precall.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
