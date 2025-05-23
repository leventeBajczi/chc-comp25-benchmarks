(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool) (O Int) (P Bool) ) 
    (=>
      (and
        (and (= L 10)
     (or (not P) (not A) (not B))
     (or (not E) (not D) (not C))
     (or (not M) (not N))
     (or (not J) (not K))
     (not C)
     (not B)
     (not A)
     (not P)
     (not N)
     (not M)
     (not K)
     (not J)
     (not D)
     (not E)
     (= O 10))
      )
      (state K J N M B P A D C E O L G I F H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Bool) (L Bool) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Int) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Bool) ) 
    (=>
      (and
        (state M1 L1 P1 O1 B R1 A D C E Q1 N1 M D1 J C1)
        (let ((a!1 (and (not K1)
                J1
                (not I1)
                W
                (not L)
                (not K)
                (= (+ D1 (* (- 1) E1)) (- 1))))
      (a!2 (and K1 (not J1) I1 W (not L) (not K) (= (+ M (* (- 1) N)) (- 1))))
      (a!3 (and (not H1)
                G1
                (not F1)
                X
                (not G)
                (not F)
                (= (+ C1 (* (- 1) B1)) (- 5))))
      (a!4 (and H1 (not G1) F1 X (not G) (not F) (= (+ J (* (- 1) H)) 6)))
      (a!5 (or (and S (not P) (not O))
               (and (or (not U) (not T))
                    (or (not X) G F)
                    (or X G (not F))
                    (or X G F)
                    (or (not W) L K)
                    (or W L (not K))
                    (or W L K)
                    (or V U T)
                    (= U T))))
      (a!6 (or (and V (not U) (not T))
               (and (or (not P) (not O))
                    (or (not L) (not K))
                    (or (not L) K)
                    (or (not G) (not F))
                    (or (not G) F)
                    (or (not X) G F)
                    (or (not W) L K)
                    (or S P O)
                    (= P O))))
      (a!7 (or (and W (not L) K)
               (and (or (not U) (not T))
                    (or U (not T))
                    (or (not P) (not O))
                    (or P (not O))
                    (or (not G) (not F))
                    (or (not G) F)
                    (or (not X) G F)
                    (or X G (not F))
                    (or X G F))))
      (a!8 (or (and X (not G) F)
               (and (or (not U) T)
                    (or (not P) O)
                    (or (not L) (not K))
                    (or (not L) K)
                    (or (not W) L K)
                    (or W L (not K))
                    (or W L K)
                    (or V U T)
                    (or S P O)))))
  (and (= (and (not W) (not L) (not K)) (and (not V) (not U) (not T)))
       (= (and (not X) (not G) F) (and U T))
       (= (and (not X) (not G) (not F)) (and (not U) T))
       (= (and G F) (and P O))
       (= (and G (not F)) (and (not P) O))
       (= (and L K) (and P (not O)))
       (= (and L (not K)) (and (not S) (not P) (not O)))
       (or S P O (and Q (not L1) (not M1) (= N1 I)) (and S (not P) (not O)))
       (or V U T (and V (not U) (not T)) (and Y (not O1) (not P1) (= Q1 A1)))
       (or C D (not E) (and W (not L) K) a!1)
       (or C E (not D) (and W (not L) K) a!2)
       (or C
           D
           E
           (and W (not L) K)
           (and K1 (not J1) (not I1) (not W) (not L) (not K)))
       (or E
           (not C)
           (not D)
           (and W (not L) K)
           (and (not K1) J1 I1 W (not L) (not K)))
       (or D E (not C) (and W (not L) K) (and K1 J1 (not W) (not L) K))
       (or C (not D) (not E) (and W (not L) K) (and (not K1) J1 I1 L K))
       (or B R1 (not A) (and X (not G) F) a!3)
       (or A R1 (not B) (and X (not G) F) a!4)
       (or A
           B
           R1
           (and X (not G) F)
           (and H1 (not G1) (not F1) (not X) (not G) (not F)))
       (or A
           (not R1)
           (not B)
           (and X (not G) F)
           (and (not H1) G1 F1 X (not G) (not F)))
       (or A B (not R1) (and X (not G) F) (and H1 G1 (not X) (not G) F))
       (or R1 (not B) (not A) (and X (not G) F) (and (not H1) G1 F1 G F))
       (or P
           (not O)
           (and S (not P) (not O))
           (and R (not Q) (not L1) (not M1) (= N1 I)))
       (or (not P)
           (not O)
           (and S (not P) (not O))
           (and (not R) (not Q) L1 (not M1)))
       (or O (not P) (and S (not P) (not O)) (and (not R) (not Q) M1))
       (or P O (not S) (and (= N1 I) (= L1 R) (= M1 Q)))
       (or U
           (not T)
           (and V (not U) (not T))
           (and Z (not Y) (not O1) (not P1) (= Q1 A1)))
       (or (not U)
           (not T)
           (and V (not U) (not T))
           (and (not Z) (not Y) (not O1) P1))
       (or T (not U) (and V (not U) (not T)) (and (not Z) (not Y) O1))
       (or U T (not V) (and (= Q1 A1) (= O1 Y) (= P1 Z)))
       (or W L K (= Q1 E1))
       (or W L (not K) (= D1 A1))
       (or L (not K) (not W) (and (= M N) (= D1 E1) (= C J1) (= D I1) (= E K1)))
       (or X G F (= Q1 B1))
       (or X G (not F) (= C1 A1))
       (or G
           (not F)
           (not X)
           (and (= J H) (= C1 B1) (= A H1) (= B F1) (= R1 G1)))
       (or (not C)
           (not E)
           (and W (not L) K)
           (and (not K1) (not J1) I1 L (not K)))
       (or (not R1)
           (not A)
           (and (not H1) (not G1) F1 G (not F))
           (and X (not G) F))
       (or F (= N1 H) (not G))
       (or (not G) (not F) (= J I))
       (or K (= N1 N) (not L))
       (or (not L) (not K) (= M I))
       (or P (not O) (not S))
       (or U (not T) (not V))
       (or (not H1) (not G1) (not F1))
       (or (not K1) (not J1) (not I1))
       (or (not C) (not D) (not E))
       (or (not R1) (not B) (not A))
       a!5
       a!6
       a!7
       a!8
       (or (not O1) (not P1))
       (or (not L1) (not M1))
       (or (not R) (not Q))
       (or (not S) (not P))
       (or (not V) (not U))
       (or (not W) (not L))
       (or (not X) (not G))
       (or (not Z) (not Y))
       (= (and (not W) (not L) K) (and U (not T)))))
      )
      (state Q R Z Y F1 G1 H1 I1 J1 K1 A1 I N E1 H B1)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool) (O Int) (P Bool) ) 
    (=>
      (and
        (state K J N M B P A D C E O L G I F H)
        (and (not (= L 5))
     (= C true)
     (= B true)
     (not A)
     (= P true)
     (= D true)
     (not E)
     (not (= O 16)))
      )
      false
    )
  )
)

(check-sat)
(exit)
