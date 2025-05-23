(set-logic HORN)


(declare-fun |state| ( Int Bool Int Int Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Int Bool Bool Int Bool Bool Bool Bool Int ) Bool)

(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Bool) (M Bool) (N Int) (O Int) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Bool) (V Int) (W Int) ) 
    (=>
      (and
        (let ((a!1 (= (and M L (or (<= K 4) (<= (- 4) K))) I))
      (a!2 (= Q (and P (<= 0 O) (not (<= 16 O))))))
  (and (= W 0)
       (= W N)
       (= R 0)
       (= O B)
       (= (<= 11 B) G)
       (= (<= B 9) D)
       (= (or (not H) A) F)
       a!1
       (= (and (<= O 12) (<= 8 O)) U)
       a!2
       (= Q H)
       (= D C)
       (= G E)
       (= I P)
       (= J A)
       (or (not U) (= V 0))
       (or (not T) (= L (<= K (- 1))))
       (or (not S) (= M (<= 1 K)))
       (or L T)
       (or M S)
       (not T)
       (= S true)
       (= J true)
       (= B R)))
      )
      (state O U W N J A Q H L T M S K I B G D R P E C F V)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Bool) (U Bool) (V Int) (W Bool) (X Int) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Int) (L1 Int) (M1 Bool) (N1 Bool) (O1 Int) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Int) (T1 Int) ) 
    (=>
      (and
        (state L1 R1 T1 N J A N1 H L Q1 M P1 K I B G D O1 M1 E C F S1)
        (let ((a!1 (= (and J1 I1 (or (<= P 4) (<= (- 4) P))) H1))
      (a!2 (= (and L M (or (<= K 4) (<= (- 4) K))) I))
      (a!3 (or H (and T (<= 0 S) (not (<= 16 S)))))
      (a!4 (or W (= (+ N (* (- 1) V)) (- 1)))))
  (and (= T1 N)
       (= L1 B)
       (= S C1)
       (= X V)
       (= C1 O)
       (= K1 X)
       (= B O1)
       (= (<= 11 C1) G1)
       (= (<= 11 B) G)
       (= (<= C1 9) E1)
       (= (<= B 9) D)
       (= (or B1 (not A1)) Z)
       (= (or A (not H)) F)
       a!1
       a!2
       (= (and (<= L1 12) (<= 8 L1)) R1)
       (= (and (<= S 12) (<= 8 S)) W)
       (= N1 H)
       (= U a!3)
       (= Y (<= N 7))
       (= A1 U)
       (= B1 Y)
       (= E1 D1)
       (= G1 F1)
       (= H1 T)
       (= J A)
       (= I M1)
       (= G E)
       (= E R)
       (= D C)
       (= C Q)
       (or (not Q1) (= L (<= K (- 1))))
       (or (not P1) (= M (<= 1 K)))
       (or (not Q) (= J1 (<= 1 P)))
       (or (not R) (= I1 (<= P (- 1))))
       a!4
       (or (not W) (= V 0))
       (or I1 R)
       (or J1 Q)
       (or M P1)
       (or L Q1)
       (= (+ B P (* (- 1) O)) 0)))
      )
      (state S W X K1 Y B1 U A1 I1 R J1 Q P H1 C1 G1 E1 O T F1 D1 Z V)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Bool) (M Bool) (N Int) (O Int) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Bool) (V Int) (W Int) ) 
    (=>
      (and
        (state O U W N J A Q H L T M S K I B G D R P E C F V)
        (not F)
      )
      false
    )
  )
)

(check-sat)
(exit)
