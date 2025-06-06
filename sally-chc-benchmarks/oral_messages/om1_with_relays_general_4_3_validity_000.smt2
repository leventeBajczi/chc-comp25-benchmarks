(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) ) 
    (=>
      (and
        (and (= S1 0.0)
     (= F1 0.0)
     (= E1 0.0)
     (= D1 0.0)
     (= C1 0.0)
     (= B1 0.0)
     (= A1 0.0)
     (= Z 0.0)
     (= Y 0.0)
     (= X 0.0)
     (= W 0.0)
     (= V 0.0)
     (= U 0.0)
     (= T 0.0)
     (= S 0.0)
     (= R 0.0)
     (= Q 0.0)
     (= P 0.0)
     (= O 0.0)
     (= N 0.0)
     (= M 0.0)
     (= L 0.0)
     (= K 0.0)
     (= J 0.0)
     (= I 0.0)
     (= H 0.0)
     (= G 0.0)
     (= F 0.0)
     (= E 0.0)
     (= D 0.0)
     (= C 0.0)
     (= B 0.0)
     (= A 0.0)
     (or (= T1 1.0) (= T1 2.0) (= T1 3.0) (= T1 4.0))
     (or (and (not K1) L1 M1 N1)
         (and K1 (not L1) M1 N1)
         (and K1 L1 (not M1) N1)
         (and K1 L1 M1 (not N1)))
     (= J1 true)
     (= I1 true)
     (= H1 true)
     (= G1 true)
     (not (= U1 0.0)))
      )
      (invariant A
           B
           C
           D
           E
           F
           G
           H
           I
           J
           K
           L
           M
           N
           O
           P
           Q
           R
           S
           T
           U
           V
           W
           X
           Y
           Z
           A1
           B1
           C1
           D1
           E1
           F1
           G1
           H1
           I1
           J1
           K1
           L1
           M1
           N1
           O1
           P1
           Q1
           R1
           S1
           T1
           U1)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) ) 
    (=>
      (and
        (invariant A
           C
           E
           G
           I
           K
           M
           O
           Q
           S
           U
           W
           Y
           A1
           C1
           E1
           G1
           I1
           K1
           M1
           O1
           Q1
           S1
           U1
           W1
           Y1
           A2
           C2
           E2
           G2
           I2
           K2
           M2
           O2
           Q2
           S2
           U2
           W2
           Y2
           A3
           C3
           E3
           G3
           I3
           K3
           M3
           O3)
        (let ((a!1 (ite (= M3 4.0) Y (ite (= M3 3.0) Q (ite (= M3 2.0) I A))))
      (a!2 (ite (= M3 4.0) A1 (ite (= M3 3.0) S (ite (= M3 2.0) K C))))
      (a!3 (ite (= M3 4.0) C1 (ite (= M3 3.0) U (ite (= M3 2.0) M E))))
      (a!4 (and (or (not M2) (and (= B O3) (= D O3) (= F O3)) (not (= 1.0 M3)))
                (or (not M2) (= 1.0 M3) (and (= B 0.0) (= D 0.0) (= F 0.0)))
                (or (not O2) (and (= J O3) (= L O3) (= N O3)) (not (= 2.0 M3)))
                (or (not O2) (= 2.0 M3) (and (= J 0.0) (= L 0.0) (= N 0.0)))
                (or (not Q2) (and (= R O3) (= T O3) (= V O3)) (not (= 3.0 M3)))
                (or (not Q2) (= 3.0 M3) (and (= R 0.0) (= T 0.0) (= V 0.0)))
                (or (not S2)
                    (and (= Z O3) (= B1 O3) (= D1 O3))
                    (not (= 4.0 M3)))
                (or (not S2) (= 4.0 M3) (and (= Z 0.0) (= B1 0.0) (= D1 0.0)))
                (= X1 W1)
                (= Z1 Y1)
                (= B2 A2)
                (= F2 E2)
                (= H2 G2)
                (= J2 I2)
                (= J3 I3)
                (= K3 0.0)
                (= L3 1.0)
                (= H1 G1)
                (= J1 I1)
                (= L1 K1)
                (= P1 O1)
                (= R1 Q1)
                (= T1 S1)
                (= D3 C3)
                (= F3 E3)
                (= H3 G3)
                (= N2 M2)
                (= P2 O2)
                (= R2 Q2)
                (= T2 S2)
                (= V2 U2)
                (= X2 W2)
                (= Z2 Y2)))
      (a!5 (and (= I1 (ite (= I1 K1) K1 G1)) (= K1 (ite (= I1 K1) K1 G1))))
      (a!6 (= (= K1 (ite (= I1 K1) K1 G1)) (= I1 (ite (= I1 K1) K1 G1))))
      (a!9 (and (= Q1 (ite (= Q1 S1) S1 O1)) (= S1 (ite (= Q1 S1) S1 O1))))
      (a!10 (= (= S1 (ite (= Q1 S1) S1 O1)) (= Q1 (ite (= Q1 S1) S1 O1))))
      (a!13 (and (= Y1 (ite (= Y1 A2) A2 W1)) (= A2 (ite (= Y1 A2) A2 W1))))
      (a!14 (= (= A2 (ite (= Y1 A2) A2 W1)) (= Y1 (ite (= Y1 A2) A2 W1))))
      (a!17 (and (= G2 (ite (= G2 I2) I2 E2)) (= I2 (ite (= G2 I2) I2 E2))))
      (a!18 (= (= I2 (ite (= G2 I2) I2 E2)) (= G2 (ite (= G2 I2) I2 E2)))))
(let ((a!7 (ite (= G1 (ite (= I1 K1) K1 G1)) (not a!6) a!5))
      (a!11 (ite (= O1 (ite (= Q1 S1) S1 O1)) (not a!10) a!9))
      (a!15 (ite (= W1 (ite (= Y1 A2) A2 W1)) (not a!14) a!13))
      (a!19 (ite (= E2 (ite (= G2 I2) I2 E2)) (not a!18) a!17)))
(let ((a!8 (= D3 (ite (or a!5 a!7) (ite (= I1 K1) K1 G1) 0.0)))
      (a!12 (= F3 (ite (or a!9 a!11) (ite (= Q1 S1) S1 O1) 0.0)))
      (a!16 (= H3 (ite (or a!13 a!15) (ite (= Y1 A2) A2 W1) 0.0)))
      (a!20 (= J3 (ite (or a!17 a!19) (ite (= G2 I2) I2 E2) 0.0))))
(let ((a!21 (or (and (or (not U2) (= X1 a!1))
                     (or (not U2) (= F2 a!1))
                     (or (not U2) (= H1 a!1))
                     (or (not U2) (= P1 a!1))
                     (or (not W2) (= Z1 a!2))
                     (or (not W2) (= H2 a!2))
                     (or (not W2) (= J1 a!2))
                     (or (not W2) (= R1 a!2))
                     (or (not Y2) (= B2 a!3))
                     (or (not Y2) (= J2 a!3))
                     (or (not Y2) (= L1 a!3))
                     (or (not Y2) (= T1 a!3))
                     (= J3 I3)
                     (= K3 1.0)
                     (= L3 2.0)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= D3 C3)
                     (= F3 E3)
                     (= H3 G3)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)
                     (= Z2 Y2))
                (and (= X1 W1)
                     (= Z1 Y1)
                     (= B2 A2)
                     (= F2 E2)
                     (= H2 G2)
                     (= J2 I2)
                     (= J3 I3)
                     (= K3 3.0)
                     (= L3 K3)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= D3 C3)
                     (= F3 E3)
                     (= H3 G3)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)
                     (= Z2 Y2))
                a!4
                (and (or (not M2) a!8)
                     (or (not O2) a!12)
                     (or (not Q2) a!16)
                     (or (not S2) a!20)
                     (= X1 W1)
                     (= Z1 Y1)
                     (= B2 A2)
                     (= F2 E2)
                     (= H2 G2)
                     (= J2 I2)
                     (= K3 2.0)
                     (= L3 3.0)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)
                     (= Z2 Y2)))))
  (and (= N3 M3) a!21 (= P3 O3))))))
      )
      (invariant B
           D
           F
           H
           J
           L
           N
           P
           R
           T
           V
           X
           Z
           B1
           D1
           F1
           H1
           J1
           L1
           N1
           P1
           R1
           T1
           V1
           X1
           Z1
           B2
           D2
           F2
           H2
           J2
           L2
           N2
           P2
           R2
           T2
           V2
           X2
           Z2
           B3
           D3
           F3
           H3
           J3
           L3
           N3
           P3)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) ) 
    (=>
      (and
        (invariant A
           B
           C
           D
           E
           F
           G
           H
           I
           J
           K
           L
           M
           N
           O
           P
           Q
           R
           S
           T
           U
           V
           W
           X
           Y
           Z
           A1
           B1
           C1
           D1
           E1
           F1
           G1
           H1
           I1
           J1
           K1
           L1
           M1
           N1
           O1
           P1
           Q1
           R1
           S1
           T1
           U1)
        (let ((a!1 (or (and G1 (not (= O1 U1)))
               (and H1 (not (= P1 U1)))
               (and I1 (not (= Q1 U1)))
               (and J1 (not (= R1 U1)))))
      (a!2 (ite (= T1 4.0) J1 (ite (= T1 3.0) I1 (ite (= T1 2.0) H1 G1)))))
  (and (<= 3.0 S1) a!1 a!2))
      )
      false
    )
  )
)

(check-sat)
(exit)
