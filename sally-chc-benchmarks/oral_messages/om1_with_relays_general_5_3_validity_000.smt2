(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) ) 
    (=>
      (and
        (and (= R1 0.0)
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
     (or (= S1 1.0) (= S1 2.0) (= S1 3.0) (= S1 4.0) (= S1 5.0))
     (or (and (not J1) K1 L1) (and J1 (not K1) L1) (and J1 K1 (not L1)))
     (= I1 true)
     (= H1 true)
     (= G1 true)
     (= F1 true)
     (= E1 true)
     (not (= T1 0.0)))
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
           T1)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) ) 
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
           M3)
        (let ((a!1 (ite (= K3 4.0) S (ite (= K3 3.0) M (ite (= K3 2.0) G A))))
      (a!7 (ite (= K3 4.0) U (ite (= K3 3.0) O (ite (= K3 2.0) I C))))
      (a!13 (ite (= K3 4.0) W (ite (= K3 3.0) Q (ite (= K3 2.0) K E))))
      (a!19 (and (or (not I2) (and (= B M3) (= D M3) (= F M3)) (not (= 1.0 K3)))
                 (or (not I2) (= 1.0 K3) (and (= B 0.0) (= D 0.0) (= F 0.0)))
                 (or (not K2) (and (= H M3) (= J M3) (= L M3)) (not (= 2.0 K3)))
                 (or (not K2) (= 2.0 K3) (and (= H 0.0) (= J 0.0) (= L 0.0)))
                 (or (not M2) (and (= N M3) (= P M3) (= R M3)) (not (= 3.0 K3)))
                 (or (not M2) (= 3.0 K3) (and (= N 0.0) (= P 0.0) (= R 0.0)))
                 (or (not O2) (and (= T M3) (= V M3) (= X M3)) (not (= 4.0 K3)))
                 (or (not O2) (= 4.0 K3) (and (= T 0.0) (= V 0.0) (= X 0.0)))
                 (or (not Q2)
                     (and (= Z M3) (= B1 M3) (= D1 M3))
                     (not (= 5.0 K3)))
                 (or (not Q2) (= 5.0 K3) (and (= Z 0.0) (= B1 0.0) (= D1 0.0)))
                 (= V1 U1)
                 (= X1 W1)
                 (= Z1 Y1)
                 (= B2 A2)
                 (= D2 C2)
                 (= F2 E2)
                 (= H2 G2)
                 (= H3 G3)
                 (= I3 0.0)
                 (= J3 1.0)
                 (= F1 E1)
                 (= H1 G1)
                 (= J1 I1)
                 (= L1 K1)
                 (= N1 M1)
                 (= P1 O1)
                 (= R1 Q1)
                 (= T1 S1)
                 (= Z2 Y2)
                 (= B3 A3)
                 (= D3 C3)
                 (= F3 E3)
                 (= J2 I2)
                 (= L2 K2)
                 (= N2 M2)
                 (= P2 O2)
                 (= R2 Q2)
                 (= T2 S2)
                 (= V2 U2)
                 (= X2 W2)))
      (a!20 (and (= G1 (ite (= G1 I1) I1 E1)) (= I1 (ite (= G1 I1) I1 E1))))
      (a!21 (= (= I1 (ite (= G1 I1) I1 E1)) (= G1 (ite (= G1 I1) I1 E1))))
      (a!24 (and (= M1 (ite (= M1 O1) O1 K1)) (= O1 (ite (= M1 O1) O1 K1))))
      (a!25 (= (= O1 (ite (= M1 O1) O1 K1)) (= M1 (ite (= M1 O1) O1 K1))))
      (a!28 (and (= U1 (ite (= S1 U1) U1 Q1)) (= S1 (ite (= S1 U1) U1 Q1))))
      (a!29 (= (= U1 (ite (= S1 U1) U1 Q1)) (= S1 (ite (= S1 U1) U1 Q1))))
      (a!32 (and (= Y1 (ite (= Y1 A2) A2 W1)) (= A2 (ite (= Y1 A2) A2 W1))))
      (a!33 (= (= A2 (ite (= Y1 A2) A2 W1)) (= Y1 (ite (= Y1 A2) A2 W1))))
      (a!36 (and (= E2 (ite (= E2 G2) G2 C2)) (= G2 (ite (= E2 G2) G2 C2))))
      (a!37 (= (= G2 (ite (= E2 G2) G2 C2)) (= E2 (ite (= E2 G2) G2 C2)))))
(let ((a!2 (or (not S2) (= X1 (ite (= K3 5.0) Y a!1))))
      (a!3 (or (not S2) (= D2 (ite (= K3 5.0) Y a!1))))
      (a!4 (or (not S2) (= F1 (ite (= K3 5.0) Y a!1))))
      (a!5 (or (not S2) (= L1 (ite (= K3 5.0) Y a!1))))
      (a!6 (or (not S2) (= R1 (ite (= K3 5.0) Y a!1))))
      (a!8 (or (not U2) (= Z1 (ite (= K3 5.0) A1 a!7))))
      (a!9 (or (not U2) (= F2 (ite (= K3 5.0) A1 a!7))))
      (a!10 (or (not U2) (= H1 (ite (= K3 5.0) A1 a!7))))
      (a!11 (or (not U2) (= N1 (ite (= K3 5.0) A1 a!7))))
      (a!12 (or (not U2) (= T1 (ite (= K3 5.0) A1 a!7))))
      (a!14 (or (not W2) (= V1 (ite (= K3 5.0) C1 a!13))))
      (a!15 (or (not W2) (= B2 (ite (= K3 5.0) C1 a!13))))
      (a!16 (or (not W2) (= H2 (ite (= K3 5.0) C1 a!13))))
      (a!17 (or (not W2) (= J1 (ite (= K3 5.0) C1 a!13))))
      (a!18 (or (not W2) (= P1 (ite (= K3 5.0) C1 a!13))))
      (a!22 (ite (= E1 (ite (= G1 I1) I1 E1)) (not a!21) a!20))
      (a!26 (ite (= K1 (ite (= M1 O1) O1 K1)) (not a!25) a!24))
      (a!30 (ite (= Q1 (ite (= S1 U1) U1 Q1)) (not a!29) a!28))
      (a!34 (ite (= W1 (ite (= Y1 A2) A2 W1)) (not a!33) a!32))
      (a!38 (ite (= C2 (ite (= E2 G2) G2 C2)) (not a!37) a!36)))
(let ((a!23 (= Z2 (ite (or a!20 a!22) (ite (= G1 I1) I1 E1) 0.0)))
      (a!27 (= B3 (ite (or a!24 a!26) (ite (= M1 O1) O1 K1) 0.0)))
      (a!31 (= D3 (ite (or a!28 a!30) (ite (= S1 U1) U1 Q1) 0.0)))
      (a!35 (= F3 (ite (or a!32 a!34) (ite (= Y1 A2) A2 W1) 0.0)))
      (a!39 (= H3 (ite (or a!36 a!38) (ite (= E2 G2) G2 C2) 0.0))))
(let ((a!40 (or (and a!2
                     a!3
                     a!4
                     a!5
                     a!6
                     a!8
                     a!9
                     a!10
                     a!11
                     a!12
                     a!14
                     a!15
                     a!16
                     a!17
                     a!18
                     (= H3 G3)
                     (= I3 1.0)
                     (= J3 2.0)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= H G)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= P O)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= X W)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= Z2 Y2)
                     (= B3 A3)
                     (= D3 C3)
                     (= F3 E3)
                     (= J2 I2)
                     (= L2 K2)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2))
                (and (= V1 U1)
                     (= X1 W1)
                     (= Z1 Y1)
                     (= B2 A2)
                     (= D2 C2)
                     (= F2 E2)
                     (= H2 G2)
                     (= H3 G3)
                     (= I3 3.0)
                     (= J3 I3)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= H G)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= P O)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= X W)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= F1 E1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= N1 M1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= Z2 Y2)
                     (= B3 A3)
                     (= D3 C3)
                     (= F3 E3)
                     (= J2 I2)
                     (= L2 K2)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2))
                a!19
                (and (or (not I2) a!23)
                     (or (not K2) a!27)
                     (or (not M2) a!31)
                     (or (not O2) a!35)
                     (or (not Q2) a!39)
                     (= V1 U1)
                     (= X1 W1)
                     (= Z1 Y1)
                     (= B2 A2)
                     (= D2 C2)
                     (= F2 E2)
                     (= H2 G2)
                     (= I3 2.0)
                     (= J3 3.0)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= H G)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= P O)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= X W)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= F1 E1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= N1 M1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= J2 I2)
                     (= L2 K2)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)))))
  (and (= L3 K3) a!40 (= N3 M3))))))
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
           N3)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) ) 
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
           T1)
        (let ((a!1 (or (and E1 (not (= M1 T1)))
               (and F1 (not (= N1 T1)))
               (and G1 (not (= O1 T1)))
               (and H1 (not (= P1 T1)))
               (and I1 (not (= Q1 T1)))))
      (a!2 (ite (= S1 4.0) H1 (ite (= S1 3.0) G1 (ite (= S1 2.0) F1 E1)))))
  (and (<= 3.0 R1) a!1 (ite (= S1 5.0) I1 a!2)))
      )
      false
    )
  )
)

(check-sat)
(exit)
