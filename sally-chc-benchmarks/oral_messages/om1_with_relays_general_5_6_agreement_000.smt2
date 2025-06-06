(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) ) 
    (=>
      (and
        (and (= Y2 0.0)
     (= H2 0.0)
     (= G2 0.0)
     (= F2 0.0)
     (= E2 0.0)
     (= D2 0.0)
     (= C2 0.0)
     (= B2 0.0)
     (= A2 0.0)
     (= Z1 0.0)
     (= Y1 0.0)
     (= X1 0.0)
     (= W1 0.0)
     (= V1 0.0)
     (= U1 0.0)
     (= T1 0.0)
     (= S1 0.0)
     (= R1 0.0)
     (= Q1 0.0)
     (= P1 0.0)
     (= O1 0.0)
     (= N1 0.0)
     (= M1 0.0)
     (= L1 0.0)
     (= K1 0.0)
     (= J1 0.0)
     (= I1 0.0)
     (= H1 0.0)
     (= G1 0.0)
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
     (or (and (not N2) O2 P2 Q2 R2 S2)
         (and N2 (not O2) P2 Q2 R2 S2)
         (and N2 O2 (not P2) Q2 R2 S2)
         (and N2 O2 P2 (not Q2) R2 S2)
         (and N2 O2 P2 Q2 (not R2) S2)
         (and N2 O2 P2 Q2 R2 (not S2)))
     (or (= Z2 1.0) (= Z2 2.0) (= Z2 3.0) (= Z2 4.0) (= Z2 5.0))
     (= M2 true)
     (= L2 true)
     (= K2 true)
     (= J2 true)
     (= I2 true)
     (not (= A3 0.0)))
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
           U1
           V1
           W1
           X1
           Y1
           Z1
           A2
           B2
           C2
           D2
           E2
           F2
           G2
           H2
           I2
           J2
           K2
           L2
           M2
           N2
           O2
           P2
           Q2
           R2
           S2
           T2
           U2
           V2
           W2
           X2
           Y2
           Z2
           A3)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Bool) (R4 Bool) (S4 Bool) (T4 Bool) (U4 Bool) (V4 Bool) (W4 Bool) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Bool) (J5 Bool) (K5 Bool) (L5 Bool) (M5 Real) (N5 Real) (O5 Real) (P5 Real) (Q5 Real) (R5 Real) (S5 Real) (T5 Real) (U5 Real) (V5 Real) (W5 Real) (X5 Real) (Y5 Real) (Z5 Real) (A6 Real) (B6 Real) ) 
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
           O3
           Q3
           S3
           U3
           W3
           Y3
           A4
           C4
           E4
           G4
           I4
           K4
           M4
           O4
           Q4
           S4
           U4
           W4
           Y4
           A5
           C5
           E5
           G5
           I5
           K5
           M5
           O5
           Q5
           S5
           U5
           W5
           Y5
           A6)
        (let ((a!1 (ite (= Y5 4.0) U1 (ite (= Y5 3.0) I1 (ite (= Y5 2.0) W K))))
      (a!7 (ite (= Y5 4.0) K1 (ite (= Y5 3.0) Y (ite (= Y5 2.0) M A))))
      (a!13 (ite (= Y5 4.0) M1 (ite (= Y5 3.0) A1 (ite (= Y5 2.0) O C))))
      (a!19 (ite (= Y5 4.0) O1 (ite (= Y5 3.0) C1 (ite (= Y5 2.0) Q E))))
      (a!25 (ite (= Y5 4.0) Q1 (ite (= Y5 3.0) E1 (ite (= Y5 2.0) S G))))
      (a!31 (ite (= Y5 4.0) S1 (ite (= Y5 3.0) G1 (ite (= Y5 2.0) U I))))
      (a!37 (and (or (not Q4)
                     (and (= B A6) (= D A6) (= F A6) (= H A6) (= J A6) (= L A6))
                     (not (= 1.0 Y5)))
                 (or (not Q4)
                     (= 1.0 Y5)
                     (and (= B 0.0)
                          (= D 0.0)
                          (= F 0.0)
                          (= H 0.0)
                          (= J 0.0)
                          (= L 0.0)))
                 (or (not S4)
                     (and (= N A6) (= P A6) (= R A6) (= T A6) (= V A6) (= X A6))
                     (not (= 2.0 Y5)))
                 (or (not S4)
                     (= 2.0 Y5)
                     (and (= N 0.0)
                          (= P 0.0)
                          (= R 0.0)
                          (= T 0.0)
                          (= V 0.0)
                          (= X 0.0)))
                 (or (not U4)
                     (and (= Z A6)
                          (= B1 A6)
                          (= D1 A6)
                          (= F1 A6)
                          (= H1 A6)
                          (= J1 A6))
                     (not (= 3.0 Y5)))
                 (or (not U4)
                     (= 3.0 Y5)
                     (and (= Z 0.0)
                          (= B1 0.0)
                          (= D1 0.0)
                          (= F1 0.0)
                          (= H1 0.0)
                          (= J1 0.0)))
                 (or (not W4)
                     (and (= L1 A6)
                          (= N1 A6)
                          (= P1 A6)
                          (= R1 A6)
                          (= T1 A6)
                          (= V1 A6))
                     (not (= 4.0 Y5)))
                 (or (not W4)
                     (= 4.0 Y5)
                     (and (= L1 0.0)
                          (= N1 0.0)
                          (= P1 0.0)
                          (= R1 0.0)
                          (= T1 0.0)
                          (= V1 0.0)))
                 (or (not Y4)
                     (and (= X1 A6)
                          (= Z1 A6)
                          (= B2 A6)
                          (= D2 A6)
                          (= F2 A6)
                          (= H2 A6))
                     (not (= 5.0 Y5)))
                 (or (not Y4)
                     (= 5.0 Y5)
                     (and (= X1 0.0)
                          (= Z1 0.0)
                          (= B2 0.0)
                          (= D2 0.0)
                          (= F2 0.0)
                          (= H2 0.0)))
                 (= B3 A3)
                 (= D3 C3)
                 (= F3 E3)
                 (= H3 G3)
                 (= J3 I3)
                 (= L3 K3)
                 (= N3 M3)
                 (= P3 O3)
                 (= R3 Q3)
                 (= T3 S3)
                 (= V3 U3)
                 (= X3 W3)
                 (= Z3 Y3)
                 (= B4 A4)
                 (= D4 C4)
                 (= F4 E4)
                 (= H4 G4)
                 (= J4 I4)
                 (= L4 K4)
                 (= N4 M4)
                 (= P4 O4)
                 (= V5 U5)
                 (= W5 0.0)
                 (= X5 1.0)
                 (= J2 I2)
                 (= L2 K2)
                 (= N2 M2)
                 (= P2 O2)
                 (= R2 Q2)
                 (= T2 S2)
                 (= V2 U2)
                 (= X2 W2)
                 (= Z2 Y2)
                 (= N5 M5)
                 (= P5 O5)
                 (= R5 Q5)
                 (= T5 S5)
                 (= J5 I5)
                 (= L5 K5)
                 (= R4 Q4)
                 (= T4 S4)
                 (= V4 U4)
                 (= X4 W4)
                 (= Z4 Y4)
                 (= B5 A5)
                 (= D5 C5)
                 (= F5 E5)
                 (= H5 G5)))
      (a!38 (ite (= O2 S2)
                 (+ 1 (ite (= Q2 S2) 2 0))
                 (+ (- 1) (ite (= Q2 S2) 2 0))))
      (a!51 (ite (= A3 E3)
                 (+ 1 (ite (= C3 E3) 2 0))
                 (+ (- 1) (ite (= C3 E3) 2 0))))
      (a!64 (ite (= M3 Q3)
                 (+ 1 (ite (= O3 Q3) 2 0))
                 (+ (- 1) (ite (= O3 Q3) 2 0))))
      (a!77 (ite (= Y3 C4)
                 (+ 1 (ite (= A4 C4) 2 0))
                 (+ (- 1) (ite (= A4 C4) 2 0))))
      (a!90 (ite (= K4 O4)
                 (+ 1 (ite (= M4 O4) 2 0))
                 (+ (- 1) (ite (= M4 O4) 2 0)))))
(let ((a!2 (or (not K5) (= F3 (ite (= Y5 5.0) G2 a!1))))
      (a!3 (or (not K5) (= R3 (ite (= Y5 5.0) G2 a!1))))
      (a!4 (or (not K5) (= D4 (ite (= Y5 5.0) G2 a!1))))
      (a!5 (or (not K5) (= P4 (ite (= Y5 5.0) G2 a!1))))
      (a!6 (or (not K5) (= T2 (ite (= Y5 5.0) G2 a!1))))
      (a!8 (or (not A5) (= H3 (ite (= Y5 5.0) W1 a!7))))
      (a!9 (or (not A5) (= T3 (ite (= Y5 5.0) W1 a!7))))
      (a!10 (or (not A5) (= F4 (ite (= Y5 5.0) W1 a!7))))
      (a!11 (or (not A5) (= J2 (ite (= Y5 5.0) W1 a!7))))
      (a!12 (or (not A5) (= V2 (ite (= Y5 5.0) W1 a!7))))
      (a!14 (or (not C5) (= J3 (ite (= Y5 5.0) Y1 a!13))))
      (a!15 (or (not C5) (= V3 (ite (= Y5 5.0) Y1 a!13))))
      (a!16 (or (not C5) (= H4 (ite (= Y5 5.0) Y1 a!13))))
      (a!17 (or (not C5) (= L2 (ite (= Y5 5.0) Y1 a!13))))
      (a!18 (or (not C5) (= X2 (ite (= Y5 5.0) Y1 a!13))))
      (a!20 (or (not E5) (= L3 (ite (= Y5 5.0) A2 a!19))))
      (a!21 (or (not E5) (= X3 (ite (= Y5 5.0) A2 a!19))))
      (a!22 (or (not E5) (= J4 (ite (= Y5 5.0) A2 a!19))))
      (a!23 (or (not E5) (= N2 (ite (= Y5 5.0) A2 a!19))))
      (a!24 (or (not E5) (= Z2 (ite (= Y5 5.0) A2 a!19))))
      (a!26 (or (not G5) (= B3 (ite (= Y5 5.0) C2 a!25))))
      (a!27 (or (not G5) (= N3 (ite (= Y5 5.0) C2 a!25))))
      (a!28 (or (not G5) (= Z3 (ite (= Y5 5.0) C2 a!25))))
      (a!29 (or (not G5) (= L4 (ite (= Y5 5.0) C2 a!25))))
      (a!30 (or (not G5) (= P2 (ite (= Y5 5.0) C2 a!25))))
      (a!32 (or (not I5) (= D3 (ite (= Y5 5.0) E2 a!31))))
      (a!33 (or (not I5) (= P3 (ite (= Y5 5.0) E2 a!31))))
      (a!34 (or (not I5) (= B4 (ite (= Y5 5.0) E2 a!31))))
      (a!35 (or (not I5) (= N4 (ite (= Y5 5.0) E2 a!31))))
      (a!36 (or (not I5) (= R2 (ite (= Y5 5.0) E2 a!31))))
      (a!39 (ite (= M2 (ite (= Q2 S2) S2 O2))
                 (+ 1 (ite (= Q2 S2) a!38 1))
                 (+ (- 1) (ite (= Q2 S2) a!38 1))))
      (a!40 (ite (and (= Q2 S2) (= a!38 0)) M2 (ite (= Q2 S2) S2 O2)))
      (a!52 (ite (= Y2 (ite (= C3 E3) E3 A3))
                 (+ 1 (ite (= C3 E3) a!51 1))
                 (+ (- 1) (ite (= C3 E3) a!51 1))))
      (a!53 (ite (and (= C3 E3) (= a!51 0)) Y2 (ite (= C3 E3) E3 A3)))
      (a!65 (ite (= K3 (ite (= O3 Q3) Q3 M3))
                 (+ 1 (ite (= O3 Q3) a!64 1))
                 (+ (- 1) (ite (= O3 Q3) a!64 1))))
      (a!66 (ite (and (= O3 Q3) (= a!64 0)) K3 (ite (= O3 Q3) Q3 M3)))
      (a!78 (ite (= W3 (ite (= A4 C4) C4 Y3))
                 (+ 1 (ite (= A4 C4) a!77 1))
                 (+ (- 1) (ite (= A4 C4) a!77 1))))
      (a!79 (ite (and (= A4 C4) (= a!77 0)) W3 (ite (= A4 C4) C4 Y3)))
      (a!91 (ite (= I4 (ite (= M4 O4) O4 K4))
                 (+ 1 (ite (= M4 O4) a!90 1))
                 (+ (- 1) (ite (= M4 O4) a!90 1))))
      (a!92 (ite (and (= M4 O4) (= a!90 0)) I4 (ite (= M4 O4) O4 K4))))
(let ((a!41 (ite (and (= Q2 S2) (= a!38 0)) 1 a!39))
      (a!43 (and (or (not (= Q2 S2)) (not (= a!38 0))) (= a!39 0)))
      (a!54 (ite (and (= C3 E3) (= a!51 0)) 1 a!52))
      (a!56 (and (or (not (= C3 E3)) (not (= a!51 0))) (= a!52 0)))
      (a!67 (ite (and (= O3 Q3) (= a!64 0)) 1 a!65))
      (a!69 (and (or (not (= O3 Q3)) (not (= a!64 0))) (= a!65 0)))
      (a!80 (ite (and (= A4 C4) (= a!77 0)) 1 a!78))
      (a!82 (and (or (not (= A4 C4)) (not (= a!77 0))) (= a!78 0)))
      (a!93 (ite (and (= M4 O4) (= a!90 0)) 1 a!91))
      (a!95 (and (or (not (= M4 O4)) (not (= a!90 0))) (= a!91 0))))
(let ((a!42 (and (or (and (= Q2 S2) (= a!38 0)) (not (= a!39 0)))
                 (= (ite (= K2 a!40) (+ 1 a!41) (+ (- 1) a!41)) 0)))
      (a!55 (and (or (and (= C3 E3) (= a!51 0)) (not (= a!52 0)))
                 (= (ite (= W2 a!53) (+ 1 a!54) (+ (- 1) a!54)) 0)))
      (a!68 (and (or (and (= O3 Q3) (= a!64 0)) (not (= a!65 0)))
                 (= (ite (= I3 a!66) (+ 1 a!67) (+ (- 1) a!67)) 0)))
      (a!81 (and (or (and (= A4 C4) (= a!77 0)) (not (= a!78 0)))
                 (= (ite (= U3 a!79) (+ 1 a!80) (+ (- 1) a!80)) 0)))
      (a!94 (and (or (and (= M4 O4) (= a!90 0)) (not (= a!91 0)))
                 (= (ite (= G4 a!92) (+ 1 a!93) (+ (- 1) a!93)) 0))))
(let ((a!44 (ite (= S2 (ite a!42 I2 (ite a!43 K2 a!40))) 3 4))
      (a!57 (ite (= E3 (ite a!55 U2 (ite a!56 W2 a!53))) 3 4))
      (a!70 (ite (= Q3 (ite a!68 G3 (ite a!69 I3 a!66))) 3 4))
      (a!83 (ite (= C4 (ite a!81 S3 (ite a!82 U3 a!79))) 3 4))
      (a!96 (ite (= O4 (ite a!94 E4 (ite a!95 G4 a!92))) 3 4)))
(let ((a!45 (ite (= Q2 (ite a!42 I2 (ite a!43 K2 a!40))) (+ (- 1) a!44) a!44))
      (a!58 (ite (= C3 (ite a!55 U2 (ite a!56 W2 a!53))) (+ (- 1) a!57) a!57))
      (a!71 (ite (= O3 (ite a!68 G3 (ite a!69 I3 a!66))) (+ (- 1) a!70) a!70))
      (a!84 (ite (= A4 (ite a!81 S3 (ite a!82 U3 a!79))) (+ (- 1) a!83) a!83))
      (a!97 (ite (= M4 (ite a!94 E4 (ite a!95 G4 a!92))) (+ (- 1) a!96) a!96)))
(let ((a!46 (ite (= O2 (ite a!42 I2 (ite a!43 K2 a!40))) (+ (- 1) a!45) a!45))
      (a!59 (ite (= A3 (ite a!55 U2 (ite a!56 W2 a!53))) (+ (- 1) a!58) a!58))
      (a!72 (ite (= M3 (ite a!68 G3 (ite a!69 I3 a!66))) (+ (- 1) a!71) a!71))
      (a!85 (ite (= Y3 (ite a!81 S3 (ite a!82 U3 a!79))) (+ (- 1) a!84) a!84))
      (a!98 (ite (= K4 (ite a!94 E4 (ite a!95 G4 a!92))) (+ (- 1) a!97) a!97)))
(let ((a!47 (ite (= M2 (ite a!42 I2 (ite a!43 K2 a!40))) (+ (- 1) a!46) a!46))
      (a!60 (ite (= Y2 (ite a!55 U2 (ite a!56 W2 a!53))) (+ (- 1) a!59) a!59))
      (a!73 (ite (= K3 (ite a!68 G3 (ite a!69 I3 a!66))) (+ (- 1) a!72) a!72))
      (a!86 (ite (= W3 (ite a!81 S3 (ite a!82 U3 a!79))) (+ (- 1) a!85) a!85))
      (a!99 (ite (= I4 (ite a!94 E4 (ite a!95 G4 a!92))) (+ (- 1) a!98) a!98)))
(let ((a!48 (ite (= K2 (ite a!42 I2 (ite a!43 K2 a!40))) (+ (- 1) a!47) a!47))
      (a!61 (ite (= W2 (ite a!55 U2 (ite a!56 W2 a!53))) (+ (- 1) a!60) a!60))
      (a!74 (ite (= I3 (ite a!68 G3 (ite a!69 I3 a!66))) (+ (- 1) a!73) a!73))
      (a!87 (ite (= U3 (ite a!81 S3 (ite a!82 U3 a!79))) (+ (- 1) a!86) a!86))
      (a!100 (ite (= G4 (ite a!94 E4 (ite a!95 G4 a!92))) (+ (- 1) a!99) a!99)))
(let ((a!49 (ite (= I2 (ite a!42 I2 (ite a!43 K2 a!40))) (= a!48 1) (= a!48 0)))
      (a!62 (ite (= U2 (ite a!55 U2 (ite a!56 W2 a!53))) (= a!61 1) (= a!61 0)))
      (a!75 (ite (= G3 (ite a!68 G3 (ite a!69 I3 a!66))) (= a!74 1) (= a!74 0)))
      (a!88 (ite (= S3 (ite a!81 S3 (ite a!82 U3 a!79))) (= a!87 1) (= a!87 0)))
      (a!101 (ite (= E4 (ite a!94 E4 (ite a!95 G4 a!92)))
                  (= a!100 1)
                  (= a!100 0))))
(let ((a!50 (= N5
               (ite (or (= a!46 0) (= a!47 0) (= a!48 0) a!49)
                    (ite a!42 I2 (ite a!43 K2 a!40))
                    0.0)))
      (a!63 (= P5
               (ite (or (= a!59 0) (= a!60 0) (= a!61 0) a!62)
                    (ite a!55 U2 (ite a!56 W2 a!53))
                    0.0)))
      (a!76 (= R5
               (ite (or (= a!72 0) (= a!73 0) (= a!74 0) a!75)
                    (ite a!68 G3 (ite a!69 I3 a!66))
                    0.0)))
      (a!89 (= T5
               (ite (or (= a!85 0) (= a!86 0) (= a!87 0) a!88)
                    (ite a!81 S3 (ite a!82 U3 a!79))
                    0.0)))
      (a!102 (= V5
                (ite (or (= a!98 0) (= a!99 0) (= a!100 0) a!101)
                     (ite a!94 E4 (ite a!95 G4 a!92))
                     0.0))))
(let ((a!103 (or (and a!2
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
                      a!20
                      a!21
                      a!22
                      a!23
                      a!24
                      a!26
                      a!27
                      a!28
                      a!29
                      a!30
                      a!32
                      a!33
                      a!34
                      a!35
                      a!36
                      (= V5 U5)
                      (= W5 1.0)
                      (= X5 2.0)
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
                      (= V1 U1)
                      (= X1 W1)
                      (= Z1 Y1)
                      (= B2 A2)
                      (= D2 C2)
                      (= F2 E2)
                      (= H2 G2)
                      (= N5 M5)
                      (= P5 O5)
                      (= R5 Q5)
                      (= T5 S5)
                      (= J5 I5)
                      (= L5 K5)
                      (= R4 Q4)
                      (= T4 S4)
                      (= V4 U4)
                      (= X4 W4)
                      (= Z4 Y4)
                      (= B5 A5)
                      (= D5 C5)
                      (= F5 E5)
                      (= H5 G5))
                 (and (= B3 A3)
                      (= D3 C3)
                      (= F3 E3)
                      (= H3 G3)
                      (= J3 I3)
                      (= L3 K3)
                      (= N3 M3)
                      (= P3 O3)
                      (= R3 Q3)
                      (= T3 S3)
                      (= V3 U3)
                      (= X3 W3)
                      (= Z3 Y3)
                      (= B4 A4)
                      (= D4 C4)
                      (= F4 E4)
                      (= H4 G4)
                      (= J4 I4)
                      (= L4 K4)
                      (= N4 M4)
                      (= P4 O4)
                      (= V5 U5)
                      (= W5 3.0)
                      (= X5 W5)
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
                      (= V1 U1)
                      (= X1 W1)
                      (= Z1 Y1)
                      (= B2 A2)
                      (= D2 C2)
                      (= F2 E2)
                      (= H2 G2)
                      (= J2 I2)
                      (= L2 K2)
                      (= N2 M2)
                      (= P2 O2)
                      (= R2 Q2)
                      (= T2 S2)
                      (= V2 U2)
                      (= X2 W2)
                      (= Z2 Y2)
                      (= N5 M5)
                      (= P5 O5)
                      (= R5 Q5)
                      (= T5 S5)
                      (= J5 I5)
                      (= L5 K5)
                      (= R4 Q4)
                      (= T4 S4)
                      (= V4 U4)
                      (= X4 W4)
                      (= Z4 Y4)
                      (= B5 A5)
                      (= D5 C5)
                      (= F5 E5)
                      (= H5 G5))
                 a!37
                 (and (or (not Q4) a!50)
                      (or (not S4) a!63)
                      (or (not U4) a!76)
                      (or (not W4) a!89)
                      (or (not Y4) a!102)
                      (= B3 A3)
                      (= D3 C3)
                      (= F3 E3)
                      (= H3 G3)
                      (= J3 I3)
                      (= L3 K3)
                      (= N3 M3)
                      (= P3 O3)
                      (= R3 Q3)
                      (= T3 S3)
                      (= V3 U3)
                      (= X3 W3)
                      (= Z3 Y3)
                      (= B4 A4)
                      (= D4 C4)
                      (= F4 E4)
                      (= H4 G4)
                      (= J4 I4)
                      (= L4 K4)
                      (= N4 M4)
                      (= P4 O4)
                      (= W5 2.0)
                      (= X5 3.0)
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
                      (= V1 U1)
                      (= X1 W1)
                      (= Z1 Y1)
                      (= B2 A2)
                      (= D2 C2)
                      (= F2 E2)
                      (= H2 G2)
                      (= J2 I2)
                      (= L2 K2)
                      (= N2 M2)
                      (= P2 O2)
                      (= R2 Q2)
                      (= T2 S2)
                      (= V2 U2)
                      (= X2 W2)
                      (= Z2 Y2)
                      (= J5 I5)
                      (= L5 K5)
                      (= R4 Q4)
                      (= T4 S4)
                      (= V4 U4)
                      (= X4 W4)
                      (= Z4 Y4)
                      (= B5 A5)
                      (= D5 C5)
                      (= F5 E5)
                      (= H5 G5)))))
  (and (= Z5 Y5) a!103 (= B6 A6))))))))))))))
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
           P3
           R3
           T3
           V3
           X3
           Z3
           B4
           D4
           F4
           H4
           J4
           L4
           N4
           P4
           R4
           T4
           V4
           X4
           Z4
           B5
           D5
           F5
           H5
           J5
           L5
           N5
           P5
           R5
           T5
           V5
           X5
           Z5
           B6)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) ) 
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
           U1
           V1
           W1
           X1
           Y1
           Z1
           A2
           B2
           C2
           D2
           E2
           F2
           G2
           H2
           I2
           J2
           K2
           L2
           M2
           N2
           O2
           P2
           Q2
           R2
           S2
           T2
           U2
           V2
           W2
           X2
           Y2
           Z2
           A3)
        (let ((a!1 (or (and J2 (not (= T2 U2)))
               (and K2 (not (= T2 V2)))
               (and L2 (not (= T2 W2)))
               (and M2 (not (= T2 X2)))))
      (a!2 (or (and I2 (not (= U2 T2)))
               (and K2 (not (= U2 V2)))
               (and L2 (not (= U2 W2)))
               (and M2 (not (= U2 X2)))))
      (a!3 (or (and I2 (not (= V2 T2)))
               (and J2 (not (= V2 U2)))
               (and L2 (not (= V2 W2)))
               (and M2 (not (= V2 X2)))))
      (a!4 (or (and I2 (not (= W2 T2)))
               (and J2 (not (= W2 U2)))
               (and K2 (not (= W2 V2)))
               (and M2 (not (= W2 X2)))))
      (a!5 (or (and I2 (not (= X2 T2)))
               (and J2 (not (= X2 U2)))
               (and K2 (not (= X2 V2)))
               (and L2 (not (= X2 W2))))))
  (and (or (and I2 a!1) (and J2 a!2) (and K2 a!3) (and L2 a!4) (and M2 a!5))
       (<= 3.0 Y2)))
      )
      false
    )
  )
)

(check-sat)
(exit)
