(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Bool) (Q3 Bool) (R3 Bool) (S3 Bool) (T3 Bool) (U3 Bool) (V3 Bool) (W3 Bool) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) ) 
    (=>
      (and
        (and (= A4 0.0)
     (= F3 0.0)
     (= E3 0.0)
     (= D3 0.0)
     (= C3 0.0)
     (= B3 0.0)
     (= A3 0.0)
     (= Z2 0.0)
     (= Y2 0.0)
     (= X2 0.0)
     (= W2 0.0)
     (= V2 0.0)
     (= U2 0.0)
     (= T2 0.0)
     (= S2 0.0)
     (= R2 0.0)
     (= Q2 0.0)
     (= P2 0.0)
     (= O2 0.0)
     (= N2 0.0)
     (= M2 0.0)
     (= L2 0.0)
     (= K2 0.0)
     (= J2 0.0)
     (= I2 0.0)
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
     (or (and (not J3) K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3)
         (and J3 (not K3) L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3)
         (and J3 K3 (not L3) M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3)
         (and J3 K3 L3 (not M3) N3 O3 P3 Q3 R3 S3 T3 U3 V3 W3)
         (and J3 K3 L3 M3 (not N3) O3 P3 Q3 R3 S3 T3 U3 V3 W3)
         (and J3 K3 L3 M3 N3 (not O3) P3 Q3 R3 S3 T3 U3 V3 W3)
         (and J3 K3 L3 M3 N3 O3 (not P3) Q3 R3 S3 T3 U3 V3 W3)
         (and J3 K3 L3 M3 N3 O3 P3 (not Q3) R3 S3 T3 U3 V3 W3)
         (and J3 K3 L3 M3 N3 O3 P3 Q3 (not R3) S3 T3 U3 V3 W3)
         (and J3 K3 L3 M3 N3 O3 P3 Q3 R3 (not S3) T3 U3 V3 W3)
         (and J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 (not T3) U3 V3 W3)
         (and J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 (not U3) V3 W3)
         (and J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 (not V3) W3)
         (and J3 K3 L3 M3 N3 O3 P3 Q3 R3 S3 T3 U3 V3 (not W3)))
     (or (= B4 1.0) (= B4 2.0) (= B4 3.0))
     (= I3 true)
     (= H3 true)
     (= G3 true)
     (not (= C4 0.0)))
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
           A3
           B3
           C3
           D3
           E3
           F3
           G3
           H3
           I3
           J3
           K3
           L3
           M3
           N3
           O3
           P3
           Q3
           R3
           S3
           T3
           U3
           V3
           W3
           X3
           Y3
           Z3
           A4
           B4
           C4)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Real) (R4 Real) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) (Y4 Real) (Z4 Real) (A5 Real) (B5 Real) (C5 Real) (D5 Real) (E5 Real) (F5 Real) (G5 Real) (H5 Real) (I5 Real) (J5 Real) (K5 Real) (L5 Real) (M5 Real) (N5 Real) (O5 Real) (P5 Real) (Q5 Real) (R5 Real) (S5 Real) (T5 Real) (U5 Real) (V5 Real) (W5 Real) (X5 Real) (Y5 Real) (Z5 Real) (A6 Real) (B6 Real) (C6 Real) (D6 Real) (E6 Real) (F6 Real) (G6 Real) (H6 Real) (I6 Real) (J6 Real) (K6 Real) (L6 Real) (M6 Bool) (N6 Bool) (O6 Bool) (P6 Bool) (Q6 Bool) (R6 Bool) (S6 Bool) (T6 Bool) (U6 Bool) (V6 Bool) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Bool) (F7 Bool) (G7 Bool) (H7 Bool) (I7 Bool) (J7 Bool) (K7 Bool) (L7 Bool) (M7 Bool) (N7 Bool) (O7 Bool) (P7 Bool) (Q7 Bool) (R7 Bool) (S7 Bool) (T7 Bool) (U7 Real) (V7 Real) (W7 Real) (X7 Real) (Y7 Real) (Z7 Real) (A8 Real) (B8 Real) (C8 Real) (D8 Real) (E8 Real) (F8 Real) ) 
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
           A6
           C6
           E6
           G6
           I6
           K6
           M6
           O6
           Q6
           S6
           U6
           W6
           Y6
           A7
           C7
           E7
           G7
           I7
           K7
           M7
           O7
           Q7
           S7
           U7
           W7
           Y7
           A8
           C8
           E8)
        (let ((a!1 (ite (= C8 3.0) W2 (ite (= C8 2.0) U1 S)))
      (a!2 (ite (= C8 3.0) Y2 (ite (= C8 2.0) W1 U)))
      (a!3 (ite (= C8 3.0) A3 (ite (= C8 2.0) Y1 W)))
      (a!4 (ite (= C8 3.0) C3 (ite (= C8 2.0) A2 Y)))
      (a!5 (ite (= C8 3.0) E3 (ite (= C8 2.0) C2 A1)))
      (a!6 (ite (= C8 3.0) E2 (ite (= C8 2.0) C1 A)))
      (a!7 (ite (= C8 3.0) G2 (ite (= C8 2.0) E1 C)))
      (a!8 (ite (= C8 3.0) I2 (ite (= C8 2.0) G1 E)))
      (a!9 (ite (= C8 3.0) K2 (ite (= C8 2.0) I1 G)))
      (a!10 (ite (= C8 3.0) M2 (ite (= C8 2.0) K1 I)))
      (a!11 (ite (= C8 3.0) O2 (ite (= C8 2.0) M1 K)))
      (a!12 (ite (= C8 3.0) Q2 (ite (= C8 2.0) O1 M)))
      (a!13 (ite (= C8 3.0) S2 (ite (= C8 2.0) Q1 O)))
      (a!14 (ite (= C8 3.0) U2 (ite (= C8 2.0) S1 Q)))
      (a!15 (and (or (not M6)
                     (and (= B E8)
                          (= D E8)
                          (= F E8)
                          (= H E8)
                          (= J E8)
                          (= L E8)
                          (= N E8)
                          (= P E8)
                          (= R E8)
                          (= T E8)
                          (= V E8)
                          (= X E8)
                          (= Z E8)
                          (= B1 E8))
                     (not (= 1.0 C8)))
                 (or (not M6)
                     (= 1.0 C8)
                     (and (= B 0.0)
                          (= D 0.0)
                          (= F 0.0)
                          (= H 0.0)
                          (= J 0.0)
                          (= L 0.0)
                          (= N 0.0)
                          (= P 0.0)
                          (= R 0.0)
                          (= T 0.0)
                          (= V 0.0)
                          (= X 0.0)
                          (= Z 0.0)
                          (= B1 0.0)))
                 (or (not O6)
                     (and (= D1 E8)
                          (= F1 E8)
                          (= H1 E8)
                          (= J1 E8)
                          (= L1 E8)
                          (= N1 E8)
                          (= P1 E8)
                          (= R1 E8)
                          (= T1 E8)
                          (= V1 E8)
                          (= X1 E8)
                          (= Z1 E8)
                          (= B2 E8)
                          (= D2 E8))
                     (not (= 2.0 C8)))
                 (or (not O6)
                     (= 2.0 C8)
                     (and (= D1 0.0)
                          (= F1 0.0)
                          (= H1 0.0)
                          (= J1 0.0)
                          (= L1 0.0)
                          (= N1 0.0)
                          (= P1 0.0)
                          (= R1 0.0)
                          (= T1 0.0)
                          (= V1 0.0)
                          (= X1 0.0)
                          (= Z1 0.0)
                          (= B2 0.0)
                          (= D2 0.0)))
                 (or (not Q6)
                     (and (= F2 E8)
                          (= H2 E8)
                          (= J2 E8)
                          (= L2 E8)
                          (= N2 E8)
                          (= P2 E8)
                          (= R2 E8)
                          (= T2 E8)
                          (= V2 E8)
                          (= X2 E8)
                          (= Z2 E8)
                          (= B3 E8)
                          (= D3 E8)
                          (= F3 E8))
                     (not (= 3.0 C8)))
                 (or (not Q6)
                     (= 3.0 C8)
                     (and (= F2 0.0)
                          (= H2 0.0)
                          (= J2 0.0)
                          (= L2 0.0)
                          (= N2 0.0)
                          (= P2 0.0)
                          (= R2 0.0)
                          (= T2 0.0)
                          (= V2 0.0)
                          (= X2 0.0)
                          (= Z2 0.0)
                          (= B3 0.0)
                          (= D3 0.0)
                          (= F3 0.0)))
                 (= D4 C4)
                 (= F4 E4)
                 (= H4 G4)
                 (= J4 I4)
                 (= L4 K4)
                 (= N4 M4)
                 (= P4 O4)
                 (= R4 Q4)
                 (= T4 S4)
                 (= V4 U4)
                 (= X4 W4)
                 (= Z4 Y4)
                 (= B5 A5)
                 (= D5 C5)
                 (= F5 E5)
                 (= H5 G5)
                 (= J5 I5)
                 (= L5 K5)
                 (= N5 M5)
                 (= P5 O5)
                 (= R5 Q5)
                 (= T5 S5)
                 (= V5 U5)
                 (= X5 W5)
                 (= Z5 Y5)
                 (= B6 A6)
                 (= D6 C6)
                 (= F6 E6)
                 (= H6 G6)
                 (= J6 I6)
                 (= L6 K6)
                 (= A8 0.0)
                 (= B8 1.0)
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
                 (= V7 U7)
                 (= X7 W7)
                 (= Z7 Y7)
                 (= J7 I7)
                 (= L7 K7)
                 (= N7 M7)
                 (= P7 O7)
                 (= R7 Q7)
                 (= T7 S7)
                 (= N6 M6)
                 (= P6 O6)
                 (= R6 Q6)
                 (= T6 S6)
                 (= V6 U6)
                 (= X6 W6)
                 (= Z6 Y6)
                 (= B7 A7)
                 (= D7 C7)
                 (= F7 E7)
                 (= H7 G7)))
      (a!16 (ite (= C4 G4)
                 (+ 1 (ite (= E4 G4) 2 0))
                 (+ (- 1) (ite (= E4 G4) 2 0))))
      (a!51 (ite (= E5 I5)
                 (+ 1 (ite (= G5 I5) 2 0))
                 (+ (- 1) (ite (= G5 I5) 2 0))))
      (a!86 (ite (= G6 K6)
                 (+ 1 (ite (= I6 K6) 2 0))
                 (+ (- 1) (ite (= I6 K6) 2 0)))))
(let ((a!17 (ite (= A4 (ite (= E4 G4) G4 C4))
                 (+ 1 (ite (= E4 G4) a!16 1))
                 (+ (- 1) (ite (= E4 G4) a!16 1))))
      (a!18 (ite (and (= E4 G4) (= a!16 0)) A4 (ite (= E4 G4) G4 C4)))
      (a!52 (ite (= C5 (ite (= G5 I5) I5 E5))
                 (+ 1 (ite (= G5 I5) a!51 1))
                 (+ (- 1) (ite (= G5 I5) a!51 1))))
      (a!53 (ite (and (= G5 I5) (= a!51 0)) C5 (ite (= G5 I5) I5 E5)))
      (a!87 (ite (= E6 (ite (= I6 K6) K6 G6))
                 (+ 1 (ite (= I6 K6) a!86 1))
                 (+ (- 1) (ite (= I6 K6) a!86 1))))
      (a!88 (ite (and (= I6 K6) (= a!86 0)) E6 (ite (= I6 K6) K6 G6))))
(let ((a!19 (ite (and (= E4 G4) (= a!16 0)) 1 a!17))
      (a!22 (and (or (not (= E4 G4)) (not (= a!16 0))) (= a!17 0)))
      (a!54 (ite (and (= G5 I5) (= a!51 0)) 1 a!52))
      (a!57 (and (or (not (= G5 I5)) (not (= a!51 0))) (= a!52 0)))
      (a!89 (ite (and (= I6 K6) (= a!86 0)) 1 a!87))
      (a!92 (and (or (not (= I6 K6)) (not (= a!86 0))) (= a!87 0))))
(let ((a!20 (ite (= Y3 a!18) (+ 1 a!19) (+ (- 1) a!19)))
      (a!55 (ite (= A5 a!53) (+ 1 a!54) (+ (- 1) a!54)))
      (a!90 (ite (= C6 a!88) (+ 1 a!89) (+ (- 1) a!89))))
(let ((a!21 (and (or (and (= E4 G4) (= a!16 0)) (not (= a!17 0))) (= a!20 0)))
      (a!23 (ite (= W3 (ite a!22 Y3 a!18))
                 (+ 1 (ite a!22 1 a!20))
                 (+ (- 1) (ite a!22 1 a!20))))
      (a!56 (and (or (and (= G5 I5) (= a!51 0)) (not (= a!52 0))) (= a!55 0)))
      (a!58 (ite (= Y4 (ite a!57 A5 a!53))
                 (+ 1 (ite a!57 1 a!55))
                 (+ (- 1) (ite a!57 1 a!55))))
      (a!91 (and (or (and (= I6 K6) (= a!86 0)) (not (= a!87 0))) (= a!90 0)))
      (a!93 (ite (= A6 (ite a!92 C6 a!88))
                 (+ 1 (ite a!92 1 a!90))
                 (+ (- 1) (ite a!92 1 a!90)))))
(let ((a!24 (ite (= U3 (ite a!21 W3 (ite a!22 Y3 a!18)))
                 (+ 1 (ite a!21 1 a!23))
                 (+ (- 1) (ite a!21 1 a!23))))
      (a!26 (and (or a!22 (not (= a!20 0))) (= a!23 0)))
      (a!59 (ite (= W4 (ite a!56 Y4 (ite a!57 A5 a!53)))
                 (+ 1 (ite a!56 1 a!58))
                 (+ (- 1) (ite a!56 1 a!58))))
      (a!61 (and (or a!57 (not (= a!55 0))) (= a!58 0)))
      (a!94 (ite (= Y5 (ite a!91 A6 (ite a!92 C6 a!88)))
                 (+ 1 (ite a!91 1 a!93))
                 (+ (- 1) (ite a!91 1 a!93))))
      (a!96 (and (or a!92 (not (= a!90 0))) (= a!93 0))))
(let ((a!25 (and (or a!21 (not (= a!23 0))) (= a!24 0)))
      (a!27 (ite a!26 U3 (ite a!21 W3 (ite a!22 Y3 a!18))))
      (a!60 (and (or a!56 (not (= a!58 0))) (= a!59 0)))
      (a!62 (ite a!61 W4 (ite a!56 Y4 (ite a!57 A5 a!53))))
      (a!95 (and (or a!91 (not (= a!93 0))) (= a!94 0)))
      (a!97 (ite a!96 Y5 (ite a!91 A6 (ite a!92 C6 a!88)))))
(let ((a!28 (ite (= S3 a!27)
                 (+ 1 (ite a!26 1 a!24))
                 (+ (- 1) (ite a!26 1 a!24))))
      (a!63 (ite (= U4 a!62)
                 (+ 1 (ite a!61 1 a!59))
                 (+ (- 1) (ite a!61 1 a!59))))
      (a!98 (ite (= W5 a!97)
                 (+ 1 (ite a!96 1 a!94))
                 (+ (- 1) (ite a!96 1 a!94)))))
(let ((a!29 (ite (= Q3 (ite a!25 S3 a!27))
                 (+ 1 (ite a!25 1 a!28))
                 (+ (- 1) (ite a!25 1 a!28))))
      (a!31 (and (or a!26 (not (= a!24 0))) (= a!28 0)))
      (a!64 (ite (= S4 (ite a!60 U4 a!62))
                 (+ 1 (ite a!60 1 a!63))
                 (+ (- 1) (ite a!60 1 a!63))))
      (a!66 (and (or a!61 (not (= a!59 0))) (= a!63 0)))
      (a!99 (ite (= U5 (ite a!95 W5 a!97))
                 (+ 1 (ite a!95 1 a!98))
                 (+ (- 1) (ite a!95 1 a!98))))
      (a!101 (and (or a!96 (not (= a!94 0))) (= a!98 0))))
(let ((a!30 (and (or a!25 (not (= a!28 0))) (= a!29 0)))
      (a!32 (ite (= O3 (ite a!31 Q3 (ite a!25 S3 a!27)))
                 (+ 1 (ite a!31 1 a!29))
                 (+ (- 1) (ite a!31 1 a!29))))
      (a!65 (and (or a!60 (not (= a!63 0))) (= a!64 0)))
      (a!67 (ite (= Q4 (ite a!66 S4 (ite a!60 U4 a!62)))
                 (+ 1 (ite a!66 1 a!64))
                 (+ (- 1) (ite a!66 1 a!64))))
      (a!100 (and (or a!95 (not (= a!98 0))) (= a!99 0)))
      (a!102 (ite (= S5 (ite a!101 U5 (ite a!95 W5 a!97)))
                  (+ 1 (ite a!101 1 a!99))
                  (+ (- 1) (ite a!101 1 a!99)))))
(let ((a!33 (ite a!30 O3 (ite a!31 Q3 (ite a!25 S3 a!27))))
      (a!36 (and (or a!31 (not (= a!29 0))) (= a!32 0)))
      (a!68 (ite a!65 Q4 (ite a!66 S4 (ite a!60 U4 a!62))))
      (a!71 (and (or a!66 (not (= a!64 0))) (= a!67 0)))
      (a!103 (ite a!100 S5 (ite a!101 U5 (ite a!95 W5 a!97))))
      (a!106 (and (or a!101 (not (= a!99 0))) (= a!102 0))))
(let ((a!34 (ite (= M3 a!33)
                 (+ 1 (ite a!30 1 a!32))
                 (+ (- 1) (ite a!30 1 a!32))))
      (a!69 (ite (= O4 a!68)
                 (+ 1 (ite a!65 1 a!67))
                 (+ (- 1) (ite a!65 1 a!67))))
      (a!104 (ite (= Q5 a!103)
                  (+ 1 (ite a!100 1 a!102))
                  (+ (- 1) (ite a!100 1 a!102)))))
(let ((a!35 (and (or a!30 (not (= a!32 0))) (= a!34 0)))
      (a!37 (ite (= K3 (ite a!36 M3 a!33))
                 (+ 1 (ite a!36 1 a!34))
                 (+ (- 1) (ite a!36 1 a!34))))
      (a!70 (and (or a!65 (not (= a!67 0))) (= a!69 0)))
      (a!72 (ite (= M4 (ite a!71 O4 a!68))
                 (+ 1 (ite a!71 1 a!69))
                 (+ (- 1) (ite a!71 1 a!69))))
      (a!105 (and (or a!100 (not (= a!102 0))) (= a!104 0)))
      (a!107 (ite (= O5 (ite a!106 Q5 a!103))
                  (+ 1 (ite a!106 1 a!104))
                  (+ (- 1) (ite a!106 1 a!104)))))
(let ((a!38 (ite (= I3 (ite a!35 K3 (ite a!36 M3 a!33)))
                 (+ 1 (ite a!35 1 a!37))
                 (+ (- 1) (ite a!35 1 a!37))))
      (a!40 (and (or a!36 (not (= a!34 0))) (= a!37 0)))
      (a!73 (ite (= K4 (ite a!70 M4 (ite a!71 O4 a!68)))
                 (+ 1 (ite a!70 1 a!72))
                 (+ (- 1) (ite a!70 1 a!72))))
      (a!75 (and (or a!71 (not (= a!69 0))) (= a!72 0)))
      (a!108 (ite (= M5 (ite a!105 O5 (ite a!106 Q5 a!103)))
                  (+ 1 (ite a!105 1 a!107))
                  (+ (- 1) (ite a!105 1 a!107))))
      (a!110 (and (or a!106 (not (= a!104 0))) (= a!107 0))))
(let ((a!39 (and (or a!35 (not (= a!37 0))) (= a!38 0)))
      (a!74 (and (or a!70 (not (= a!72 0))) (= a!73 0)))
      (a!109 (and (or a!105 (not (= a!107 0))) (= a!108 0))))
(let ((a!41 (ite a!39 G3 (ite a!40 I3 (ite a!35 K3 (ite a!36 M3 a!33)))))
      (a!76 (ite a!74 I4 (ite a!75 K4 (ite a!70 M4 (ite a!71 O4 a!68)))))
      (a!111 (ite a!109 K5 (ite a!110 M5 (ite a!105 O5 (ite a!106 Q5 a!103))))))
(let ((a!42 (ite (= E4 a!41)
                 (+ (- 1) (ite (= G4 a!41) 7 8))
                 (ite (= G4 a!41) 7 8)))
      (a!77 (ite (= G5 a!76)
                 (+ (- 1) (ite (= I5 a!76) 7 8))
                 (ite (= I5 a!76) 7 8)))
      (a!112 (ite (= I6 a!111)
                  (+ (- 1) (ite (= K6 a!111) 7 8))
                  (ite (= K6 a!111) 7 8))))
(let ((a!43 (ite (= A4 a!41)
                 (+ (- 1) (ite (= C4 a!41) (+ (- 1) a!42) a!42))
                 (ite (= C4 a!41) (+ (- 1) a!42) a!42)))
      (a!78 (ite (= C5 a!76)
                 (+ (- 1) (ite (= E5 a!76) (+ (- 1) a!77) a!77))
                 (ite (= E5 a!76) (+ (- 1) a!77) a!77)))
      (a!113 (ite (= E6 a!111)
                  (+ (- 1) (ite (= G6 a!111) (+ (- 1) a!112) a!112))
                  (ite (= G6 a!111) (+ (- 1) a!112) a!112))))
(let ((a!44 (ite (= W3 a!41)
                 (+ (- 1) (ite (= Y3 a!41) (+ (- 1) a!43) a!43))
                 (ite (= Y3 a!41) (+ (- 1) a!43) a!43)))
      (a!79 (ite (= Y4 a!76)
                 (+ (- 1) (ite (= A5 a!76) (+ (- 1) a!78) a!78))
                 (ite (= A5 a!76) (+ (- 1) a!78) a!78)))
      (a!114 (ite (= A6 a!111)
                  (+ (- 1) (ite (= C6 a!111) (+ (- 1) a!113) a!113))
                  (ite (= C6 a!111) (+ (- 1) a!113) a!113))))
(let ((a!45 (ite (= S3 a!41)
                 (+ (- 1) (ite (= U3 a!41) (+ (- 1) a!44) a!44))
                 (ite (= U3 a!41) (+ (- 1) a!44) a!44)))
      (a!80 (ite (= U4 a!76)
                 (+ (- 1) (ite (= W4 a!76) (+ (- 1) a!79) a!79))
                 (ite (= W4 a!76) (+ (- 1) a!79) a!79)))
      (a!115 (ite (= W5 a!111)
                  (+ (- 1) (ite (= Y5 a!111) (+ (- 1) a!114) a!114))
                  (ite (= Y5 a!111) (+ (- 1) a!114) a!114))))
(let ((a!46 (ite (= O3 a!41)
                 (+ (- 1) (ite (= Q3 a!41) (+ (- 1) a!45) a!45))
                 (ite (= Q3 a!41) (+ (- 1) a!45) a!45)))
      (a!81 (ite (= Q4 a!76)
                 (+ (- 1) (ite (= S4 a!76) (+ (- 1) a!80) a!80))
                 (ite (= S4 a!76) (+ (- 1) a!80) a!80)))
      (a!116 (ite (= S5 a!111)
                  (+ (- 1) (ite (= U5 a!111) (+ (- 1) a!115) a!115))
                  (ite (= U5 a!111) (+ (- 1) a!115) a!115))))
(let ((a!47 (ite (= K3 a!41)
                 (+ (- 1) (ite (= M3 a!41) (+ (- 1) a!46) a!46))
                 (ite (= M3 a!41) (+ (- 1) a!46) a!46)))
      (a!82 (ite (= M4 a!76)
                 (+ (- 1) (ite (= O4 a!76) (+ (- 1) a!81) a!81))
                 (ite (= O4 a!76) (+ (- 1) a!81) a!81)))
      (a!117 (ite (= O5 a!111)
                  (+ (- 1) (ite (= Q5 a!111) (+ (- 1) a!116) a!116))
                  (ite (= Q5 a!111) (+ (- 1) a!116) a!116))))
(let ((a!48 (= (ite (= I3 a!41) (+ (- 1) a!47) a!47) 0))
      (a!83 (= (ite (= K4 a!76) (+ (- 1) a!82) a!82) 0))
      (a!118 (= (ite (= M5 a!111) (+ (- 1) a!117) a!117) 0)))
(let ((a!49 (ite (= G3 a!41) (= (ite (= I3 a!41) (+ (- 1) a!47) a!47) 1) a!48))
      (a!84 (ite (= I4 a!76) (= (ite (= K4 a!76) (+ (- 1) a!82) a!82) 1) a!83))
      (a!119 (ite (= K5 a!111)
                  (= (ite (= M5 a!111) (+ (- 1) a!117) a!117) 1)
                  a!118)))
(let ((a!50 (or (= (ite (= C4 a!41) (+ (- 1) a!42) a!42) 0)
                (= a!43 0)
                (= (ite (= Y3 a!41) (+ (- 1) a!43) a!43) 0)
                (= a!44 0)
                (= (ite (= U3 a!41) (+ (- 1) a!44) a!44) 0)
                (= a!45 0)
                (= (ite (= Q3 a!41) (+ (- 1) a!45) a!45) 0)
                (= a!46 0)
                (= (ite (= M3 a!41) (+ (- 1) a!46) a!46) 0)
                (= a!47 0)
                a!48
                a!49))
      (a!85 (or (= (ite (= E5 a!76) (+ (- 1) a!77) a!77) 0)
                (= a!78 0)
                (= (ite (= A5 a!76) (+ (- 1) a!78) a!78) 0)
                (= a!79 0)
                (= (ite (= W4 a!76) (+ (- 1) a!79) a!79) 0)
                (= a!80 0)
                (= (ite (= S4 a!76) (+ (- 1) a!80) a!80) 0)
                (= a!81 0)
                (= (ite (= O4 a!76) (+ (- 1) a!81) a!81) 0)
                (= a!82 0)
                a!83
                a!84))
      (a!120 (or (= (ite (= G6 a!111) (+ (- 1) a!112) a!112) 0)
                 (= a!113 0)
                 (= (ite (= C6 a!111) (+ (- 1) a!113) a!113) 0)
                 (= a!114 0)
                 (= (ite (= Y5 a!111) (+ (- 1) a!114) a!114) 0)
                 (= a!115 0)
                 (= (ite (= U5 a!111) (+ (- 1) a!115) a!115) 0)
                 (= a!116 0)
                 (= (ite (= Q5 a!111) (+ (- 1) a!116) a!116) 0)
                 (= a!117 0)
                 a!118
                 a!119)))
(let ((a!121 (and (or (not M6) (= V7 (ite a!50 a!41 0.0)))
                  (or (not O6) (= X7 (ite a!85 a!76 0.0)))
                  (or (not Q6) (= Z7 (ite a!120 a!111 0.0)))
                  (= D4 C4)
                  (= F4 E4)
                  (= H4 G4)
                  (= J4 I4)
                  (= L4 K4)
                  (= N4 M4)
                  (= P4 O4)
                  (= R4 Q4)
                  (= T4 S4)
                  (= V4 U4)
                  (= X4 W4)
                  (= Z4 Y4)
                  (= B5 A5)
                  (= D5 C5)
                  (= F5 E5)
                  (= H5 G5)
                  (= J5 I5)
                  (= L5 K5)
                  (= N5 M5)
                  (= P5 O5)
                  (= R5 Q5)
                  (= T5 S5)
                  (= V5 U5)
                  (= X5 W5)
                  (= Z5 Y5)
                  (= B6 A6)
                  (= D6 C6)
                  (= F6 E6)
                  (= H6 G6)
                  (= J6 I6)
                  (= L6 K6)
                  (= A8 2.0)
                  (= B8 3.0)
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
                  (= J7 I7)
                  (= L7 K7)
                  (= N7 M7)
                  (= P7 O7)
                  (= R7 Q7)
                  (= T7 S7)
                  (= N6 M6)
                  (= P6 O6)
                  (= R6 Q6)
                  (= T6 S6)
                  (= V6 U6)
                  (= X6 W6)
                  (= Z6 Y6)
                  (= B7 A7)
                  (= D7 C7)
                  (= F7 E7)
                  (= H7 G7))))
(let ((a!122 (or (and (or (not K7) (= B5 a!1))
                      (or (not K7) (= D6 a!1))
                      (or (not K7) (= Z3 a!1))
                      (or (not M7) (= D5 a!2))
                      (or (not M7) (= F6 a!2))
                      (or (not M7) (= B4 a!2))
                      (or (not O7) (= D4 a!3))
                      (or (not O7) (= F5 a!3))
                      (or (not O7) (= H6 a!3))
                      (or (not Q7) (= F4 a!4))
                      (or (not Q7) (= H5 a!4))
                      (or (not Q7) (= J6 a!4))
                      (or (not S7) (= H4 a!5))
                      (or (not S7) (= J5 a!5))
                      (or (not S7) (= L6 a!5))
                      (or (not S6) (= J4 a!6))
                      (or (not S6) (= L5 a!6))
                      (or (not S6) (= H3 a!6))
                      (or (not U6) (= L4 a!7))
                      (or (not U6) (= N5 a!7))
                      (or (not U6) (= J3 a!7))
                      (or (not W6) (= N4 a!8))
                      (or (not W6) (= P5 a!8))
                      (or (not W6) (= L3 a!8))
                      (or (not Y6) (= P4 a!9))
                      (or (not Y6) (= R5 a!9))
                      (or (not Y6) (= N3 a!9))
                      (or (not A7) (= R4 a!10))
                      (or (not A7) (= T5 a!10))
                      (or (not A7) (= P3 a!10))
                      (or (not C7) (= T4 a!11))
                      (or (not C7) (= V5 a!11))
                      (or (not C7) (= R3 a!11))
                      (or (not E7) (= V4 a!12))
                      (or (not E7) (= X5 a!12))
                      (or (not E7) (= T3 a!12))
                      (or (not G7) (= X4 a!13))
                      (or (not G7) (= Z5 a!13))
                      (or (not G7) (= V3 a!13))
                      (or (not I7) (= Z4 a!14))
                      (or (not I7) (= B6 a!14))
                      (or (not I7) (= X3 a!14))
                      (= A8 1.0)
                      (= B8 2.0)
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
                      (= B3 A3)
                      (= D3 C3)
                      (= F3 E3)
                      (= V7 U7)
                      (= X7 W7)
                      (= Z7 Y7)
                      (= J7 I7)
                      (= L7 K7)
                      (= N7 M7)
                      (= P7 O7)
                      (= R7 Q7)
                      (= T7 S7)
                      (= N6 M6)
                      (= P6 O6)
                      (= R6 Q6)
                      (= T6 S6)
                      (= V6 U6)
                      (= X6 W6)
                      (= Z6 Y6)
                      (= B7 A7)
                      (= D7 C7)
                      (= F7 E7)
                      (= H7 G7))
                 (and (= D4 C4)
                      (= F4 E4)
                      (= H4 G4)
                      (= J4 I4)
                      (= L4 K4)
                      (= N4 M4)
                      (= P4 O4)
                      (= R4 Q4)
                      (= T4 S4)
                      (= V4 U4)
                      (= X4 W4)
                      (= Z4 Y4)
                      (= B5 A5)
                      (= D5 C5)
                      (= F5 E5)
                      (= H5 G5)
                      (= J5 I5)
                      (= L5 K5)
                      (= N5 M5)
                      (= P5 O5)
                      (= R5 Q5)
                      (= T5 S5)
                      (= V5 U5)
                      (= X5 W5)
                      (= Z5 Y5)
                      (= B6 A6)
                      (= D6 C6)
                      (= F6 E6)
                      (= H6 G6)
                      (= J6 I6)
                      (= L6 K6)
                      (= A8 3.0)
                      (= B8 A8)
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
                      (= V7 U7)
                      (= X7 W7)
                      (= Z7 Y7)
                      (= J7 I7)
                      (= L7 K7)
                      (= N7 M7)
                      (= P7 O7)
                      (= R7 Q7)
                      (= T7 S7)
                      (= N6 M6)
                      (= P6 O6)
                      (= R6 Q6)
                      (= T6 S6)
                      (= V6 U6)
                      (= X6 W6)
                      (= Z6 Y6)
                      (= B7 A7)
                      (= D7 C7)
                      (= F7 E7)
                      (= H7 G7))
                 a!15
                 a!121)))
  (and (= D8 C8) a!122 (= F8 E8)))))))))))))))))))))))))))))
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
           B6
           D6
           F6
           H6
           J6
           L6
           N6
           P6
           R6
           T6
           V6
           X6
           Z6
           B7
           D7
           F7
           H7
           J7
           L7
           N7
           P7
           R7
           T7
           V7
           X7
           Z7
           B8
           D8
           F8)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Bool) (Q3 Bool) (R3 Bool) (S3 Bool) (T3 Bool) (U3 Bool) (V3 Bool) (W3 Bool) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) ) 
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
           A3
           B3
           C3
           D3
           E3
           F3
           G3
           H3
           I3
           J3
           K3
           L3
           M3
           N3
           O3
           P3
           Q3
           R3
           S3
           T3
           U3
           V3
           W3
           X3
           Y3
           Z3
           A4
           B4
           C4)
        (let ((a!1 (or (and H3 (not (= X3 Y3))) (and I3 (not (= X3 Z3)))))
      (a!2 (or (and G3 (not (= Y3 X3))) (and I3 (not (= Y3 Z3)))))
      (a!3 (or (and G3 (not (= Z3 X3))) (and H3 (not (= Z3 Y3))))))
  (and (or (and G3 a!1) (and H3 a!2) (and I3 a!3)) (<= 3.0 A4)))
      )
      false
    )
  )
)

(check-sat)
(exit)
