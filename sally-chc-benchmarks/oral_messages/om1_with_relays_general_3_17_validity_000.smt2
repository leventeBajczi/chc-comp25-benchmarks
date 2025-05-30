(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Bool) (Z3 Bool) (A4 Bool) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Bool) (N4 Bool) (O4 Bool) (P4 Bool) (Q4 Bool) (R4 Bool) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) ) 
    (=>
      (and
        (and (= V4 0.0)
     (= X3 0.0)
     (= W3 0.0)
     (= V3 0.0)
     (= U3 0.0)
     (= T3 0.0)
     (= S3 0.0)
     (= R3 0.0)
     (= Q3 0.0)
     (= P3 0.0)
     (= O3 0.0)
     (= N3 0.0)
     (= M3 0.0)
     (= L3 0.0)
     (= K3 0.0)
     (= J3 0.0)
     (= I3 0.0)
     (= H3 0.0)
     (= G3 0.0)
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
     (or (and (not B4) C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 (not C4) D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 (not D4) E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 (not E4) F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 (not F4) G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 (not G4) H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 (not H4) I4 J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 (not I4) J4 K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 (not J4) K4 L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 (not K4) L4 M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 (not L4) M4 N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 (not M4) N4 O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 (not N4) O4 P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 (not O4) P4 Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 (not P4) Q4 R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 (not Q4) R4)
         (and B4 C4 D4 E4 F4 G4 H4 I4 J4 K4 L4 M4 N4 O4 P4 Q4 (not R4)))
     (or (= W4 1.0) (= W4 2.0) (= W4 3.0))
     (= A4 true)
     (= Z3 true)
     (= Y3 true)
     (not (= X4 0.0)))
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
           C4
           D4
           E4
           F4
           G4
           H4
           I4
           J4
           K4
           L4
           M4
           N4
           O4
           P4
           Q4
           R4
           S4
           T4
           U4
           V4
           W4
           X4)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Real) (R4 Real) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) (Y4 Real) (Z4 Real) (A5 Real) (B5 Real) (C5 Real) (D5 Real) (E5 Real) (F5 Real) (G5 Real) (H5 Real) (I5 Real) (J5 Real) (K5 Real) (L5 Real) (M5 Real) (N5 Real) (O5 Real) (P5 Real) (Q5 Real) (R5 Real) (S5 Real) (T5 Real) (U5 Real) (V5 Real) (W5 Real) (X5 Real) (Y5 Real) (Z5 Real) (A6 Real) (B6 Real) (C6 Real) (D6 Real) (E6 Real) (F6 Real) (G6 Real) (H6 Real) (I6 Real) (J6 Real) (K6 Real) (L6 Real) (M6 Real) (N6 Real) (O6 Real) (P6 Real) (Q6 Real) (R6 Real) (S6 Real) (T6 Real) (U6 Real) (V6 Real) (W6 Real) (X6 Real) (Y6 Real) (Z6 Real) (A7 Real) (B7 Real) (C7 Real) (D7 Real) (E7 Real) (F7 Real) (G7 Real) (H7 Real) (I7 Real) (J7 Real) (K7 Real) (L7 Real) (M7 Real) (N7 Real) (O7 Real) (P7 Real) (Q7 Real) (R7 Real) (S7 Real) (T7 Real) (U7 Real) (V7 Real) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Bool) (S8 Bool) (T8 Bool) (U8 Bool) (V8 Bool) (W8 Bool) (X8 Bool) (Y8 Bool) (Z8 Bool) (A9 Bool) (B9 Bool) (C9 Bool) (D9 Bool) (E9 Bool) (F9 Bool) (G9 Bool) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Real) (L9 Real) (M9 Real) (N9 Real) (O9 Real) (P9 Real) (Q9 Real) (R9 Real) (S9 Real) (T9 Real) (U9 Real) (V9 Real) ) 
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
           E8
           G8
           I8
           K8
           M8
           O8
           Q8
           S8
           U8
           W8
           Y8
           A9
           C9
           E9
           G9
           I9
           K9
           M9
           O9
           Q9
           S9
           U9)
        (let ((a!1 (ite (= S9 3.0) K3 (ite (= S9 2.0) C2 U)))
      (a!2 (ite (= S9 3.0) M3 (ite (= S9 2.0) E2 W)))
      (a!3 (ite (= S9 3.0) O3 (ite (= S9 2.0) G2 Y)))
      (a!4 (ite (= S9 3.0) Q3 (ite (= S9 2.0) I2 A1)))
      (a!5 (ite (= S9 3.0) S3 (ite (= S9 2.0) K2 C1)))
      (a!6 (ite (= S9 3.0) U3 (ite (= S9 2.0) M2 E1)))
      (a!7 (ite (= S9 3.0) W3 (ite (= S9 2.0) O2 G1)))
      (a!8 (ite (= S9 3.0) Q2 (ite (= S9 2.0) I1 A)))
      (a!9 (ite (= S9 3.0) S2 (ite (= S9 2.0) K1 C)))
      (a!10 (ite (= S9 3.0) U2 (ite (= S9 2.0) M1 E)))
      (a!11 (ite (= S9 3.0) W2 (ite (= S9 2.0) O1 G)))
      (a!12 (ite (= S9 3.0) Y2 (ite (= S9 2.0) Q1 I)))
      (a!13 (ite (= S9 3.0) A3 (ite (= S9 2.0) S1 K)))
      (a!14 (ite (= S9 3.0) C3 (ite (= S9 2.0) U1 M)))
      (a!15 (ite (= S9 3.0) E3 (ite (= S9 2.0) W1 O)))
      (a!16 (ite (= S9 3.0) G3 (ite (= S9 2.0) Y1 Q)))
      (a!17 (ite (= S9 3.0) I3 (ite (= S9 2.0) A2 S)))
      (a!18 (and (or (not W7)
                     (and (= B U9)
                          (= D U9)
                          (= F U9)
                          (= H U9)
                          (= J U9)
                          (= L U9)
                          (= N U9)
                          (= P U9)
                          (= R U9)
                          (= T U9)
                          (= V U9)
                          (= X U9)
                          (= Z U9)
                          (= B1 U9)
                          (= D1 U9)
                          (= F1 U9)
                          (= H1 U9))
                     (not (= 1.0 S9)))
                 (or (not W7)
                     (= 1.0 S9)
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
                          (= B1 0.0)
                          (= D1 0.0)
                          (= F1 0.0)
                          (= H1 0.0)))
                 (or (not Y7)
                     (and (= J1 U9)
                          (= L1 U9)
                          (= N1 U9)
                          (= P1 U9)
                          (= R1 U9)
                          (= T1 U9)
                          (= V1 U9)
                          (= X1 U9)
                          (= Z1 U9)
                          (= B2 U9)
                          (= D2 U9)
                          (= F2 U9)
                          (= H2 U9)
                          (= J2 U9)
                          (= L2 U9)
                          (= N2 U9)
                          (= P2 U9))
                     (not (= 2.0 S9)))
                 (or (not Y7)
                     (= 2.0 S9)
                     (and (= J1 0.0)
                          (= L1 0.0)
                          (= N1 0.0)
                          (= P1 0.0)
                          (= R1 0.0)
                          (= T1 0.0)
                          (= V1 0.0)
                          (= X1 0.0)
                          (= Z1 0.0)
                          (= B2 0.0)
                          (= D2 0.0)
                          (= F2 0.0)
                          (= H2 0.0)
                          (= J2 0.0)
                          (= L2 0.0)
                          (= N2 0.0)
                          (= P2 0.0)))
                 (or (not A8)
                     (and (= R2 U9)
                          (= T2 U9)
                          (= V2 U9)
                          (= X2 U9)
                          (= Z2 U9)
                          (= B3 U9)
                          (= D3 U9)
                          (= F3 U9)
                          (= H3 U9)
                          (= J3 U9)
                          (= L3 U9)
                          (= N3 U9)
                          (= P3 U9)
                          (= R3 U9)
                          (= T3 U9)
                          (= V3 U9)
                          (= X3 U9))
                     (not (= 3.0 S9)))
                 (or (not A8)
                     (= 3.0 S9)
                     (and (= R2 0.0)
                          (= T2 0.0)
                          (= V2 0.0)
                          (= X2 0.0)
                          (= Z2 0.0)
                          (= B3 0.0)
                          (= D3 0.0)
                          (= F3 0.0)
                          (= H3 0.0)
                          (= J3 0.0)
                          (= L3 0.0)
                          (= N3 0.0)
                          (= P3 0.0)
                          (= R3 0.0)
                          (= T3 0.0)
                          (= V3 0.0)
                          (= X3 0.0)))
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
                 (= H7 G7)
                 (= J7 I7)
                 (= L7 K7)
                 (= N7 M7)
                 (= P7 O7)
                 (= R7 Q7)
                 (= T7 S7)
                 (= V7 U7)
                 (= Q9 0.0)
                 (= R9 1.0)
                 (= Z3 Y3)
                 (= B4 A4)
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
                 (= L9 K9)
                 (= N9 M9)
                 (= P9 O9)
                 (= X8 W8)
                 (= Z8 Y8)
                 (= B9 A9)
                 (= D9 C9)
                 (= F9 E9)
                 (= H9 G9)
                 (= J9 I9)
                 (= X7 W7)
                 (= Z7 Y7)
                 (= B8 A8)
                 (= D8 C8)
                 (= F8 E8)
                 (= H8 G8)
                 (= J8 I8)
                 (= L8 K8)
                 (= N8 M8)
                 (= P8 O8)
                 (= R8 Q8)
                 (= T8 S8)
                 (= V8 U8)))
      (a!19 (ite (= A5 E5)
                 (+ 1 (ite (= C5 E5) 2 0))
                 (+ (- 1) (ite (= C5 E5) 2 0))))
      (a!61 (ite (= I6 M6)
                 (+ 1 (ite (= K6 M6) 2 0))
                 (+ (- 1) (ite (= K6 M6) 2 0))))
      (a!103 (ite (= Q7 U7)
                  (+ 1 (ite (= S7 U7) 2 0))
                  (+ (- 1) (ite (= S7 U7) 2 0)))))
(let ((a!20 (ite (= Y4 (ite (= C5 E5) E5 A5))
                 (+ 1 (ite (= C5 E5) a!19 1))
                 (+ (- 1) (ite (= C5 E5) a!19 1))))
      (a!22 (ite (and (= C5 E5) (= a!19 0)) Y4 (ite (= C5 E5) E5 A5)))
      (a!62 (ite (= G6 (ite (= K6 M6) M6 I6))
                 (+ 1 (ite (= K6 M6) a!61 1))
                 (+ (- 1) (ite (= K6 M6) a!61 1))))
      (a!64 (ite (and (= K6 M6) (= a!61 0)) G6 (ite (= K6 M6) M6 I6)))
      (a!104 (ite (= O7 (ite (= S7 U7) U7 Q7))
                  (+ 1 (ite (= S7 U7) a!103 1))
                  (+ (- 1) (ite (= S7 U7) a!103 1))))
      (a!106 (ite (and (= S7 U7) (= a!103 0)) O7 (ite (= S7 U7) U7 Q7))))
(let ((a!21 (and (or (not (= C5 E5)) (not (= a!19 0))) (= a!20 0)))
      (a!23 (ite (and (= C5 E5) (= a!19 0)) 1 a!20))
      (a!63 (and (or (not (= K6 M6)) (not (= a!61 0))) (= a!62 0)))
      (a!65 (ite (and (= K6 M6) (= a!61 0)) 1 a!62))
      (a!105 (and (or (not (= S7 U7)) (not (= a!103 0))) (= a!104 0)))
      (a!107 (ite (and (= S7 U7) (= a!103 0)) 1 a!104)))
(let ((a!24 (ite (= W4 a!22) (+ 1 a!23) (+ (- 1) a!23)))
      (a!66 (ite (= E6 a!64) (+ 1 a!65) (+ (- 1) a!65)))
      (a!108 (ite (= M7 a!106) (+ 1 a!107) (+ (- 1) a!107))))
(let ((a!25 (ite (= U4 (ite a!21 W4 a!22))
                 (+ 1 (ite a!21 1 a!24))
                 (+ (- 1) (ite a!21 1 a!24))))
      (a!27 (and (or (and (= C5 E5) (= a!19 0)) (not (= a!20 0))) (= a!24 0)))
      (a!67 (ite (= C6 (ite a!63 E6 a!64))
                 (+ 1 (ite a!63 1 a!66))
                 (+ (- 1) (ite a!63 1 a!66))))
      (a!69 (and (or (and (= K6 M6) (= a!61 0)) (not (= a!62 0))) (= a!66 0)))
      (a!109 (ite (= K7 (ite a!105 M7 a!106))
                  (+ 1 (ite a!105 1 a!108))
                  (+ (- 1) (ite a!105 1 a!108))))
      (a!111 (and (or (and (= S7 U7) (= a!103 0)) (not (= a!104 0)))
                  (= a!108 0))))
(let ((a!26 (and (or a!21 (not (= a!24 0))) (= a!25 0)))
      (a!28 (ite (= S4 (ite a!27 U4 (ite a!21 W4 a!22)))
                 (+ 1 (ite a!27 1 a!25))
                 (+ (- 1) (ite a!27 1 a!25))))
      (a!68 (and (or a!63 (not (= a!66 0))) (= a!67 0)))
      (a!70 (ite (= A6 (ite a!69 C6 (ite a!63 E6 a!64)))
                 (+ 1 (ite a!69 1 a!67))
                 (+ (- 1) (ite a!69 1 a!67))))
      (a!110 (and (or a!105 (not (= a!108 0))) (= a!109 0)))
      (a!112 (ite (= I7 (ite a!111 K7 (ite a!105 M7 a!106)))
                  (+ 1 (ite a!111 1 a!109))
                  (+ (- 1) (ite a!111 1 a!109)))))
(let ((a!29 (ite a!26 S4 (ite a!27 U4 (ite a!21 W4 a!22))))
      (a!32 (and (or a!27 (not (= a!25 0))) (= a!28 0)))
      (a!71 (ite a!68 A6 (ite a!69 C6 (ite a!63 E6 a!64))))
      (a!74 (and (or a!69 (not (= a!67 0))) (= a!70 0)))
      (a!113 (ite a!110 I7 (ite a!111 K7 (ite a!105 M7 a!106))))
      (a!116 (and (or a!111 (not (= a!109 0))) (= a!112 0))))
(let ((a!30 (ite (= Q4 a!29)
                 (+ 1 (ite a!26 1 a!28))
                 (+ (- 1) (ite a!26 1 a!28))))
      (a!72 (ite (= Y5 a!71)
                 (+ 1 (ite a!68 1 a!70))
                 (+ (- 1) (ite a!68 1 a!70))))
      (a!114 (ite (= G7 a!113)
                  (+ 1 (ite a!110 1 a!112))
                  (+ (- 1) (ite a!110 1 a!112)))))
(let ((a!31 (and (or a!26 (not (= a!28 0))) (= a!30 0)))
      (a!33 (ite (= O4 (ite a!32 Q4 a!29))
                 (+ 1 (ite a!32 1 a!30))
                 (+ (- 1) (ite a!32 1 a!30))))
      (a!73 (and (or a!68 (not (= a!70 0))) (= a!72 0)))
      (a!75 (ite (= W5 (ite a!74 Y5 a!71))
                 (+ 1 (ite a!74 1 a!72))
                 (+ (- 1) (ite a!74 1 a!72))))
      (a!115 (and (or a!110 (not (= a!112 0))) (= a!114 0)))
      (a!117 (ite (= E7 (ite a!116 G7 a!113))
                  (+ 1 (ite a!116 1 a!114))
                  (+ (- 1) (ite a!116 1 a!114)))))
(let ((a!34 (ite (= M4 (ite a!31 O4 (ite a!32 Q4 a!29)))
                 (+ 1 (ite a!31 1 a!33))
                 (+ (- 1) (ite a!31 1 a!33))))
      (a!36 (and (or a!32 (not (= a!30 0))) (= a!33 0)))
      (a!76 (ite (= U5 (ite a!73 W5 (ite a!74 Y5 a!71)))
                 (+ 1 (ite a!73 1 a!75))
                 (+ (- 1) (ite a!73 1 a!75))))
      (a!78 (and (or a!74 (not (= a!72 0))) (= a!75 0)))
      (a!118 (ite (= C7 (ite a!115 E7 (ite a!116 G7 a!113)))
                  (+ 1 (ite a!115 1 a!117))
                  (+ (- 1) (ite a!115 1 a!117))))
      (a!120 (and (or a!116 (not (= a!114 0))) (= a!117 0))))
(let ((a!35 (and (or a!31 (not (= a!33 0))) (= a!34 0)))
      (a!37 (ite a!36 M4 (ite a!31 O4 (ite a!32 Q4 a!29))))
      (a!77 (and (or a!73 (not (= a!75 0))) (= a!76 0)))
      (a!79 (ite a!78 U5 (ite a!73 W5 (ite a!74 Y5 a!71))))
      (a!119 (and (or a!115 (not (= a!117 0))) (= a!118 0)))
      (a!121 (ite a!120 C7 (ite a!115 E7 (ite a!116 G7 a!113)))))
(let ((a!38 (ite (= K4 a!37)
                 (+ 1 (ite a!36 1 a!34))
                 (+ (- 1) (ite a!36 1 a!34))))
      (a!80 (ite (= S5 a!79)
                 (+ 1 (ite a!78 1 a!76))
                 (+ (- 1) (ite a!78 1 a!76))))
      (a!122 (ite (= A7 a!121)
                  (+ 1 (ite a!120 1 a!118))
                  (+ (- 1) (ite a!120 1 a!118)))))
(let ((a!39 (ite (= I4 (ite a!35 K4 a!37))
                 (+ 1 (ite a!35 1 a!38))
                 (+ (- 1) (ite a!35 1 a!38))))
      (a!41 (and (or a!36 (not (= a!34 0))) (= a!38 0)))
      (a!81 (ite (= Q5 (ite a!77 S5 a!79))
                 (+ 1 (ite a!77 1 a!80))
                 (+ (- 1) (ite a!77 1 a!80))))
      (a!83 (and (or a!78 (not (= a!76 0))) (= a!80 0)))
      (a!123 (ite (= Y6 (ite a!119 A7 a!121))
                  (+ 1 (ite a!119 1 a!122))
                  (+ (- 1) (ite a!119 1 a!122))))
      (a!125 (and (or a!120 (not (= a!118 0))) (= a!122 0))))
(let ((a!40 (and (or a!35 (not (= a!38 0))) (= a!39 0)))
      (a!42 (ite (= G4 (ite a!41 I4 (ite a!35 K4 a!37)))
                 (+ 1 (ite a!41 1 a!39))
                 (+ (- 1) (ite a!41 1 a!39))))
      (a!82 (and (or a!77 (not (= a!80 0))) (= a!81 0)))
      (a!84 (ite (= O5 (ite a!83 Q5 (ite a!77 S5 a!79)))
                 (+ 1 (ite a!83 1 a!81))
                 (+ (- 1) (ite a!83 1 a!81))))
      (a!124 (and (or a!119 (not (= a!122 0))) (= a!123 0)))
      (a!126 (ite (= W6 (ite a!125 Y6 (ite a!119 A7 a!121)))
                  (+ 1 (ite a!125 1 a!123))
                  (+ (- 1) (ite a!125 1 a!123)))))
(let ((a!43 (ite a!40 G4 (ite a!41 I4 (ite a!35 K4 a!37))))
      (a!46 (and (or a!41 (not (= a!39 0))) (= a!42 0)))
      (a!85 (ite a!82 O5 (ite a!83 Q5 (ite a!77 S5 a!79))))
      (a!88 (and (or a!83 (not (= a!81 0))) (= a!84 0)))
      (a!127 (ite a!124 W6 (ite a!125 Y6 (ite a!119 A7 a!121))))
      (a!130 (and (or a!125 (not (= a!123 0))) (= a!126 0))))
(let ((a!44 (ite (= E4 a!43)
                 (+ 1 (ite a!40 1 a!42))
                 (+ (- 1) (ite a!40 1 a!42))))
      (a!86 (ite (= M5 a!85)
                 (+ 1 (ite a!82 1 a!84))
                 (+ (- 1) (ite a!82 1 a!84))))
      (a!128 (ite (= U6 a!127)
                  (+ 1 (ite a!124 1 a!126))
                  (+ (- 1) (ite a!124 1 a!126)))))
(let ((a!45 (and (or a!40 (not (= a!42 0))) (= a!44 0)))
      (a!47 (ite (= C4 (ite a!46 E4 a!43))
                 (+ 1 (ite a!46 1 a!44))
                 (+ (- 1) (ite a!46 1 a!44))))
      (a!87 (and (or a!82 (not (= a!84 0))) (= a!86 0)))
      (a!89 (ite (= K5 (ite a!88 M5 a!85))
                 (+ 1 (ite a!88 1 a!86))
                 (+ (- 1) (ite a!88 1 a!86))))
      (a!129 (and (or a!124 (not (= a!126 0))) (= a!128 0)))
      (a!131 (ite (= S6 (ite a!130 U6 a!127))
                  (+ 1 (ite a!130 1 a!128))
                  (+ (- 1) (ite a!130 1 a!128)))))
(let ((a!48 (ite (= A4 (ite a!45 C4 (ite a!46 E4 a!43)))
                 (+ 1 (ite a!45 1 a!47))
                 (+ (- 1) (ite a!45 1 a!47))))
      (a!50 (and (or a!46 (not (= a!44 0))) (= a!47 0)))
      (a!90 (ite (= I5 (ite a!87 K5 (ite a!88 M5 a!85)))
                 (+ 1 (ite a!87 1 a!89))
                 (+ (- 1) (ite a!87 1 a!89))))
      (a!92 (and (or a!88 (not (= a!86 0))) (= a!89 0)))
      (a!132 (ite (= Q6 (ite a!129 S6 (ite a!130 U6 a!127)))
                  (+ 1 (ite a!129 1 a!131))
                  (+ (- 1) (ite a!129 1 a!131))))
      (a!134 (and (or a!130 (not (= a!128 0))) (= a!131 0))))
(let ((a!49 (and (or a!45 (not (= a!47 0))) (= a!48 0)))
      (a!91 (and (or a!87 (not (= a!89 0))) (= a!90 0)))
      (a!133 (and (or a!129 (not (= a!131 0))) (= a!132 0))))
(let ((a!51 (ite a!49 Y3 (ite a!50 A4 (ite a!45 C4 (ite a!46 E4 a!43)))))
      (a!93 (ite a!91 G5 (ite a!92 I5 (ite a!87 K5 (ite a!88 M5 a!85)))))
      (a!135 (ite a!133 O6 (ite a!134 Q6 (ite a!129 S6 (ite a!130 U6 a!127))))))
(let ((a!52 (ite (= C5 a!51)
                 (+ (- 1) (ite (= E5 a!51) 8 9))
                 (ite (= E5 a!51) 8 9)))
      (a!94 (ite (= K6 a!93)
                 (+ (- 1) (ite (= M6 a!93) 8 9))
                 (ite (= M6 a!93) 8 9)))
      (a!136 (ite (= S7 a!135)
                  (+ (- 1) (ite (= U7 a!135) 8 9))
                  (ite (= U7 a!135) 8 9))))
(let ((a!53 (ite (= Y4 a!51)
                 (+ (- 1) (ite (= A5 a!51) (+ (- 1) a!52) a!52))
                 (ite (= A5 a!51) (+ (- 1) a!52) a!52)))
      (a!95 (ite (= G6 a!93)
                 (+ (- 1) (ite (= I6 a!93) (+ (- 1) a!94) a!94))
                 (ite (= I6 a!93) (+ (- 1) a!94) a!94)))
      (a!137 (ite (= O7 a!135)
                  (+ (- 1) (ite (= Q7 a!135) (+ (- 1) a!136) a!136))
                  (ite (= Q7 a!135) (+ (- 1) a!136) a!136))))
(let ((a!54 (ite (= U4 a!51)
                 (+ (- 1) (ite (= W4 a!51) (+ (- 1) a!53) a!53))
                 (ite (= W4 a!51) (+ (- 1) a!53) a!53)))
      (a!96 (ite (= C6 a!93)
                 (+ (- 1) (ite (= E6 a!93) (+ (- 1) a!95) a!95))
                 (ite (= E6 a!93) (+ (- 1) a!95) a!95)))
      (a!138 (ite (= K7 a!135)
                  (+ (- 1) (ite (= M7 a!135) (+ (- 1) a!137) a!137))
                  (ite (= M7 a!135) (+ (- 1) a!137) a!137))))
(let ((a!55 (ite (= Q4 a!51)
                 (+ (- 1) (ite (= S4 a!51) (+ (- 1) a!54) a!54))
                 (ite (= S4 a!51) (+ (- 1) a!54) a!54)))
      (a!97 (ite (= Y5 a!93)
                 (+ (- 1) (ite (= A6 a!93) (+ (- 1) a!96) a!96))
                 (ite (= A6 a!93) (+ (- 1) a!96) a!96)))
      (a!139 (ite (= G7 a!135)
                  (+ (- 1) (ite (= I7 a!135) (+ (- 1) a!138) a!138))
                  (ite (= I7 a!135) (+ (- 1) a!138) a!138))))
(let ((a!56 (ite (= M4 a!51)
                 (+ (- 1) (ite (= O4 a!51) (+ (- 1) a!55) a!55))
                 (ite (= O4 a!51) (+ (- 1) a!55) a!55)))
      (a!98 (ite (= U5 a!93)
                 (+ (- 1) (ite (= W5 a!93) (+ (- 1) a!97) a!97))
                 (ite (= W5 a!93) (+ (- 1) a!97) a!97)))
      (a!140 (ite (= C7 a!135)
                  (+ (- 1) (ite (= E7 a!135) (+ (- 1) a!139) a!139))
                  (ite (= E7 a!135) (+ (- 1) a!139) a!139))))
(let ((a!57 (ite (= I4 a!51)
                 (+ (- 1) (ite (= K4 a!51) (+ (- 1) a!56) a!56))
                 (ite (= K4 a!51) (+ (- 1) a!56) a!56)))
      (a!99 (ite (= Q5 a!93)
                 (+ (- 1) (ite (= S5 a!93) (+ (- 1) a!98) a!98))
                 (ite (= S5 a!93) (+ (- 1) a!98) a!98)))
      (a!141 (ite (= Y6 a!135)
                  (+ (- 1) (ite (= A7 a!135) (+ (- 1) a!140) a!140))
                  (ite (= A7 a!135) (+ (- 1) a!140) a!140))))
(let ((a!58 (ite (= E4 a!51)
                 (+ (- 1) (ite (= G4 a!51) (+ (- 1) a!57) a!57))
                 (ite (= G4 a!51) (+ (- 1) a!57) a!57)))
      (a!100 (ite (= M5 a!93)
                  (+ (- 1) (ite (= O5 a!93) (+ (- 1) a!99) a!99))
                  (ite (= O5 a!93) (+ (- 1) a!99) a!99)))
      (a!142 (ite (= U6 a!135)
                  (+ (- 1) (ite (= W6 a!135) (+ (- 1) a!141) a!141))
                  (ite (= W6 a!135) (+ (- 1) a!141) a!141))))
(let ((a!59 (ite (= A4 a!51)
                 (+ (- 1) (ite (= C4 a!51) (+ (- 1) a!58) a!58))
                 (ite (= C4 a!51) (+ (- 1) a!58) a!58)))
      (a!101 (ite (= I5 a!93)
                  (+ (- 1) (ite (= K5 a!93) (+ (- 1) a!100) a!100))
                  (ite (= K5 a!93) (+ (- 1) a!100) a!100)))
      (a!143 (ite (= Q6 a!135)
                  (+ (- 1) (ite (= S6 a!135) (+ (- 1) a!142) a!142))
                  (ite (= S6 a!135) (+ (- 1) a!142) a!142))))
(let ((a!60 (or (= (ite (= A5 a!51) (+ (- 1) a!52) a!52) 0)
                (= a!53 0)
                (= (ite (= W4 a!51) (+ (- 1) a!53) a!53) 0)
                (= a!54 0)
                (= (ite (= S4 a!51) (+ (- 1) a!54) a!54) 0)
                (= a!55 0)
                (= (ite (= O4 a!51) (+ (- 1) a!55) a!55) 0)
                (= a!56 0)
                (= (ite (= K4 a!51) (+ (- 1) a!56) a!56) 0)
                (= a!57 0)
                (= (ite (= G4 a!51) (+ (- 1) a!57) a!57) 0)
                (= a!58 0)
                (= (ite (= C4 a!51) (+ (- 1) a!58) a!58) 0)
                (= a!59 0)
                (ite (= Y3 a!51) (= a!59 1) (= a!59 0))))
      (a!102 (or (= (ite (= I6 a!93) (+ (- 1) a!94) a!94) 0)
                 (= a!95 0)
                 (= (ite (= E6 a!93) (+ (- 1) a!95) a!95) 0)
                 (= a!96 0)
                 (= (ite (= A6 a!93) (+ (- 1) a!96) a!96) 0)
                 (= a!97 0)
                 (= (ite (= W5 a!93) (+ (- 1) a!97) a!97) 0)
                 (= a!98 0)
                 (= (ite (= S5 a!93) (+ (- 1) a!98) a!98) 0)
                 (= a!99 0)
                 (= (ite (= O5 a!93) (+ (- 1) a!99) a!99) 0)
                 (= a!100 0)
                 (= (ite (= K5 a!93) (+ (- 1) a!100) a!100) 0)
                 (= a!101 0)
                 (ite (= G5 a!93) (= a!101 1) (= a!101 0))))
      (a!144 (or (= (ite (= Q7 a!135) (+ (- 1) a!136) a!136) 0)
                 (= a!137 0)
                 (= (ite (= M7 a!135) (+ (- 1) a!137) a!137) 0)
                 (= a!138 0)
                 (= (ite (= I7 a!135) (+ (- 1) a!138) a!138) 0)
                 (= a!139 0)
                 (= (ite (= E7 a!135) (+ (- 1) a!139) a!139) 0)
                 (= a!140 0)
                 (= (ite (= A7 a!135) (+ (- 1) a!140) a!140) 0)
                 (= a!141 0)
                 (= (ite (= W6 a!135) (+ (- 1) a!141) a!141) 0)
                 (= a!142 0)
                 (= (ite (= S6 a!135) (+ (- 1) a!142) a!142) 0)
                 (= a!143 0)
                 (ite (= O6 a!135) (= a!143 1) (= a!143 0)))))
(let ((a!145 (and (or (not W7) (= L9 (ite a!60 a!51 0.0)))
                  (or (not Y7) (= N9 (ite a!102 a!93 0.0)))
                  (or (not A8) (= P9 (ite a!144 a!135 0.0)))
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
                  (= H7 G7)
                  (= J7 I7)
                  (= L7 K7)
                  (= N7 M7)
                  (= P7 O7)
                  (= R7 Q7)
                  (= T7 S7)
                  (= V7 U7)
                  (= Q9 2.0)
                  (= R9 3.0)
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
                  (= X8 W8)
                  (= Z8 Y8)
                  (= B9 A9)
                  (= D9 C9)
                  (= F9 E9)
                  (= H9 G9)
                  (= J9 I9)
                  (= X7 W7)
                  (= Z7 Y7)
                  (= B8 A8)
                  (= D8 C8)
                  (= F8 E8)
                  (= H8 G8)
                  (= J8 I8)
                  (= L8 K8)
                  (= N8 M8)
                  (= P8 O8)
                  (= R8 Q8)
                  (= T8 S8)
                  (= V8 U8))))
(let ((a!146 (or (and (or (not W8) (= B6 a!1))
                      (or (not W8) (= J7 a!1))
                      (or (not W8) (= T4 a!1))
                      (or (not Y8) (= D6 a!2))
                      (or (not Y8) (= L7 a!2))
                      (or (not Y8) (= V4 a!2))
                      (or (not A9) (= F6 a!3))
                      (or (not A9) (= N7 a!3))
                      (or (not A9) (= X4 a!3))
                      (or (not C9) (= Z4 a!4))
                      (or (not C9) (= H6 a!4))
                      (or (not C9) (= P7 a!4))
                      (or (not E9) (= B5 a!5))
                      (or (not E9) (= J6 a!5))
                      (or (not E9) (= R7 a!5))
                      (or (not G9) (= D5 a!6))
                      (or (not G9) (= L6 a!6))
                      (or (not G9) (= T7 a!6))
                      (or (not I9) (= F5 a!7))
                      (or (not I9) (= N6 a!7))
                      (or (not I9) (= V7 a!7))
                      (or (not C8) (= H5 a!8))
                      (or (not C8) (= P6 a!8))
                      (or (not C8) (= Z3 a!8))
                      (or (not E8) (= J5 a!9))
                      (or (not E8) (= R6 a!9))
                      (or (not E8) (= B4 a!9))
                      (or (not G8) (= L5 a!10))
                      (or (not G8) (= T6 a!10))
                      (or (not G8) (= D4 a!10))
                      (or (not I8) (= N5 a!11))
                      (or (not I8) (= V6 a!11))
                      (or (not I8) (= F4 a!11))
                      (or (not K8) (= P5 a!12))
                      (or (not K8) (= X6 a!12))
                      (or (not K8) (= H4 a!12))
                      (or (not M8) (= R5 a!13))
                      (or (not M8) (= Z6 a!13))
                      (or (not M8) (= J4 a!13))
                      (or (not O8) (= T5 a!14))
                      (or (not O8) (= B7 a!14))
                      (or (not O8) (= L4 a!14))
                      (or (not Q8) (= V5 a!15))
                      (or (not Q8) (= D7 a!15))
                      (or (not Q8) (= N4 a!15))
                      (or (not S8) (= X5 a!16))
                      (or (not S8) (= F7 a!16))
                      (or (not S8) (= P4 a!16))
                      (or (not U8) (= Z5 a!17))
                      (or (not U8) (= H7 a!17))
                      (or (not U8) (= R4 a!17))
                      (= Q9 1.0)
                      (= R9 2.0)
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
                      (= L9 K9)
                      (= N9 M9)
                      (= P9 O9)
                      (= X8 W8)
                      (= Z8 Y8)
                      (= B9 A9)
                      (= D9 C9)
                      (= F9 E9)
                      (= H9 G9)
                      (= J9 I9)
                      (= X7 W7)
                      (= Z7 Y7)
                      (= B8 A8)
                      (= D8 C8)
                      (= F8 E8)
                      (= H8 G8)
                      (= J8 I8)
                      (= L8 K8)
                      (= N8 M8)
                      (= P8 O8)
                      (= R8 Q8)
                      (= T8 S8)
                      (= V8 U8))
                 (and (= Z4 Y4)
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
                      (= H7 G7)
                      (= J7 I7)
                      (= L7 K7)
                      (= N7 M7)
                      (= P7 O7)
                      (= R7 Q7)
                      (= T7 S7)
                      (= V7 U7)
                      (= Q9 3.0)
                      (= R9 Q9)
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
                      (= L9 K9)
                      (= N9 M9)
                      (= P9 O9)
                      (= X8 W8)
                      (= Z8 Y8)
                      (= B9 A9)
                      (= D9 C9)
                      (= F9 E9)
                      (= H9 G9)
                      (= J9 I9)
                      (= X7 W7)
                      (= Z7 Y7)
                      (= B8 A8)
                      (= D8 C8)
                      (= F8 E8)
                      (= H8 G8)
                      (= J8 I8)
                      (= L8 K8)
                      (= N8 M8)
                      (= P8 O8)
                      (= R8 Q8)
                      (= T8 S8)
                      (= V8 U8))
                 a!18
                 a!145)))
  (and (= T9 S9) a!146 (= V9 U9)))))))))))))))))))))))))))))))))
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
           F8
           H8
           J8
           L8
           N8
           P8
           R8
           T8
           V8
           X8
           Z8
           B9
           D9
           F9
           H9
           J9
           L9
           N9
           P9
           R9
           T9
           V9)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Bool) (Z3 Bool) (A4 Bool) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Bool) (N4 Bool) (O4 Bool) (P4 Bool) (Q4 Bool) (R4 Bool) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) ) 
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
           C4
           D4
           E4
           F4
           G4
           H4
           I4
           J4
           K4
           L4
           M4
           N4
           O4
           P4
           Q4
           R4
           S4
           T4
           U4
           V4
           W4
           X4)
        (let ((a!1 (or (and Y3 (not (= S4 X4)))
               (and Z3 (not (= T4 X4)))
               (and A4 (not (= U4 X4))))))
  (and (<= 3.0 V4) a!1 (ite (= W4 3.0) A4 (ite (= W4 2.0) Z3 Y3))))
      )
      false
    )
  )
)

(check-sat)
(exit)
