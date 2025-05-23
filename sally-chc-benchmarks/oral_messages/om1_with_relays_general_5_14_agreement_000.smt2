(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Real) (R4 Real) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) (Y4 Real) (Z4 Real) (A5 Real) (B5 Real) (C5 Real) (D5 Real) (E5 Real) (F5 Real) (G5 Real) (H5 Real) (I5 Real) (J5 Real) (K5 Bool) (L5 Bool) (M5 Bool) (N5 Bool) (O5 Bool) (P5 Bool) (Q5 Bool) (R5 Bool) (S5 Bool) (T5 Bool) (U5 Bool) (V5 Bool) (W5 Bool) (X5 Bool) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Real) (E6 Real) (F6 Real) (G6 Real) (H6 Real) (I6 Real) (J6 Real) (K6 Real) ) 
    (=>
      (and
        (and (= I6 0.0)
     (= J5 0.0)
     (= I5 0.0)
     (= H5 0.0)
     (= G5 0.0)
     (= F5 0.0)
     (= E5 0.0)
     (= D5 0.0)
     (= C5 0.0)
     (= B5 0.0)
     (= A5 0.0)
     (= Z4 0.0)
     (= Y4 0.0)
     (= X4 0.0)
     (= W4 0.0)
     (= V4 0.0)
     (= U4 0.0)
     (= T4 0.0)
     (= S4 0.0)
     (= R4 0.0)
     (= Q4 0.0)
     (= P4 0.0)
     (= O4 0.0)
     (= N4 0.0)
     (= M4 0.0)
     (= L4 0.0)
     (= K4 0.0)
     (= J4 0.0)
     (= I4 0.0)
     (= H4 0.0)
     (= G4 0.0)
     (= F4 0.0)
     (= E4 0.0)
     (= D4 0.0)
     (= C4 0.0)
     (= B4 0.0)
     (= A4 0.0)
     (= Z3 0.0)
     (= Y3 0.0)
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
     (or (and (not P5) Q5 R5 S5 T5 U5 V5 W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 (not Q5) R5 S5 T5 U5 V5 W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 (not R5) S5 T5 U5 V5 W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 (not S5) T5 U5 V5 W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 (not T5) U5 V5 W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 T5 (not U5) V5 W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 T5 U5 (not V5) W5 X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 T5 U5 V5 (not W5) X5 Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 T5 U5 V5 W5 (not X5) Y5 Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 T5 U5 V5 W5 X5 (not Y5) Z5 A6 B6 C6)
         (and P5 Q5 R5 S5 T5 U5 V5 W5 X5 Y5 (not Z5) A6 B6 C6)
         (and P5 Q5 R5 S5 T5 U5 V5 W5 X5 Y5 Z5 (not A6) B6 C6)
         (and P5 Q5 R5 S5 T5 U5 V5 W5 X5 Y5 Z5 A6 (not B6) C6)
         (and P5 Q5 R5 S5 T5 U5 V5 W5 X5 Y5 Z5 A6 B6 (not C6)))
     (or (= J6 1.0) (= J6 2.0) (= J6 3.0) (= J6 4.0) (= J6 5.0))
     (= O5 true)
     (= N5 true)
     (= M5 true)
     (= L5 true)
     (= K5 true)
     (not (= K6 0.0)))
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
           X4
           Y4
           Z4
           A5
           B5
           C5
           D5
           E5
           F5
           G5
           H5
           I5
           J5
           K5
           L5
           M5
           N5
           O5
           P5
           Q5
           R5
           S5
           T5
           U5
           V5
           W5
           X5
           Y5
           Z5
           A6
           B6
           C6
           D6
           E6
           F6
           G6
           H6
           I6
           J6
           K6)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Real) (R4 Real) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) (Y4 Real) (Z4 Real) (A5 Real) (B5 Real) (C5 Real) (D5 Real) (E5 Real) (F5 Real) (G5 Real) (H5 Real) (I5 Real) (J5 Real) (K5 Real) (L5 Real) (M5 Real) (N5 Real) (O5 Real) (P5 Real) (Q5 Real) (R5 Real) (S5 Real) (T5 Real) (U5 Real) (V5 Real) (W5 Real) (X5 Real) (Y5 Real) (Z5 Real) (A6 Real) (B6 Real) (C6 Real) (D6 Real) (E6 Real) (F6 Real) (G6 Real) (H6 Real) (I6 Real) (J6 Real) (K6 Real) (L6 Real) (M6 Real) (N6 Real) (O6 Real) (P6 Real) (Q6 Real) (R6 Real) (S6 Real) (T6 Real) (U6 Real) (V6 Real) (W6 Real) (X6 Real) (Y6 Real) (Z6 Real) (A7 Real) (B7 Real) (C7 Real) (D7 Real) (E7 Real) (F7 Real) (G7 Real) (H7 Real) (I7 Real) (J7 Real) (K7 Real) (L7 Real) (M7 Real) (N7 Real) (O7 Real) (P7 Real) (Q7 Real) (R7 Real) (S7 Real) (T7 Real) (U7 Real) (V7 Real) (W7 Real) (X7 Real) (Y7 Real) (Z7 Real) (A8 Real) (B8 Real) (C8 Real) (D8 Real) (E8 Real) (F8 Real) (G8 Real) (H8 Real) (I8 Real) (J8 Real) (K8 Real) (L8 Real) (M8 Real) (N8 Real) (O8 Real) (P8 Real) (Q8 Real) (R8 Real) (S8 Real) (T8 Real) (U8 Real) (V8 Real) (W8 Real) (X8 Real) (Y8 Real) (Z8 Real) (A9 Real) (B9 Real) (C9 Real) (D9 Real) (E9 Real) (F9 Real) (G9 Real) (H9 Real) (I9 Real) (J9 Real) (K9 Real) (L9 Real) (M9 Real) (N9 Real) (O9 Real) (P9 Real) (Q9 Real) (R9 Real) (S9 Real) (T9 Real) (U9 Real) (V9 Real) (W9 Real) (X9 Real) (Y9 Real) (Z9 Real) (A10 Real) (B10 Real) (C10 Real) (D10 Real) (E10 Real) (F10 Real) (G10 Real) (H10 Real) (I10 Real) (J10 Real) (K10 Real) (L10 Real) (M10 Real) (N10 Real) (O10 Real) (P10 Real) (Q10 Real) (R10 Real) (S10 Real) (T10 Real) (U10 Bool) (V10 Bool) (W10 Bool) (X10 Bool) (Y10 Bool) (Z10 Bool) (A11 Bool) (B11 Bool) (C11 Bool) (D11 Bool) (E11 Bool) (F11 Bool) (G11 Bool) (H11 Bool) (I11 Bool) (J11 Bool) (K11 Bool) (L11 Bool) (M11 Bool) (N11 Bool) (O11 Bool) (P11 Bool) (Q11 Bool) (R11 Bool) (S11 Bool) (T11 Bool) (U11 Bool) (V11 Bool) (W11 Bool) (X11 Bool) (Y11 Bool) (Z11 Bool) (A12 Bool) (B12 Bool) (C12 Bool) (D12 Bool) (E12 Bool) (F12 Bool) (G12 Real) (H12 Real) (I12 Real) (J12 Real) (K12 Real) (L12 Real) (M12 Real) (N12 Real) (O12 Real) (P12 Real) (Q12 Real) (R12 Real) (S12 Real) (T12 Real) (U12 Real) (V12 Real) ) 
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
           U9
           W9
           Y9
           A10
           C10
           E10
           G10
           I10
           K10
           M10
           O10
           Q10
           S10
           U10
           W10
           Y10
           A11
           C11
           E11
           G11
           I11
           K11
           M11
           O11
           Q11
           S11
           U11
           W11
           Y11
           A12
           C12
           E12
           G12
           I12
           K12
           M12
           O12
           Q12
           S12
           U12)
        (let ((a!1 (ite (= S12 4.0) Y3 (ite (= S12 3.0) W2 (ite (= S12 2.0) U1 S))))
      (a!7 (ite (= S12 4.0) A4 (ite (= S12 3.0) Y2 (ite (= S12 2.0) W1 U))))
      (a!13 (ite (= S12 4.0) C4 (ite (= S12 3.0) A3 (ite (= S12 2.0) Y1 W))))
      (a!19 (ite (= S12 4.0) E4 (ite (= S12 3.0) C3 (ite (= S12 2.0) A2 Y))))
      (a!25 (ite (= S12 4.0) G4 (ite (= S12 3.0) E3 (ite (= S12 2.0) C2 A1))))
      (a!31 (ite (= S12 4.0) G3 (ite (= S12 3.0) E2 (ite (= S12 2.0) C1 A))))
      (a!37 (ite (= S12 4.0) I3 (ite (= S12 3.0) G2 (ite (= S12 2.0) E1 C))))
      (a!43 (ite (= S12 4.0) K3 (ite (= S12 3.0) I2 (ite (= S12 2.0) G1 E))))
      (a!49 (ite (= S12 4.0) M3 (ite (= S12 3.0) K2 (ite (= S12 2.0) I1 G))))
      (a!55 (ite (= S12 4.0) O3 (ite (= S12 3.0) M2 (ite (= S12 2.0) K1 I))))
      (a!61 (ite (= S12 4.0) Q3 (ite (= S12 3.0) O2 (ite (= S12 2.0) M1 K))))
      (a!67 (ite (= S12 4.0) S3 (ite (= S12 3.0) Q2 (ite (= S12 2.0) O1 M))))
      (a!73 (ite (= S12 4.0) U3 (ite (= S12 3.0) S2 (ite (= S12 2.0) Q1 O))))
      (a!79 (ite (= S12 4.0) W3 (ite (= S12 3.0) U2 (ite (= S12 2.0) S1 Q))))
      (a!85 (and (or (not U10)
                     (and (= B U12)
                          (= D U12)
                          (= F U12)
                          (= H U12)
                          (= J U12)
                          (= L U12)
                          (= N U12)
                          (= P U12)
                          (= R U12)
                          (= T U12)
                          (= V U12)
                          (= X U12)
                          (= Z U12)
                          (= B1 U12))
                     (not (= 1.0 S12)))
                 (or (not U10)
                     (= 1.0 S12)
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
                 (or (not W10)
                     (and (= D1 U12)
                          (= F1 U12)
                          (= H1 U12)
                          (= J1 U12)
                          (= L1 U12)
                          (= N1 U12)
                          (= P1 U12)
                          (= R1 U12)
                          (= T1 U12)
                          (= V1 U12)
                          (= X1 U12)
                          (= Z1 U12)
                          (= B2 U12)
                          (= D2 U12))
                     (not (= 2.0 S12)))
                 (or (not W10)
                     (= 2.0 S12)
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
                 (or (not Y10)
                     (and (= F2 U12)
                          (= H2 U12)
                          (= J2 U12)
                          (= L2 U12)
                          (= N2 U12)
                          (= P2 U12)
                          (= R2 U12)
                          (= T2 U12)
                          (= V2 U12)
                          (= X2 U12)
                          (= Z2 U12)
                          (= B3 U12)
                          (= D3 U12)
                          (= F3 U12))
                     (not (= 3.0 S12)))
                 (or (not Y10)
                     (= 3.0 S12)
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
                 (or (not A11)
                     (and (= H3 U12)
                          (= J3 U12)
                          (= L3 U12)
                          (= N3 U12)
                          (= P3 U12)
                          (= R3 U12)
                          (= T3 U12)
                          (= V3 U12)
                          (= X3 U12)
                          (= Z3 U12)
                          (= B4 U12)
                          (= D4 U12)
                          (= F4 U12)
                          (= H4 U12))
                     (not (= 4.0 S12)))
                 (or (not A11)
                     (= 4.0 S12)
                     (and (= H3 0.0)
                          (= J3 0.0)
                          (= L3 0.0)
                          (= N3 0.0)
                          (= P3 0.0)
                          (= R3 0.0)
                          (= T3 0.0)
                          (= V3 0.0)
                          (= X3 0.0)
                          (= Z3 0.0)
                          (= B4 0.0)
                          (= D4 0.0)
                          (= F4 0.0)
                          (= H4 0.0)))
                 (or (not C11)
                     (and (= J4 U12)
                          (= L4 U12)
                          (= N4 U12)
                          (= P4 U12)
                          (= R4 U12)
                          (= T4 U12)
                          (= V4 U12)
                          (= X4 U12)
                          (= Z4 U12)
                          (= B5 U12)
                          (= D5 U12)
                          (= F5 U12)
                          (= H5 U12)
                          (= J5 U12))
                     (not (= 5.0 S12)))
                 (or (not C11)
                     (= 5.0 S12)
                     (and (= J4 0.0)
                          (= L4 0.0)
                          (= N4 0.0)
                          (= P4 0.0)
                          (= R4 0.0)
                          (= T4 0.0)
                          (= V4 0.0)
                          (= X4 0.0)
                          (= Z4 0.0)
                          (= B5 0.0)
                          (= D5 0.0)
                          (= F5 0.0)
                          (= H5 0.0)
                          (= J5 0.0)))
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
                 (= V8 U8)
                 (= X8 W8)
                 (= Z8 Y8)
                 (= B9 A9)
                 (= D9 C9)
                 (= F9 E9)
                 (= H9 G9)
                 (= J9 I9)
                 (= L9 K9)
                 (= N9 M9)
                 (= P9 O9)
                 (= R9 Q9)
                 (= T9 S9)
                 (= V9 U9)
                 (= X9 W9)
                 (= Z9 Y9)
                 (= B10 A10)
                 (= D10 C10)
                 (= F10 E10)
                 (= H10 G10)
                 (= J10 I10)
                 (= L10 K10)
                 (= N10 M10)
                 (= P10 O10)
                 (= R10 Q10)
                 (= T10 S10)
                 (= P12 O12)
                 (= Q12 0.0)
                 (= R12 1.0)
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
                 (= H12 G12)
                 (= J12 I12)
                 (= L12 K12)
                 (= N12 M12)
                 (= V11 U11)
                 (= X11 W11)
                 (= Z11 Y11)
                 (= B12 A12)
                 (= D12 C12)
                 (= F12 E12)
                 (= V10 U10)
                 (= X10 W10)
                 (= Z10 Y10)
                 (= B11 A11)
                 (= D11 C11)
                 (= F11 E11)
                 (= H11 G11)
                 (= J11 I11)
                 (= L11 K11)
                 (= N11 M11)
                 (= P11 O11)
                 (= R11 Q11)
                 (= T11 S11)))
      (a!86 (ite (= G6 K6)
                 (+ 1 (ite (= I6 K6) 2 0))
                 (+ (- 1) (ite (= I6 K6) 2 0))))
      (a!121 (ite (= I7 M7)
                  (+ 1 (ite (= K7 M7) 2 0))
                  (+ (- 1) (ite (= K7 M7) 2 0))))
      (a!156 (ite (= K8 O8)
                  (+ 1 (ite (= M8 O8) 2 0))
                  (+ (- 1) (ite (= M8 O8) 2 0))))
      (a!191 (ite (= M9 Q9)
                  (+ 1 (ite (= O9 Q9) 2 0))
                  (+ (- 1) (ite (= O9 Q9) 2 0))))
      (a!226 (ite (= O10 S10)
                  (+ 1 (ite (= Q10 S10) 2 0))
                  (+ (- 1) (ite (= Q10 S10) 2 0)))))
(let ((a!2 (or (not W11) (= F7 (ite (= S12 5.0) A5 a!1))))
      (a!3 (or (not W11) (= H8 (ite (= S12 5.0) A5 a!1))))
      (a!4 (or (not W11) (= J9 (ite (= S12 5.0) A5 a!1))))
      (a!5 (or (not W11) (= L10 (ite (= S12 5.0) A5 a!1))))
      (a!6 (or (not W11) (= D6 (ite (= S12 5.0) A5 a!1))))
      (a!8 (or (not Y11) (= H7 (ite (= S12 5.0) C5 a!7))))
      (a!9 (or (not Y11) (= J8 (ite (= S12 5.0) C5 a!7))))
      (a!10 (or (not Y11) (= L9 (ite (= S12 5.0) C5 a!7))))
      (a!11 (or (not Y11) (= N10 (ite (= S12 5.0) C5 a!7))))
      (a!12 (or (not Y11) (= F6 (ite (= S12 5.0) C5 a!7))))
      (a!14 (or (not A12) (= J7 (ite (= S12 5.0) E5 a!13))))
      (a!15 (or (not A12) (= L8 (ite (= S12 5.0) E5 a!13))))
      (a!16 (or (not A12) (= N9 (ite (= S12 5.0) E5 a!13))))
      (a!17 (or (not A12) (= P10 (ite (= S12 5.0) E5 a!13))))
      (a!18 (or (not A12) (= H6 (ite (= S12 5.0) E5 a!13))))
      (a!20 (or (not C12) (= L7 (ite (= S12 5.0) G5 a!19))))
      (a!21 (or (not C12) (= N8 (ite (= S12 5.0) G5 a!19))))
      (a!22 (or (not C12) (= P9 (ite (= S12 5.0) G5 a!19))))
      (a!23 (or (not C12) (= R10 (ite (= S12 5.0) G5 a!19))))
      (a!24 (or (not C12) (= J6 (ite (= S12 5.0) G5 a!19))))
      (a!26 (or (not E12) (= L6 (ite (= S12 5.0) I5 a!25))))
      (a!27 (or (not E12) (= N7 (ite (= S12 5.0) I5 a!25))))
      (a!28 (or (not E12) (= P8 (ite (= S12 5.0) I5 a!25))))
      (a!29 (or (not E12) (= R9 (ite (= S12 5.0) I5 a!25))))
      (a!30 (or (not E12) (= T10 (ite (= S12 5.0) I5 a!25))))
      (a!32 (or (not E11) (= N6 (ite (= S12 5.0) I4 a!31))))
      (a!33 (or (not E11) (= P7 (ite (= S12 5.0) I4 a!31))))
      (a!34 (or (not E11) (= R8 (ite (= S12 5.0) I4 a!31))))
      (a!35 (or (not E11) (= T9 (ite (= S12 5.0) I4 a!31))))
      (a!36 (or (not E11) (= L5 (ite (= S12 5.0) I4 a!31))))
      (a!38 (or (not G11) (= P6 (ite (= S12 5.0) K4 a!37))))
      (a!39 (or (not G11) (= R7 (ite (= S12 5.0) K4 a!37))))
      (a!40 (or (not G11) (= T8 (ite (= S12 5.0) K4 a!37))))
      (a!41 (or (not G11) (= V9 (ite (= S12 5.0) K4 a!37))))
      (a!42 (or (not G11) (= N5 (ite (= S12 5.0) K4 a!37))))
      (a!44 (or (not I11) (= R6 (ite (= S12 5.0) M4 a!43))))
      (a!45 (or (not I11) (= T7 (ite (= S12 5.0) M4 a!43))))
      (a!46 (or (not I11) (= V8 (ite (= S12 5.0) M4 a!43))))
      (a!47 (or (not I11) (= X9 (ite (= S12 5.0) M4 a!43))))
      (a!48 (or (not I11) (= P5 (ite (= S12 5.0) M4 a!43))))
      (a!50 (or (not K11) (= T6 (ite (= S12 5.0) O4 a!49))))
      (a!51 (or (not K11) (= V7 (ite (= S12 5.0) O4 a!49))))
      (a!52 (or (not K11) (= X8 (ite (= S12 5.0) O4 a!49))))
      (a!53 (or (not K11) (= Z9 (ite (= S12 5.0) O4 a!49))))
      (a!54 (or (not K11) (= R5 (ite (= S12 5.0) O4 a!49))))
      (a!56 (or (not M11) (= V6 (ite (= S12 5.0) Q4 a!55))))
      (a!57 (or (not M11) (= X7 (ite (= S12 5.0) Q4 a!55))))
      (a!58 (or (not M11) (= Z8 (ite (= S12 5.0) Q4 a!55))))
      (a!59 (or (not M11) (= B10 (ite (= S12 5.0) Q4 a!55))))
      (a!60 (or (not M11) (= T5 (ite (= S12 5.0) Q4 a!55))))
      (a!62 (or (not O11) (= X6 (ite (= S12 5.0) S4 a!61))))
      (a!63 (or (not O11) (= Z7 (ite (= S12 5.0) S4 a!61))))
      (a!64 (or (not O11) (= B9 (ite (= S12 5.0) S4 a!61))))
      (a!65 (or (not O11) (= D10 (ite (= S12 5.0) S4 a!61))))
      (a!66 (or (not O11) (= V5 (ite (= S12 5.0) S4 a!61))))
      (a!68 (or (not Q11) (= Z6 (ite (= S12 5.0) U4 a!67))))
      (a!69 (or (not Q11) (= B8 (ite (= S12 5.0) U4 a!67))))
      (a!70 (or (not Q11) (= D9 (ite (= S12 5.0) U4 a!67))))
      (a!71 (or (not Q11) (= F10 (ite (= S12 5.0) U4 a!67))))
      (a!72 (or (not Q11) (= X5 (ite (= S12 5.0) U4 a!67))))
      (a!74 (or (not S11) (= B7 (ite (= S12 5.0) W4 a!73))))
      (a!75 (or (not S11) (= D8 (ite (= S12 5.0) W4 a!73))))
      (a!76 (or (not S11) (= F9 (ite (= S12 5.0) W4 a!73))))
      (a!77 (or (not S11) (= H10 (ite (= S12 5.0) W4 a!73))))
      (a!78 (or (not S11) (= Z5 (ite (= S12 5.0) W4 a!73))))
      (a!80 (or (not U11) (= D7 (ite (= S12 5.0) Y4 a!79))))
      (a!81 (or (not U11) (= F8 (ite (= S12 5.0) Y4 a!79))))
      (a!82 (or (not U11) (= H9 (ite (= S12 5.0) Y4 a!79))))
      (a!83 (or (not U11) (= J10 (ite (= S12 5.0) Y4 a!79))))
      (a!84 (or (not U11) (= B6 (ite (= S12 5.0) Y4 a!79))))
      (a!87 (ite (= E6 (ite (= I6 K6) K6 G6))
                 (+ 1 (ite (= I6 K6) a!86 1))
                 (+ (- 1) (ite (= I6 K6) a!86 1))))
      (a!88 (ite (and (= I6 K6) (= a!86 0)) E6 (ite (= I6 K6) K6 G6)))
      (a!122 (ite (= G7 (ite (= K7 M7) M7 I7))
                  (+ 1 (ite (= K7 M7) a!121 1))
                  (+ (- 1) (ite (= K7 M7) a!121 1))))
      (a!123 (ite (and (= K7 M7) (= a!121 0)) G7 (ite (= K7 M7) M7 I7)))
      (a!157 (ite (= I8 (ite (= M8 O8) O8 K8))
                  (+ 1 (ite (= M8 O8) a!156 1))
                  (+ (- 1) (ite (= M8 O8) a!156 1))))
      (a!158 (ite (and (= M8 O8) (= a!156 0)) I8 (ite (= M8 O8) O8 K8)))
      (a!192 (ite (= K9 (ite (= O9 Q9) Q9 M9))
                  (+ 1 (ite (= O9 Q9) a!191 1))
                  (+ (- 1) (ite (= O9 Q9) a!191 1))))
      (a!193 (ite (and (= O9 Q9) (= a!191 0)) K9 (ite (= O9 Q9) Q9 M9)))
      (a!227 (ite (= M10 (ite (= Q10 S10) S10 O10))
                  (+ 1 (ite (= Q10 S10) a!226 1))
                  (+ (- 1) (ite (= Q10 S10) a!226 1))))
      (a!228 (ite (and (= Q10 S10) (= a!226 0)) M10 (ite (= Q10 S10) S10 O10))))
(let ((a!89 (ite (and (= I6 K6) (= a!86 0)) 1 a!87))
      (a!92 (and (or (not (= I6 K6)) (not (= a!86 0))) (= a!87 0)))
      (a!124 (ite (and (= K7 M7) (= a!121 0)) 1 a!122))
      (a!127 (and (or (not (= K7 M7)) (not (= a!121 0))) (= a!122 0)))
      (a!159 (ite (and (= M8 O8) (= a!156 0)) 1 a!157))
      (a!162 (and (or (not (= M8 O8)) (not (= a!156 0))) (= a!157 0)))
      (a!194 (ite (and (= O9 Q9) (= a!191 0)) 1 a!192))
      (a!197 (and (or (not (= O9 Q9)) (not (= a!191 0))) (= a!192 0)))
      (a!229 (ite (and (= Q10 S10) (= a!226 0)) 1 a!227))
      (a!232 (and (or (not (= Q10 S10)) (not (= a!226 0))) (= a!227 0))))
(let ((a!90 (ite (= C6 a!88) (+ 1 a!89) (+ (- 1) a!89)))
      (a!125 (ite (= E7 a!123) (+ 1 a!124) (+ (- 1) a!124)))
      (a!160 (ite (= G8 a!158) (+ 1 a!159) (+ (- 1) a!159)))
      (a!195 (ite (= I9 a!193) (+ 1 a!194) (+ (- 1) a!194)))
      (a!230 (ite (= K10 a!228) (+ 1 a!229) (+ (- 1) a!229))))
(let ((a!91 (and (or (and (= I6 K6) (= a!86 0)) (not (= a!87 0))) (= a!90 0)))
      (a!93 (ite (= A6 (ite a!92 C6 a!88))
                 (+ 1 (ite a!92 1 a!90))
                 (+ (- 1) (ite a!92 1 a!90))))
      (a!126 (and (or (and (= K7 M7) (= a!121 0)) (not (= a!122 0)))
                  (= a!125 0)))
      (a!128 (ite (= C7 (ite a!127 E7 a!123))
                  (+ 1 (ite a!127 1 a!125))
                  (+ (- 1) (ite a!127 1 a!125))))
      (a!161 (and (or (and (= M8 O8) (= a!156 0)) (not (= a!157 0)))
                  (= a!160 0)))
      (a!163 (ite (= E8 (ite a!162 G8 a!158))
                  (+ 1 (ite a!162 1 a!160))
                  (+ (- 1) (ite a!162 1 a!160))))
      (a!196 (and (or (and (= O9 Q9) (= a!191 0)) (not (= a!192 0)))
                  (= a!195 0)))
      (a!198 (ite (= G9 (ite a!197 I9 a!193))
                  (+ 1 (ite a!197 1 a!195))
                  (+ (- 1) (ite a!197 1 a!195))))
      (a!231 (and (or (and (= Q10 S10) (= a!226 0)) (not (= a!227 0)))
                  (= a!230 0)))
      (a!233 (ite (= I10 (ite a!232 K10 a!228))
                  (+ 1 (ite a!232 1 a!230))
                  (+ (- 1) (ite a!232 1 a!230)))))
(let ((a!94 (ite (= Y5 (ite a!91 A6 (ite a!92 C6 a!88)))
                 (+ 1 (ite a!91 1 a!93))
                 (+ (- 1) (ite a!91 1 a!93))))
      (a!96 (and (or a!92 (not (= a!90 0))) (= a!93 0)))
      (a!129 (ite (= A7 (ite a!126 C7 (ite a!127 E7 a!123)))
                  (+ 1 (ite a!126 1 a!128))
                  (+ (- 1) (ite a!126 1 a!128))))
      (a!131 (and (or a!127 (not (= a!125 0))) (= a!128 0)))
      (a!164 (ite (= C8 (ite a!161 E8 (ite a!162 G8 a!158)))
                  (+ 1 (ite a!161 1 a!163))
                  (+ (- 1) (ite a!161 1 a!163))))
      (a!166 (and (or a!162 (not (= a!160 0))) (= a!163 0)))
      (a!199 (ite (= E9 (ite a!196 G9 (ite a!197 I9 a!193)))
                  (+ 1 (ite a!196 1 a!198))
                  (+ (- 1) (ite a!196 1 a!198))))
      (a!201 (and (or a!197 (not (= a!195 0))) (= a!198 0)))
      (a!234 (ite (= G10 (ite a!231 I10 (ite a!232 K10 a!228)))
                  (+ 1 (ite a!231 1 a!233))
                  (+ (- 1) (ite a!231 1 a!233))))
      (a!236 (and (or a!232 (not (= a!230 0))) (= a!233 0))))
(let ((a!95 (and (or a!91 (not (= a!93 0))) (= a!94 0)))
      (a!97 (ite a!96 Y5 (ite a!91 A6 (ite a!92 C6 a!88))))
      (a!130 (and (or a!126 (not (= a!128 0))) (= a!129 0)))
      (a!132 (ite a!131 A7 (ite a!126 C7 (ite a!127 E7 a!123))))
      (a!165 (and (or a!161 (not (= a!163 0))) (= a!164 0)))
      (a!167 (ite a!166 C8 (ite a!161 E8 (ite a!162 G8 a!158))))
      (a!200 (and (or a!196 (not (= a!198 0))) (= a!199 0)))
      (a!202 (ite a!201 E9 (ite a!196 G9 (ite a!197 I9 a!193))))
      (a!235 (and (or a!231 (not (= a!233 0))) (= a!234 0)))
      (a!237 (ite a!236 G10 (ite a!231 I10 (ite a!232 K10 a!228)))))
(let ((a!98 (ite (= W5 a!97)
                 (+ 1 (ite a!96 1 a!94))
                 (+ (- 1) (ite a!96 1 a!94))))
      (a!133 (ite (= Y6 a!132)
                  (+ 1 (ite a!131 1 a!129))
                  (+ (- 1) (ite a!131 1 a!129))))
      (a!168 (ite (= A8 a!167)
                  (+ 1 (ite a!166 1 a!164))
                  (+ (- 1) (ite a!166 1 a!164))))
      (a!203 (ite (= C9 a!202)
                  (+ 1 (ite a!201 1 a!199))
                  (+ (- 1) (ite a!201 1 a!199))))
      (a!238 (ite (= E10 a!237)
                  (+ 1 (ite a!236 1 a!234))
                  (+ (- 1) (ite a!236 1 a!234)))))
(let ((a!99 (ite (= U5 (ite a!95 W5 a!97))
                 (+ 1 (ite a!95 1 a!98))
                 (+ (- 1) (ite a!95 1 a!98))))
      (a!101 (and (or a!96 (not (= a!94 0))) (= a!98 0)))
      (a!134 (ite (= W6 (ite a!130 Y6 a!132))
                  (+ 1 (ite a!130 1 a!133))
                  (+ (- 1) (ite a!130 1 a!133))))
      (a!136 (and (or a!131 (not (= a!129 0))) (= a!133 0)))
      (a!169 (ite (= Y7 (ite a!165 A8 a!167))
                  (+ 1 (ite a!165 1 a!168))
                  (+ (- 1) (ite a!165 1 a!168))))
      (a!171 (and (or a!166 (not (= a!164 0))) (= a!168 0)))
      (a!204 (ite (= A9 (ite a!200 C9 a!202))
                  (+ 1 (ite a!200 1 a!203))
                  (+ (- 1) (ite a!200 1 a!203))))
      (a!206 (and (or a!201 (not (= a!199 0))) (= a!203 0)))
      (a!239 (ite (= C10 (ite a!235 E10 a!237))
                  (+ 1 (ite a!235 1 a!238))
                  (+ (- 1) (ite a!235 1 a!238))))
      (a!241 (and (or a!236 (not (= a!234 0))) (= a!238 0))))
(let ((a!100 (and (or a!95 (not (= a!98 0))) (= a!99 0)))
      (a!102 (ite (= S5 (ite a!101 U5 (ite a!95 W5 a!97)))
                  (+ 1 (ite a!101 1 a!99))
                  (+ (- 1) (ite a!101 1 a!99))))
      (a!135 (and (or a!130 (not (= a!133 0))) (= a!134 0)))
      (a!137 (ite (= U6 (ite a!136 W6 (ite a!130 Y6 a!132)))
                  (+ 1 (ite a!136 1 a!134))
                  (+ (- 1) (ite a!136 1 a!134))))
      (a!170 (and (or a!165 (not (= a!168 0))) (= a!169 0)))
      (a!172 (ite (= W7 (ite a!171 Y7 (ite a!165 A8 a!167)))
                  (+ 1 (ite a!171 1 a!169))
                  (+ (- 1) (ite a!171 1 a!169))))
      (a!205 (and (or a!200 (not (= a!203 0))) (= a!204 0)))
      (a!207 (ite (= Y8 (ite a!206 A9 (ite a!200 C9 a!202)))
                  (+ 1 (ite a!206 1 a!204))
                  (+ (- 1) (ite a!206 1 a!204))))
      (a!240 (and (or a!235 (not (= a!238 0))) (= a!239 0)))
      (a!242 (ite (= A10 (ite a!241 C10 (ite a!235 E10 a!237)))
                  (+ 1 (ite a!241 1 a!239))
                  (+ (- 1) (ite a!241 1 a!239)))))
(let ((a!103 (ite a!100 S5 (ite a!101 U5 (ite a!95 W5 a!97))))
      (a!106 (and (or a!101 (not (= a!99 0))) (= a!102 0)))
      (a!138 (ite a!135 U6 (ite a!136 W6 (ite a!130 Y6 a!132))))
      (a!141 (and (or a!136 (not (= a!134 0))) (= a!137 0)))
      (a!173 (ite a!170 W7 (ite a!171 Y7 (ite a!165 A8 a!167))))
      (a!176 (and (or a!171 (not (= a!169 0))) (= a!172 0)))
      (a!208 (ite a!205 Y8 (ite a!206 A9 (ite a!200 C9 a!202))))
      (a!211 (and (or a!206 (not (= a!204 0))) (= a!207 0)))
      (a!243 (ite a!240 A10 (ite a!241 C10 (ite a!235 E10 a!237))))
      (a!246 (and (or a!241 (not (= a!239 0))) (= a!242 0))))
(let ((a!104 (ite (= Q5 a!103)
                  (+ 1 (ite a!100 1 a!102))
                  (+ (- 1) (ite a!100 1 a!102))))
      (a!139 (ite (= S6 a!138)
                  (+ 1 (ite a!135 1 a!137))
                  (+ (- 1) (ite a!135 1 a!137))))
      (a!174 (ite (= U7 a!173)
                  (+ 1 (ite a!170 1 a!172))
                  (+ (- 1) (ite a!170 1 a!172))))
      (a!209 (ite (= W8 a!208)
                  (+ 1 (ite a!205 1 a!207))
                  (+ (- 1) (ite a!205 1 a!207))))
      (a!244 (ite (= Y9 a!243)
                  (+ 1 (ite a!240 1 a!242))
                  (+ (- 1) (ite a!240 1 a!242)))))
(let ((a!105 (and (or a!100 (not (= a!102 0))) (= a!104 0)))
      (a!107 (ite (= O5 (ite a!106 Q5 a!103))
                  (+ 1 (ite a!106 1 a!104))
                  (+ (- 1) (ite a!106 1 a!104))))
      (a!140 (and (or a!135 (not (= a!137 0))) (= a!139 0)))
      (a!142 (ite (= Q6 (ite a!141 S6 a!138))
                  (+ 1 (ite a!141 1 a!139))
                  (+ (- 1) (ite a!141 1 a!139))))
      (a!175 (and (or a!170 (not (= a!172 0))) (= a!174 0)))
      (a!177 (ite (= S7 (ite a!176 U7 a!173))
                  (+ 1 (ite a!176 1 a!174))
                  (+ (- 1) (ite a!176 1 a!174))))
      (a!210 (and (or a!205 (not (= a!207 0))) (= a!209 0)))
      (a!212 (ite (= U8 (ite a!211 W8 a!208))
                  (+ 1 (ite a!211 1 a!209))
                  (+ (- 1) (ite a!211 1 a!209))))
      (a!245 (and (or a!240 (not (= a!242 0))) (= a!244 0)))
      (a!247 (ite (= W9 (ite a!246 Y9 a!243))
                  (+ 1 (ite a!246 1 a!244))
                  (+ (- 1) (ite a!246 1 a!244)))))
(let ((a!108 (ite (= M5 (ite a!105 O5 (ite a!106 Q5 a!103)))
                  (+ 1 (ite a!105 1 a!107))
                  (+ (- 1) (ite a!105 1 a!107))))
      (a!110 (and (or a!106 (not (= a!104 0))) (= a!107 0)))
      (a!143 (ite (= O6 (ite a!140 Q6 (ite a!141 S6 a!138)))
                  (+ 1 (ite a!140 1 a!142))
                  (+ (- 1) (ite a!140 1 a!142))))
      (a!145 (and (or a!141 (not (= a!139 0))) (= a!142 0)))
      (a!178 (ite (= Q7 (ite a!175 S7 (ite a!176 U7 a!173)))
                  (+ 1 (ite a!175 1 a!177))
                  (+ (- 1) (ite a!175 1 a!177))))
      (a!180 (and (or a!176 (not (= a!174 0))) (= a!177 0)))
      (a!213 (ite (= S8 (ite a!210 U8 (ite a!211 W8 a!208)))
                  (+ 1 (ite a!210 1 a!212))
                  (+ (- 1) (ite a!210 1 a!212))))
      (a!215 (and (or a!211 (not (= a!209 0))) (= a!212 0)))
      (a!248 (ite (= U9 (ite a!245 W9 (ite a!246 Y9 a!243)))
                  (+ 1 (ite a!245 1 a!247))
                  (+ (- 1) (ite a!245 1 a!247))))
      (a!250 (and (or a!246 (not (= a!244 0))) (= a!247 0))))
(let ((a!109 (and (or a!105 (not (= a!107 0))) (= a!108 0)))
      (a!144 (and (or a!140 (not (= a!142 0))) (= a!143 0)))
      (a!179 (and (or a!175 (not (= a!177 0))) (= a!178 0)))
      (a!214 (and (or a!210 (not (= a!212 0))) (= a!213 0)))
      (a!249 (and (or a!245 (not (= a!247 0))) (= a!248 0))))
(let ((a!111 (ite a!109 K5 (ite a!110 M5 (ite a!105 O5 (ite a!106 Q5 a!103)))))
      (a!146 (ite a!144 M6 (ite a!145 O6 (ite a!140 Q6 (ite a!141 S6 a!138)))))
      (a!181 (ite a!179 O7 (ite a!180 Q7 (ite a!175 S7 (ite a!176 U7 a!173)))))
      (a!216 (ite a!214 Q8 (ite a!215 S8 (ite a!210 U8 (ite a!211 W8 a!208)))))
      (a!251 (ite a!249 S9 (ite a!250 U9 (ite a!245 W9 (ite a!246 Y9 a!243))))))
(let ((a!112 (ite (= I6 a!111)
                  (+ (- 1) (ite (= K6 a!111) 7 8))
                  (ite (= K6 a!111) 7 8)))
      (a!147 (ite (= K7 a!146)
                  (+ (- 1) (ite (= M7 a!146) 7 8))
                  (ite (= M7 a!146) 7 8)))
      (a!182 (ite (= M8 a!181)
                  (+ (- 1) (ite (= O8 a!181) 7 8))
                  (ite (= O8 a!181) 7 8)))
      (a!217 (ite (= O9 a!216)
                  (+ (- 1) (ite (= Q9 a!216) 7 8))
                  (ite (= Q9 a!216) 7 8)))
      (a!252 (ite (= Q10 a!251)
                  (+ (- 1) (ite (= S10 a!251) 7 8))
                  (ite (= S10 a!251) 7 8))))
(let ((a!113 (ite (= E6 a!111)
                  (+ (- 1) (ite (= G6 a!111) (+ (- 1) a!112) a!112))
                  (ite (= G6 a!111) (+ (- 1) a!112) a!112)))
      (a!148 (ite (= G7 a!146)
                  (+ (- 1) (ite (= I7 a!146) (+ (- 1) a!147) a!147))
                  (ite (= I7 a!146) (+ (- 1) a!147) a!147)))
      (a!183 (ite (= I8 a!181)
                  (+ (- 1) (ite (= K8 a!181) (+ (- 1) a!182) a!182))
                  (ite (= K8 a!181) (+ (- 1) a!182) a!182)))
      (a!218 (ite (= K9 a!216)
                  (+ (- 1) (ite (= M9 a!216) (+ (- 1) a!217) a!217))
                  (ite (= M9 a!216) (+ (- 1) a!217) a!217)))
      (a!253 (ite (= M10 a!251)
                  (+ (- 1) (ite (= O10 a!251) (+ (- 1) a!252) a!252))
                  (ite (= O10 a!251) (+ (- 1) a!252) a!252))))
(let ((a!114 (ite (= A6 a!111)
                  (+ (- 1) (ite (= C6 a!111) (+ (- 1) a!113) a!113))
                  (ite (= C6 a!111) (+ (- 1) a!113) a!113)))
      (a!149 (ite (= C7 a!146)
                  (+ (- 1) (ite (= E7 a!146) (+ (- 1) a!148) a!148))
                  (ite (= E7 a!146) (+ (- 1) a!148) a!148)))
      (a!184 (ite (= E8 a!181)
                  (+ (- 1) (ite (= G8 a!181) (+ (- 1) a!183) a!183))
                  (ite (= G8 a!181) (+ (- 1) a!183) a!183)))
      (a!219 (ite (= G9 a!216)
                  (+ (- 1) (ite (= I9 a!216) (+ (- 1) a!218) a!218))
                  (ite (= I9 a!216) (+ (- 1) a!218) a!218)))
      (a!254 (ite (= I10 a!251)
                  (+ (- 1) (ite (= K10 a!251) (+ (- 1) a!253) a!253))
                  (ite (= K10 a!251) (+ (- 1) a!253) a!253))))
(let ((a!115 (ite (= W5 a!111)
                  (+ (- 1) (ite (= Y5 a!111) (+ (- 1) a!114) a!114))
                  (ite (= Y5 a!111) (+ (- 1) a!114) a!114)))
      (a!150 (ite (= Y6 a!146)
                  (+ (- 1) (ite (= A7 a!146) (+ (- 1) a!149) a!149))
                  (ite (= A7 a!146) (+ (- 1) a!149) a!149)))
      (a!185 (ite (= A8 a!181)
                  (+ (- 1) (ite (= C8 a!181) (+ (- 1) a!184) a!184))
                  (ite (= C8 a!181) (+ (- 1) a!184) a!184)))
      (a!220 (ite (= C9 a!216)
                  (+ (- 1) (ite (= E9 a!216) (+ (- 1) a!219) a!219))
                  (ite (= E9 a!216) (+ (- 1) a!219) a!219)))
      (a!255 (ite (= E10 a!251)
                  (+ (- 1) (ite (= G10 a!251) (+ (- 1) a!254) a!254))
                  (ite (= G10 a!251) (+ (- 1) a!254) a!254))))
(let ((a!116 (ite (= S5 a!111)
                  (+ (- 1) (ite (= U5 a!111) (+ (- 1) a!115) a!115))
                  (ite (= U5 a!111) (+ (- 1) a!115) a!115)))
      (a!151 (ite (= U6 a!146)
                  (+ (- 1) (ite (= W6 a!146) (+ (- 1) a!150) a!150))
                  (ite (= W6 a!146) (+ (- 1) a!150) a!150)))
      (a!186 (ite (= W7 a!181)
                  (+ (- 1) (ite (= Y7 a!181) (+ (- 1) a!185) a!185))
                  (ite (= Y7 a!181) (+ (- 1) a!185) a!185)))
      (a!221 (ite (= Y8 a!216)
                  (+ (- 1) (ite (= A9 a!216) (+ (- 1) a!220) a!220))
                  (ite (= A9 a!216) (+ (- 1) a!220) a!220)))
      (a!256 (ite (= A10 a!251)
                  (+ (- 1) (ite (= C10 a!251) (+ (- 1) a!255) a!255))
                  (ite (= C10 a!251) (+ (- 1) a!255) a!255))))
(let ((a!117 (ite (= O5 a!111)
                  (+ (- 1) (ite (= Q5 a!111) (+ (- 1) a!116) a!116))
                  (ite (= Q5 a!111) (+ (- 1) a!116) a!116)))
      (a!152 (ite (= Q6 a!146)
                  (+ (- 1) (ite (= S6 a!146) (+ (- 1) a!151) a!151))
                  (ite (= S6 a!146) (+ (- 1) a!151) a!151)))
      (a!187 (ite (= S7 a!181)
                  (+ (- 1) (ite (= U7 a!181) (+ (- 1) a!186) a!186))
                  (ite (= U7 a!181) (+ (- 1) a!186) a!186)))
      (a!222 (ite (= U8 a!216)
                  (+ (- 1) (ite (= W8 a!216) (+ (- 1) a!221) a!221))
                  (ite (= W8 a!216) (+ (- 1) a!221) a!221)))
      (a!257 (ite (= W9 a!251)
                  (+ (- 1) (ite (= Y9 a!251) (+ (- 1) a!256) a!256))
                  (ite (= Y9 a!251) (+ (- 1) a!256) a!256))))
(let ((a!118 (= (ite (= M5 a!111) (+ (- 1) a!117) a!117) 0))
      (a!153 (= (ite (= O6 a!146) (+ (- 1) a!152) a!152) 0))
      (a!188 (= (ite (= Q7 a!181) (+ (- 1) a!187) a!187) 0))
      (a!223 (= (ite (= S8 a!216) (+ (- 1) a!222) a!222) 0))
      (a!258 (= (ite (= U9 a!251) (+ (- 1) a!257) a!257) 0)))
(let ((a!119 (ite (= K5 a!111)
                  (= (ite (= M5 a!111) (+ (- 1) a!117) a!117) 1)
                  a!118))
      (a!154 (ite (= M6 a!146)
                  (= (ite (= O6 a!146) (+ (- 1) a!152) a!152) 1)
                  a!153))
      (a!189 (ite (= O7 a!181)
                  (= (ite (= Q7 a!181) (+ (- 1) a!187) a!187) 1)
                  a!188))
      (a!224 (ite (= Q8 a!216)
                  (= (ite (= S8 a!216) (+ (- 1) a!222) a!222) 1)
                  a!223))
      (a!259 (ite (= S9 a!251)
                  (= (ite (= U9 a!251) (+ (- 1) a!257) a!257) 1)
                  a!258)))
(let ((a!120 (or (= (ite (= G6 a!111) (+ (- 1) a!112) a!112) 0)
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
                 a!119))
      (a!155 (or (= (ite (= I7 a!146) (+ (- 1) a!147) a!147) 0)
                 (= a!148 0)
                 (= (ite (= E7 a!146) (+ (- 1) a!148) a!148) 0)
                 (= a!149 0)
                 (= (ite (= A7 a!146) (+ (- 1) a!149) a!149) 0)
                 (= a!150 0)
                 (= (ite (= W6 a!146) (+ (- 1) a!150) a!150) 0)
                 (= a!151 0)
                 (= (ite (= S6 a!146) (+ (- 1) a!151) a!151) 0)
                 (= a!152 0)
                 a!153
                 a!154))
      (a!190 (or (= (ite (= K8 a!181) (+ (- 1) a!182) a!182) 0)
                 (= a!183 0)
                 (= (ite (= G8 a!181) (+ (- 1) a!183) a!183) 0)
                 (= a!184 0)
                 (= (ite (= C8 a!181) (+ (- 1) a!184) a!184) 0)
                 (= a!185 0)
                 (= (ite (= Y7 a!181) (+ (- 1) a!185) a!185) 0)
                 (= a!186 0)
                 (= (ite (= U7 a!181) (+ (- 1) a!186) a!186) 0)
                 (= a!187 0)
                 a!188
                 a!189))
      (a!225 (or (= (ite (= M9 a!216) (+ (- 1) a!217) a!217) 0)
                 (= a!218 0)
                 (= (ite (= I9 a!216) (+ (- 1) a!218) a!218) 0)
                 (= a!219 0)
                 (= (ite (= E9 a!216) (+ (- 1) a!219) a!219) 0)
                 (= a!220 0)
                 (= (ite (= A9 a!216) (+ (- 1) a!220) a!220) 0)
                 (= a!221 0)
                 (= (ite (= W8 a!216) (+ (- 1) a!221) a!221) 0)
                 (= a!222 0)
                 a!223
                 a!224))
      (a!260 (or (= (ite (= O10 a!251) (+ (- 1) a!252) a!252) 0)
                 (= a!253 0)
                 (= (ite (= K10 a!251) (+ (- 1) a!253) a!253) 0)
                 (= a!254 0)
                 (= (ite (= G10 a!251) (+ (- 1) a!254) a!254) 0)
                 (= a!255 0)
                 (= (ite (= C10 a!251) (+ (- 1) a!255) a!255) 0)
                 (= a!256 0)
                 (= (ite (= Y9 a!251) (+ (- 1) a!256) a!256) 0)
                 (= a!257 0)
                 a!258
                 a!259)))
(let ((a!261 (and (or (not U10) (= H12 (ite a!120 a!111 0.0)))
                  (or (not W10) (= J12 (ite a!155 a!146 0.0)))
                  (or (not Y10) (= L12 (ite a!190 a!181 0.0)))
                  (or (not A11) (= N12 (ite a!225 a!216 0.0)))
                  (or (not C11) (= P12 (ite a!260 a!251 0.0)))
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
                  (= V8 U8)
                  (= X8 W8)
                  (= Z8 Y8)
                  (= B9 A9)
                  (= D9 C9)
                  (= F9 E9)
                  (= H9 G9)
                  (= J9 I9)
                  (= L9 K9)
                  (= N9 M9)
                  (= P9 O9)
                  (= R9 Q9)
                  (= T9 S9)
                  (= V9 U9)
                  (= X9 W9)
                  (= Z9 Y9)
                  (= B10 A10)
                  (= D10 C10)
                  (= F10 E10)
                  (= H10 G10)
                  (= J10 I10)
                  (= L10 K10)
                  (= N10 M10)
                  (= P10 O10)
                  (= R10 Q10)
                  (= T10 S10)
                  (= Q12 2.0)
                  (= R12 3.0)
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
                  (= V11 U11)
                  (= X11 W11)
                  (= Z11 Y11)
                  (= B12 A12)
                  (= D12 C12)
                  (= F12 E12)
                  (= V10 U10)
                  (= X10 W10)
                  (= Z10 Y10)
                  (= B11 A11)
                  (= D11 C11)
                  (= F11 E11)
                  (= H11 G11)
                  (= J11 I11)
                  (= L11 K11)
                  (= N11 M11)
                  (= P11 O11)
                  (= R11 Q11)
                  (= T11 S11))))
  (and (= T12 S12)
       (or (and a!2
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
                a!38
                a!39
                a!40
                a!41
                a!42
                a!44
                a!45
                a!46
                a!47
                a!48
                a!50
                a!51
                a!52
                a!53
                a!54
                a!56
                a!57
                a!58
                a!59
                a!60
                a!62
                a!63
                a!64
                a!65
                a!66
                a!68
                a!69
                a!70
                a!71
                a!72
                a!74
                a!75
                a!76
                a!77
                a!78
                a!80
                a!81
                a!82
                a!83
                a!84
                (= P12 O12)
                (= Q12 1.0)
                (= R12 2.0)
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
                (= Z4 Y4)
                (= B5 A5)
                (= D5 C5)
                (= F5 E5)
                (= H5 G5)
                (= J5 I5)
                (= H12 G12)
                (= J12 I12)
                (= L12 K12)
                (= N12 M12)
                (= V11 U11)
                (= X11 W11)
                (= Z11 Y11)
                (= B12 A12)
                (= D12 C12)
                (= F12 E12)
                (= V10 U10)
                (= X10 W10)
                (= Z10 Y10)
                (= B11 A11)
                (= D11 C11)
                (= F11 E11)
                (= H11 G11)
                (= J11 I11)
                (= L11 K11)
                (= N11 M11)
                (= P11 O11)
                (= R11 Q11)
                (= T11 S11))
           (and (= L6 K6)
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
                (= V8 U8)
                (= X8 W8)
                (= Z8 Y8)
                (= B9 A9)
                (= D9 C9)
                (= F9 E9)
                (= H9 G9)
                (= J9 I9)
                (= L9 K9)
                (= N9 M9)
                (= P9 O9)
                (= R9 Q9)
                (= T9 S9)
                (= V9 U9)
                (= X9 W9)
                (= Z9 Y9)
                (= B10 A10)
                (= D10 C10)
                (= F10 E10)
                (= H10 G10)
                (= J10 I10)
                (= L10 K10)
                (= N10 M10)
                (= P10 O10)
                (= R10 Q10)
                (= T10 S10)
                (= P12 O12)
                (= Q12 3.0)
                (= R12 Q12)
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
                (= H12 G12)
                (= J12 I12)
                (= L12 K12)
                (= N12 M12)
                (= V11 U11)
                (= X11 W11)
                (= Z11 Y11)
                (= B12 A12)
                (= D12 C12)
                (= F12 E12)
                (= V10 U10)
                (= X10 W10)
                (= Z10 Y10)
                (= B11 A11)
                (= D11 C11)
                (= F11 E11)
                (= H11 G11)
                (= J11 I11)
                (= L11 K11)
                (= N11 M11)
                (= P11 O11)
                (= R11 Q11)
                (= T11 S11))
           a!85
           a!261)
       (= V12 U12))))))))))))))))))))))))))))
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
           V9
           X9
           Z9
           B10
           D10
           F10
           H10
           J10
           L10
           N10
           P10
           R10
           T10
           V10
           X10
           Z10
           B11
           D11
           F11
           H11
           J11
           L11
           N11
           P11
           R11
           T11
           V11
           X11
           Z11
           B12
           D12
           F12
           H12
           J12
           L12
           N12
           P12
           R12
           T12
           V12)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Real) (R4 Real) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) (Y4 Real) (Z4 Real) (A5 Real) (B5 Real) (C5 Real) (D5 Real) (E5 Real) (F5 Real) (G5 Real) (H5 Real) (I5 Real) (J5 Real) (K5 Bool) (L5 Bool) (M5 Bool) (N5 Bool) (O5 Bool) (P5 Bool) (Q5 Bool) (R5 Bool) (S5 Bool) (T5 Bool) (U5 Bool) (V5 Bool) (W5 Bool) (X5 Bool) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Real) (E6 Real) (F6 Real) (G6 Real) (H6 Real) (I6 Real) (J6 Real) (K6 Real) ) 
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
           X4
           Y4
           Z4
           A5
           B5
           C5
           D5
           E5
           F5
           G5
           H5
           I5
           J5
           K5
           L5
           M5
           N5
           O5
           P5
           Q5
           R5
           S5
           T5
           U5
           V5
           W5
           X5
           Y5
           Z5
           A6
           B6
           C6
           D6
           E6
           F6
           G6
           H6
           I6
           J6
           K6)
        (let ((a!1 (or (and L5 (not (= D6 E6)))
               (and M5 (not (= D6 F6)))
               (and N5 (not (= D6 G6)))
               (and O5 (not (= D6 H6)))))
      (a!2 (or (and K5 (not (= E6 D6)))
               (and M5 (not (= E6 F6)))
               (and N5 (not (= E6 G6)))
               (and O5 (not (= E6 H6)))))
      (a!3 (or (and K5 (not (= F6 D6)))
               (and L5 (not (= F6 E6)))
               (and N5 (not (= F6 G6)))
               (and O5 (not (= F6 H6)))))
      (a!4 (or (and K5 (not (= G6 D6)))
               (and L5 (not (= G6 E6)))
               (and M5 (not (= G6 F6)))
               (and O5 (not (= G6 H6)))))
      (a!5 (or (and K5 (not (= H6 D6)))
               (and L5 (not (= H6 E6)))
               (and M5 (not (= H6 F6)))
               (and N5 (not (= H6 G6))))))
  (and (or (and K5 a!1) (and L5 a!2) (and M5 a!3) (and N5 a!4) (and O5 a!5))
       (<= 3.0 I6)))
      )
      false
    )
  )
)

(check-sat)
(exit)
