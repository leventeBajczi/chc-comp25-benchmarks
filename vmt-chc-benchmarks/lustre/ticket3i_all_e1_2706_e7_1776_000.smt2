(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Int Int Int Int Int Bool Bool Bool Int Bool Bool Bool Int Bool Bool Bool Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Int) (K Bool) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Bool) (U Int) (V Bool) (W Bool) (X Int) (Y Bool) (Z Int) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Int) (F1 Bool) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Bool) (E2 Int) (F2 Int) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Bool) (L2 Bool) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Bool) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Bool) (Z2 Int) (A3 Bool) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Bool) (K3 Int) (L3 Int) ) 
    (=>
      (and
        (let ((a!1 (or (not G2)
               (and (not Y1)
                    (<= I2 3)
                    (<= X1 3)
                    (<= W1 3)
                    (<= (+ X1 W1 I2) 8)
                    (<= 0 I2)
                    (<= 0 X1)
                    (<= 0 W1))))
      (a!2 (or A3 (and (not (<= 3 E2)) (not (<= 3 C2)) (not (<= 3 B2)))))
      (a!3 (= (or (and (not J3)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not C))
                  (and (not J3)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       C)
                  (and (not J3)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       Y2
                       (not C))
                  (and (not J3)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       R2
                       (not Y2)
                       (not C))
                  (and (not J3)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       D2
                       (not R2)
                       (not Y2)
                       (not C))
                  (and (not J3)
                       (not H)
                       (not K)
                       (not N)
                       Q
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not C))
                  (and (not J3)
                       (not H)
                       (not K)
                       N
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not C))
                  (and (not J3)
                       (not H)
                       K
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not C))
                  (and (not J3)
                       H
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not C))
                  (and J3
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not C)))
              T1)))
  (and (= a!1 V1)
       (= L2 G2)
       (= K2 Y1)
       (= U1 (and T1 (<= 0 R1) (<= 0 P1) (<= 0 N1) (<= 0 J1)))
       (= U1 L2)
       (= A3 K2)
       (= J2 H2)
       (= B2 I2)
       (= G3 F3)
       (= E3 D3)
       (= C3 B3)
       (= G1 0)
       (= G1 B2)
       (= H1 0)
       (= H1 C2)
       (= I1 0)
       (= I1 E2)
       (= K1 J1)
       (= K1 L1)
       (= L1 F2)
       (= M1 J2)
       (= M1 L1)
       (= O1 G3)
       (= O1 N1)
       (= Q1 E3)
       (= Q1 P1)
       (= S1 C3)
       (= S1 R1)
       (= C2 W1)
       (= E2 X1)
       (or (not A3) (<= 3 E2) (<= 3 C2) (<= 3 B2))
       (or (not V) (= I 0))
       (or (not C) (= B A))
       (or (not C) (= E D))
       (or (= W2 P) Y2)
       (or (not Y2) (= W2 Z))
       (or (not R2) (= N2 U))
       (or (= N2 J) R2)
       (or (= A2 E) D2)
       (or (not D2) (= A2 E1))
       (or (not F1) (= D 0))
       (or (not D1) (= E1 2))
       (or (not B1) (= C1 1))
       (or (not A1) (= O 0))
       (or (not Q) (= P O))
       (or (not Q) (= T2 Z2))
       (or Q (= T2 B))
       (or (= W2 V2) N)
       (or (not N) (= M L))
       (or (= Q2 L3) N)
       (or (not N) (= Q2 X2))
       (or (not N) (= V2 X))
       (or (= T2 S2) K)
       (or (not K) (= S2 U2))
       (or (not K) (= J I))
       (or (not H) (= G F))
       (or (not H) (= M2 S))
       (or (= N2 M2) H)
       (or (not H) (= P2 O2))
       (or (= Q2 P2) H)
       (or J3 (= A2 Z1))
       (or (not J3) (= Z1 C1))
       (or (not J3) (= L3 K3))
       (or (not J3) (= I3 H3))
       (or (not R) (= S 1))
       (or (not T) (= U 2))
       (or (not W) (= X 1))
       (or (not Y) (= Z 2))
       a!2
       a!3))
      )
      (state U1
       L2
       R2
       H
       K
       N
       Y2
       Q
       J3
       D2
       C
       T1
       A3
       K2
       S1
       C3
       Q1
       E3
       O1
       G3
       M1
       J2
       K1
       L1
       I1
       E2
       H1
       C2
       G1
       B2
       T2
       Z2
       B
       W2
       Z
       P
       Q2
       L3
       X2
       V2
       X
       S2
       U2
       N2
       U
       J
       P2
       O2
       M2
       S
       G2
       Y1
       B3
       D3
       F3
       H2
       F2
       X1
       A2
       E1
       E
       W1
       I2
       Z1
       C1
       V1
       J1
       R1
       P1
       N1
       D
       F1
       D1
       B1
       O
       A1
       Y
       W
       I
       V
       T
       R
       M
       L
       G
       F
       A
       K3
       I3
       H3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Int) (K Bool) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Bool) (U Int) (V Bool) (W Bool) (X Int) (Y Bool) (Z Int) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Int) (F1 Bool) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Bool) (E2 Int) (F2 Int) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Bool) (L2 Bool) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Bool) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Bool) (Z2 Int) (A3 Bool) (B3 Int) (C3 Bool) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Bool) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Bool) (N3 Int) (O3 Int) (P3 Bool) (Q3 Int) (R3 Int) (S3 Bool) (T3 Int) (U3 Int) (V3 Bool) (W3 Int) (X3 Int) (Y3 Bool) (Z3 Int) (A4 Bool) (B4 Bool) (C4 Int) (D4 Bool) (E4 Int) (F4 Bool) (G4 Bool) (H4 Int) (I4 Bool) (J4 Int) (K4 Bool) (L4 Bool) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Int) (B5 Int) (C5 Int) (D5 Int) (E5 Int) (F5 Int) (G5 Int) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Bool) (M5 Bool) (N5 Bool) (O5 Int) (P5 Int) (Q5 Int) (R5 Bool) (S5 Int) (T5 Int) (U5 Int) (V5 Bool) (W5 Int) (X5 Int) (Y5 Int) (Z5 Int) (A6 Int) (B6 Int) (C6 Int) (D6 Int) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Bool) (J6 Int) (K6 Int) (L6 Bool) (M6 Bool) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Bool) (W6 Int) (X6 Int) ) 
    (=>
      (and
        (state U1
       L2
       R2
       H
       K
       N
       Y2
       Q
       V6
       D2
       C
       T1
       A3
       K2
       S1
       O6
       Q1
       Q6
       O1
       S6
       M1
       J2
       K1
       L1
       I1
       E2
       H1
       C2
       G1
       B2
       T2
       Z2
       B
       W2
       Z
       P
       Q2
       X6
       X2
       V2
       X
       S2
       U2
       N2
       U
       J
       P2
       O2
       M2
       S
       G2
       Y1
       N6
       P6
       R6
       H2
       F2
       X1
       A2
       E1
       E
       W1
       I2
       Z1
       C1
       V1
       J1
       R1
       P1
       N1
       D
       F1
       D1
       B1
       O
       A1
       Y
       W
       I
       V
       T
       R
       M
       L
       G
       F
       A
       W6
       U6
       T6)
        (let ((a!1 (= (or (and (not L6)
                       (not I6)
                       (not V5)
                       (not V3)
                       (not S3)
                       (not P3)
                       (not M3)
                       (not H3)
                       (not C3))
                  (and (not L6)
                       (not I6)
                       (not V5)
                       (not V3)
                       (not S3)
                       (not P3)
                       (not M3)
                       (not H3)
                       C3)
                  (and (not L6)
                       (not I6)
                       (not V5)
                       (not V3)
                       (not S3)
                       (not P3)
                       (not M3)
                       H3
                       (not C3))
                  (and (not L6)
                       (not I6)
                       (not V5)
                       (not V3)
                       (not S3)
                       (not P3)
                       M3
                       (not H3)
                       (not C3))
                  (and (not L6)
                       (not I6)
                       (not V5)
                       (not V3)
                       (not S3)
                       P3
                       (not M3)
                       (not H3)
                       (not C3))
                  (and (not L6)
                       (not I6)
                       (not V5)
                       (not V3)
                       S3
                       (not P3)
                       (not M3)
                       (not H3)
                       (not C3))
                  (and (not L6)
                       (not I6)
                       (not V5)
                       V3
                       (not S3)
                       (not P3)
                       (not M3)
                       (not H3)
                       (not C3))
                  (and (not L6)
                       (not I6)
                       V5
                       (not V3)
                       (not S3)
                       (not P3)
                       (not M3)
                       (not H3)
                       (not C3))
                  (and (not L6)
                       I6
                       (not V5)
                       (not V3)
                       (not S3)
                       (not P3)
                       (not M3)
                       (not H3)
                       (not C3))
                  (and L6
                       (not I6)
                       (not V5)
                       (not V3)
                       (not S3)
                       (not P3)
                       (not M3)
                       (not H3)
                       (not C3)))
              H5))
      (a!2 (= (or (and (not C)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not V6))
                  (and (not C)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       V6)
                  (and (not C)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       Y2
                       (not V6))
                  (and (not C)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       R2
                       (not Y2)
                       (not V6))
                  (and (not C)
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       D2
                       (not R2)
                       (not Y2)
                       (not V6))
                  (and (not C)
                       (not H)
                       (not K)
                       (not N)
                       Q
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not V6))
                  (and (not C)
                       (not H)
                       (not K)
                       N
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not V6))
                  (and (not C)
                       (not H)
                       K
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not V6))
                  (and (not C)
                       H
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not V6))
                  (and C
                       (not H)
                       (not K)
                       (not N)
                       (not Q)
                       (not D2)
                       (not R2)
                       (not Y2)
                       (not V6)))
              T1))
      (a!3 (or (not N5)
               (and (not R5)
                    (<= Q5 3)
                    (<= P5 3)
                    (<= O5 3)
                    (<= (+ Q5 P5 O5) 8)
                    (<= 0 Q5)
                    (<= 0 P5)
                    (<= 0 O5))))
      (a!4 (or (not G2)
               (and (not Y1)
                    (<= W1 3)
                    (<= X1 3)
                    (<= I2 3)
                    (<= (+ X1 W1 I2) 8)
                    (<= 0 W1)
                    (<= 0 X1)
                    (<= 0 I2))))
      (a!5 (= L5 (or L2 (and H5 (<= 0 K5) (<= 0 J5) (<= 0 I5) (<= 0 G5)))))
      (a!6 (or (not A4) (= (+ L1 (* (- 1) M4)) (- 1))))
      (a!7 (or (not B4) (= (+ J2 (* (- 1) O4)) (- 1))))
      (a!8 (or (not F4) (= (+ L1 (* (- 1) N4)) (- 1))))
      (a!9 (or (not G4) (= (+ J2 (* (- 1) P4)) (- 1))))
      (a!10 (or (not K4) (= (+ L1 (* (- 1) I3)) (- 1))))
      (a!11 (or (not L4) (= (+ J2 (* (- 1) E3)) (- 1))))
      (a!12 (or M6 (and (not (<= 3 W5)) (not (<= 3 U5)) (not (<= 3 T5)))))
      (a!13 (or A3 (and (not (<= 3 B2)) (not (<= 3 C2)) (not (<= 3 E2))))))
  (and (= (= C2 2) G4)
       (= (= B2 2) B4)
       a!1
       a!2
       (= a!3 M5)
       (= a!4 V1)
       (= Y3 (and (<= Q4 J2) (= B2 1)))
       (= A4 (= B2 0))
       (= D4 (and (<= R4 J2) (= C2 1)))
       (= F4 (= C2 0))
       (= I4 (and (<= S4 J2) (= E2 1)))
       (= K4 (= E2 0))
       a!5
       (= E6 R5)
       (= E6 M6)
       (= F6 L5)
       (= F6 N5)
       (= A3 K2)
       (= L2 G2)
       (= K2 Y1)
       (= U1 L2)
       (= S6 R6)
       (= Q6 P6)
       (= O6 N6)
       (= Q4 D5)
       (= Q4 B6)
       (= R4 E5)
       (= R4 C6)
       (= S4 F5)
       (= S4 D6)
       (= U4 T4)
       (= W4 V4)
       (= Y4 X4)
       (= A5 Z4)
       (= C5 B5)
       (= D5 L3)
       (= E5 R3)
       (= F5 K3)
       (= T5 U4)
       (= T5 O5)
       (= U5 W4)
       (= U5 P5)
       (= W5 Y4)
       (= W5 Q5)
       (= Y5 A5)
       (= Y5 X5)
       (= A6 C5)
       (= A6 Z5)
       (= J2 H2)
       (= E2 X1)
       (= C2 W1)
       (= B2 I2)
       (= S1 O6)
       (= Q1 Q6)
       (= O1 S6)
       (= M1 J2)
       (= L1 F2)
       (= K1 L1)
       (= I1 E2)
       (= H1 C2)
       (= G1 B2)
       (or (not M6) (<= 3 W5) (<= 3 U5) (<= 3 T5))
       (or (not A3) (<= 3 B2) (<= 3 C2) (<= 3 E2))
       (or V6 (= A2 Z1))
       (or (not V6) (= Z1 C1))
       (or (not C3) (= B3 D3))
       (or (not C3) (= F3 E3))
       (or C3 (= J2 F3))
       (or C3 (= E2 B3))
       (or H3 (= O6 K3))
       (or (not H3) (= G3 I3))
       (or (not H3) (= K3 J3))
       (or (not H3) (= J4 X4))
       (or H3 (= S5 X4))
       (or H3 (= L1 G3))
       (or M3 (= S6 L3))
       (or (not M3) (= L3 N3))
       (or (not M3) (= Z3 T4))
       (or (not M3) (= Z4 M4))
       (or M3 (= G6 T4))
       (or M3 (= H6 Z4))
       (or (not P3) (= O3 Q3))
       (or (not P3) (= O4 B5))
       (or P3 (= J6 B5))
       (or P3 (= B2 O3))
       (or S3 (= Q6 R3))
       (or S3 (= G3 H6))
       (or (not S3) (= R3 T3))
       (or (not S3) (= E4 V4))
       (or (not S3) (= H6 N4))
       (or S3 (= K6 V4))
       (or (not V3) (= U3 W3))
       (or (not V3) (= P4 J6))
       (or V3 (= J6 F3))
       (or V3 (= C2 U3))
       (or (not Y3) (= X3 2))
       (or Y3 (= B2 X3))
       a!6
       (or A4 (= S6 N3))
       (or (not A4) (= Z3 1))
       (or A4 (= B2 Z3))
       (or (not A4) (= L1 N3))
       (or A4 (= L1 M4))
       a!7
       (or (not B4) (= Q3 0))
       (or B4 (= J2 O4))
       (or B4 (= B2 Q3))
       (or (not D4) (= C4 2))
       (or D4 (= C2 C4))
       a!8
       (or F4 (= Q6 T3))
       (or (not F4) (= E4 1))
       (or F4 (= C2 E4))
       (or (not F4) (= L1 T3))
       (or F4 (= L1 N4))
       a!9
       (or (not G4) (= W3 0))
       (or G4 (= J2 P4))
       (or G4 (= C2 W3))
       (or (not I4) (= H4 2))
       (or I4 (= E2 H4))
       a!10
       (or K4 (= O6 J3))
       (or (not K4) (= J4 1))
       (or K4 (= E2 J4))
       (or K4 (= L1 I3))
       (or (not K4) (= L1 J3))
       a!11
       (or (not L4) (= D3 0))
       (or L4 (= J2 E3))
       (or L4 (= E2 D3))
       (or (not V5) (= H4 S5))
       (or V5 (= S5 B3))
       (or (not I6) (= X3 G6))
       (or I6 (= G6 O3))
       (or (not L6) (= C4 K6))
       (or L6 (= K6 U3))
       a!12
       a!13
       (or (not Y2) (= W2 Z))
       (or Y2 (= W2 P))
       (or (not R2) (= N2 U))
       (or R2 (= N2 J))
       (or (not D2) (= A2 E1))
       (or D2 (= A2 E))
       (or (not Q) (= T2 Z2))
       (or Q (= T2 B))
       (or N (= W2 V2))
       (or (not N) (= V2 X))
       (or N (= Q2 X6))
       (or (not N) (= Q2 X2))
       (or K (= T2 S2))
       (or (not K) (= S2 U2))
       (or H (= Q2 P2))
       (or (not H) (= P2 O2))
       (or H (= N2 M2))
       (or (not H) (= M2 S))
       (= (= E2 2) L4)))
      )
      (state L5
       F6
       I6
       M3
       P3
       S3
       L6
       V3
       H3
       V5
       C3
       H5
       M6
       E6
       F5
       S4
       E5
       R4
       D5
       Q4
       C5
       A6
       A5
       Y5
       Y4
       W5
       W4
       U5
       U4
       T5
       J6
       P4
       F3
       K6
       C4
       U3
       H6
       G3
       N4
       V4
       E4
       B5
       O4
       G6
       X3
       O3
       Z4
       M4
       T4
       Z3
       N5
       R5
       D6
       C6
       B6
       Z5
       X5
       Q5
       S5
       H4
       B3
       P5
       O5
       X4
       J4
       M5
       K5
       J5
       I5
       G5
       D3
       L4
       I4
       K4
       W3
       G4
       D4
       F4
       Q3
       B4
       Y3
       A4
       R3
       T3
       L3
       N3
       E3
       I3
       K3
       J3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Int) (K Bool) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Bool) (U Int) (V Bool) (W Bool) (X Int) (Y Bool) (Z Int) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Int) (F1 Bool) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Bool) (E2 Int) (F2 Int) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Bool) (L2 Bool) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Bool) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Bool) (Z2 Int) (A3 Bool) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Bool) (K3 Int) (L3 Int) ) 
    (=>
      (and
        (state U1
       L2
       R2
       H
       K
       N
       Y2
       Q
       J3
       D2
       C
       T1
       A3
       K2
       S1
       C3
       Q1
       E3
       O1
       G3
       M1
       J2
       K1
       L1
       I1
       E2
       H1
       C2
       G1
       B2
       T2
       Z2
       B
       W2
       Z
       P
       Q2
       L3
       X2
       V2
       X
       S2
       U2
       N2
       U
       J
       P2
       O2
       M2
       S
       G2
       Y1
       B3
       D3
       F3
       H2
       F2
       X1
       A2
       E1
       E
       W1
       I2
       Z1
       C1
       V1
       J1
       R1
       P1
       N1
       D
       F1
       D1
       B1
       O
       A1
       Y
       W
       I
       V
       T
       R
       M
       L
       G
       F
       A
       K3
       I3
       H3)
        (not V1)
      )
      false
    )
  )
)

(check-sat)
(exit)
