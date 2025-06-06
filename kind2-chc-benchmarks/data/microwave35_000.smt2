(set-logic HORN)


(declare-fun |ERR| ( ) Bool)
(declare-fun |top_reset| ( Int Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Bool Bool Bool Int Bool Int Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Bool Bool Bool Int Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |top_step| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Bool Bool Bool Int Bool Int Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Bool Bool Bool Int Bool ) Bool)
(declare-fun |MAIN| ( Int Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Bool Bool Bool Int Bool Bool ) Bool)

(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Int) (P1 Bool) (Q1 Int) (R1 Bool) (S1 Bool) (T1 Int) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Int) (F3 Bool) ) 
    (=>
      (and
        (and (= S1 C)
     (= U1 E)
     (= V1 F)
     (= W1 G)
     (= X1 H)
     (= Y1 I)
     (= Z1 J)
     (= A2 K)
     (= B2 L)
     (= C2 M)
     (= D2 N)
     (= E2 O)
     (= F2 P)
     (= G2 Q)
     (= L2 V)
     (= M2 W)
     (= N2 X)
     (= R2 B1)
     (= S2 C1)
     (= T2 D1)
     (= U2 E1)
     (= A3 K1)
     (= B3 L1)
     (= C3 M1)
     (= D3 N1)
     (= Q1 A)
     (= T1 D)
     (= H2 R)
     (= I2 S)
     (= J2 T)
     (= K2 U)
     (= O2 Y)
     (= P2 Z)
     (= Q2 A1)
     (= V2 F1)
     (= W2 G1)
     (= X2 H1)
     (= Y2 I1)
     (= Z2 J1)
     (= E3 O1)
     (= F3 true)
     (= R1 B))
      )
      (top_reset A
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
           F3)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Bool) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Int) (F1 Bool) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Bool) (P1 Int) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Int) (V1 Bool) (W1 Bool) (X1 Int) (Y1 Int) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Int) (D2 Bool) (E2 Int) (F2 Bool) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Bool) (P2 Int) (Q2 Bool) (R2 Int) (S2 Bool) (T2 Bool) (U2 Int) (V2 Int) (W2 Int) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Int) (D3 Bool) (E3 Bool) (F3 Int) (G3 Bool) (H3 Int) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Bool) (P3 Int) (Q3 Int) (R3 Bool) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Bool) (Z3 Bool) (A4 Int) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Bool) (N4 Bool) (O4 Bool) (P4 Int) (Q4 Bool) (R4 Bool) (S4 Int) (T4 Bool) (U4 Bool) (V4 Bool) (W4 Bool) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Int) (H5 Int) (I5 Int) (J5 Int) (K5 Bool) (L5 Bool) (M5 Bool) (N5 Int) (O5 Int) (P5 Int) (Q5 Bool) (R5 Bool) (S5 Bool) (T5 Bool) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Int) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Int) (E6 Bool) (F6 Int) (G6 Bool) (H6 Bool) (I6 Int) (J6 Bool) (K6 Bool) (L6 Bool) (M6 Bool) (N6 Bool) (O6 Bool) (P6 Bool) (Q6 Bool) (R6 Bool) (S6 Bool) (T6 Bool) (U6 Bool) (V6 Bool) (W6 Int) (X6 Int) (Y6 Int) (Z6 Int) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Int) (E7 Int) (F7 Int) (G7 Bool) (H7 Bool) (I7 Bool) (J7 Bool) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Bool) (Q7 Bool) (R7 Bool) (S7 Bool) (T7 Int) (U7 Bool) ) 
    (=>
      (and
        (let ((a!1 (and (or (not (<= Z 3)) (not (>= Z 1))) (<= V 3) (>= V 1)))
      (a!2 (= T2 (and (not B2) (not (<= U2 0)) (= P1 2))))
      (a!3 (= E3 (and (not T2) (not B2) (or (not A2) Z1) (= C2 2))))
      (a!4 (div (+ Q3 (* (- 60) (div Q3 60))) 10))
      (a!6 (or (and (or (not O) (= C 9)) (or O (= C 10))) N))
      (a!15 (or (not B1) (and (or A1 (= X V)) (or (not A1) (= X 2)))))
      (a!16 (or (not B1) (and (or (= E1 J2) A1) (or (not A1) (= E1 2)))))
      (a!17 (or (not D1) (and (or C1 (= Y X)) (or (not C1) (= Y 3)))))
      (a!18 (and (or (and (<= H3 3) (>= H3 1)) (= G1 H3))
                 (or (not (<= H3 3)) (not (>= H3 1)) (= G1 0))))
      (a!19 (or (not R1) (and (or Q1 (= I1 G1)) (or (not Q1) (= I1 4)))))
      (a!20 (or (not R1) (and (or (= U1 I2) Q1) (or (not Q1) (= U1 1)))))
      (a!21 (and (or (= J1 I1) (= I1 3)) (or (not (= I1 3)) (= J1 1))))
      (a!22 (or (not T1) (and (or S1 (= M1 J1)) (or (not S1) (= M1 2)))))
      (a!23 (or (not T1) (and (or (= X1 U1) S1) (or (not S1) (= X1 2)))))
      (a!24 (or (not W1)
                (and (or V1 (= P1 N1)) (or (not V1) (= P1 4)) (= U2 0))))
      (a!25 (and (or (and (<= M1 3) (>= M1 1)) (= N1 M1))
                 (or (not (<= M1 3)) (not (>= M1 1)) (= N1 0))))
      (a!26 (or (not W1) (and (or (= E2 X1) V1) (or (not V1) (= E2 1)))))
      (a!27 (and (or (= I3 4) (= Z I3)) (or (not (= I3 4)) (= Z 0))))
      (a!28 (or (not D1) (and (or (= I2 E1) C1) (or (not C1) (= I2 3)))))
      (a!30 (and (or (= Y1 P1) (= P1 2)) (or (not (= P1 2)) (= Y1 1))))
      (a!31 (or (not T2) (and (or D2 (= C2 Y1)) (or (not D2) (= C2 2)))))
      (a!32 (or (not T2) (and (or (= H2 E2) D2) (or (not D2) (= H2 2)))))
      (a!33 (and (or (= F3 C2) (= C2 2)) (or (not (= C2 2)) (= F3 1))))
      (a!34 (or (not O3) (and (or (= A4 J2) G2) (or (not G2) (= A4 1)))))
      (a!35 (or (not E3) (and (or D3 (= A4 H2)) (or (not D3) (= A4 3)))))
      (a!38 (and (or (= Q3 U2) T2) (or (not T2) (= Q3 (+ (- 1) U2)))))
      (a!40 (or (not E3) (and (or (= P3 F3) D3) (or (not D3) (= P3 3)))))
      (a!43 (or (= K1 (and (not C6) C4)) R3))
      (a!44 (= O4
               (or M5
                   (not I4)
                   (and (not T4) D4)
                   (and (not Z4) E4)
                   (and (not F5) F4)
                   (and (not K5) G4)
                   (and (not L5) H4)
                   C4
                   (= S3 5)
                   (not Z3))))
      (a!45 (= B3
               (or S5
                   (not J4)
                   (and (not T4) D4)
                   (and (not Z4) E4)
                   (and (not F5) F4)
                   (and (not K5) G4)
                   (and (not L5) H4)
                   (and (not M5) I4)
                   C4
                   (= S3 6)
                   (not Z3))))
      (a!46 (= A3
               (or A6
                   (not K4)
                   (and (not T4) D4)
                   (and (not Z4) E4)
                   (and (not F5) F4)
                   (and (not K5) G4)
                   (and (not L5) H4)
                   (and (not M5) I4)
                   (and (not S5) J4)
                   C4
                   (= S3 7)
                   (not Z3))))
      (a!47 (= Z2
               (or B6
                   (not L4)
                   (and (not T4) D4)
                   (and (not Z4) E4)
                   (and (not F5) F4)
                   (and (not K5) G4)
                   (and (not L5) H4)
                   (and (not M5) I4)
                   (and (not S5) J4)
                   (and (not A6) K4)
                   C4
                   (= S3 8)
                   (not Z3))))
      (a!48 (= Y2
               (or Z5
                   (not M4)
                   (and (not T4) D4)
                   (and (not Z4) E4)
                   (and (not F5) F4)
                   (and (not K5) G4)
                   (and (not L5) H4)
                   (and (not M5) I4)
                   (and (not S5) J4)
                   (and (not A6) K4)
                   (and (not B6) L4)
                   C4
                   (= S3 9)
                   (not Z3))))
      (a!49 (= X2
               (or (and (not T4) D4)
                   (and (not Z4) E4)
                   (and (not F5) F4)
                   (and (not K5) G4)
                   (and (not L5) H4)
                   (and (not M5) I4)
                   (and (not S5) J4)
                   (and (not A6) K4)
                   (and (not B6) L4)
                   (and (not Z5) M4)
                   C4
                   (= S3 Y5)
                   (not Z3))))
      (a!50 (or (and (or (not M4) (= W3 9)) (or M4 (= W3 10))) L4))
      (a!62 (and (= W3 G5) (= V3 H5) (= U3 I5)))
      (a!63 (or (and (or (not O) (= W3 9)) (or (= W3 10) O)) N))
      (a!76 (= X3 (+ W3 (* 10 V3) (* 60 U3))))
      (a!80 (and (or (<= L2 0) (= N3 L2)) (or (not (<= L2 0)) (= N3 0))))
      (a!82 (and (or (<= N2 0) (= L3 N2)) (or (not (<= N2 0)) (= L3 0))))
      (a!84 (and (or (<= M2 0) (= M3 M2)) (or (not (<= M2 0)) (= M3 0))))
      (a!86 (and (or (<= P2 0) (= K3 P2)) (or (not (<= P2 0)) (= K3 0))))
      (a!88 (and (or (<= K2 0) (= T3 K2)) (or (not (<= K2 0)) (= T3 0))))
      (a!90 (and (or (<= R2 0) (= J3 R2)) (or (not (<= R2 0)) (= J3 0))))
      (a!92 (or (not Z3) (and (or (not Q4) (not Y3)) (or Q4 (= Y3 R4)))))
      (a!93 (or (and (or (not Q5) (not O3)) (or Q5 (= O3 R5))) R3))
      (a!94 (or (and (or (not M4) (= D 9)) (or M4 (= D 10))) L4)))
(let ((a!5 (= S3 (+ Q3 (* (- 60) (div Q3 60)) (* (- 10) a!4))))
      (a!7 (or (and a!6 (or (not N) (= C 8))) M))
      (a!29 (or (not F2) (and a!28 (or (= I2 E1) D1))))
      (a!36 (or (not G3) (and a!35 (or E3 (= A4 H2)))))
      (a!39 (or (and (or (not G3) a!38) (or G3 (= Q3 V2))) O3))
      (a!41 (or (not G3) (and a!40 (or (= P3 F3) E3))))
      (a!51 (or (and a!50 (or (not L4) (= W3 8))) K4))
      (a!64 (or (and a!63 (or (not N) (= W3 8))) M))
      (a!77 (and (or (and (not Z3) Y3) a!76) (or (not Y3) Z3 (= X3 0))))
      (a!78 (or (and (not Z3) Y3) (and (or Z3 (= X3 S4)) (or (not Z3) a!76))))
      (a!81 (or (and (or a!80 O2) (or (not O2) (= N3 639))) R3))
      (a!83 (or (and (or (not O2) a!82) (or (= L3 639) O2)) R3))
      (a!85 (or (and (or (not Q2) a!84) (or Q2 (= M3 639))) R3))
      (a!87 (or (and (or a!86 Q2) (or (not Q2) (= K3 639))) R3))
      (a!89 (or (and (or (not S2) a!88) (or S2 (= T3 639))) R3))
      (a!91 (or (and (or a!90 S2) (or (not S2) (= J3 639))) R3))
      (a!95 (or (and a!94 (or (not L4) (= D 8))) K4)))
(let ((a!8 (or (and a!7 (or (not M) (= C 7))) L))
      (a!37 (or (and a!36 (or G3 (= A4 I2))) O3))
      (a!42 (or (and a!41 (or (= P3 H3) G3)) O3))
      (a!52 (or (and a!51 (or (not K4) (= W3 7))) J4))
      (a!65 (or (and a!64 (or (not M) (= W3 7))) L))
      (a!79 (or (and a!78 (or (not Y3) Z3 (= X3 0))) R3))
      (a!96 (or (and a!95 (or (not K4) (= D 7))) J4)))
(let ((a!9 (or (and a!8 (or (not L) (= C 6))) K))
      (a!53 (or (and a!52 (or (not J4) (= W3 6))) I4))
      (a!66 (or (and a!65 (or (not L) (= W3 6))) K))
      (a!97 (or (and a!96 (or (not J4) (= D 6))) I4)))
(let ((a!10 (or (and a!9 (or (not K) (= C 5))) J))
      (a!54 (or (and a!53 (or (not I4) (= W3 5))) H4))
      (a!67 (or (and a!66 (or (not K) (= W3 5))) J))
      (a!98 (or (and a!97 (or (not I4) (= D 5))) H4)))
(let ((a!11 (or (and a!10 (or (not J) (= C 4))) I))
      (a!55 (or (and a!54 (or (not H4) (= W3 4))) G4))
      (a!68 (or (and a!67 (or (not J) (= W3 4))) I))
      (a!99 (or (and a!98 (or (not H4) (= D 4))) G4)))
(let ((a!12 (or (and a!11 (or (not I) (= C 3))) H))
      (a!56 (or (and a!55 (or (not G4) (= W3 3))) F4))
      (a!69 (or (and a!68 (or (not I) (= W3 3))) H))
      (a!100 (or (and a!99 (or (not G4) (= D 3))) F4)))
(let ((a!13 (or (and a!12 (or (not H) (= C 2))) G))
      (a!57 (or (and a!56 (or (not F4) (= W3 2))) E4))
      (a!70 (or (and a!69 (or (not H) (= W3 2))) G))
      (a!101 (or (and a!100 (or (not F4) (= D 2))) E4)))
(let ((a!14 (or (and a!13 (or (not G) (= C 1))) F))
      (a!58 (or (and a!57 (or (not E4) (= W3 1))) D4))
      (a!71 (or (and a!70 (or (not G) (= W3 1))) F))
      (a!102 (or (and a!101 (or (not E4) (= D 1))) D4)))
(let ((a!59 (or (not P) (and a!58 (or (not D4) (= W3 0)))))
      (a!72 (or (not E) (and a!71 (or (not F) (= W3 0)) (= V3 G5) (= U3 H5)))))
(let ((a!60 (or (and a!59 (or (= W3 0) P)) C4))
      (a!73 (and (or (and (or E a!62) a!72) C4)
                 (or (not C4) (and (= W3 0) (= V3 0) (= U3 0))))))
(let ((a!61 (or (not R3)
                (and a!60 (or (not C4) (= W3 0)) (= V3 0) (= U3 0) (= Q B4))))
      (a!74 (or (not Y3) (and a!60 (or (not C4) (= W3 0)) (= V3 0) (= U3 0)))))
(let ((a!75 (and (or (not Z3) (and (or a!73 Y3) a!74))
                 (or Z3 a!62)
                 (= Q (and (not T5) B4)))))
  (and (not (= (= S 0) H1))
       (not (= (= U 0) A2))
       (not (= (= V 2) A1))
       (not (= (= X 3) C1))
       (not (= (= G1 4) Q1))
       (not (= (= J1 2) S1))
       (not (= (= L1 0) Z1))
       (not (= (= N1 4) V1))
       (not (= (= Y1 2) D2))
       (not (= (= F3 3) D3))
       (not (= (= I3 4) G2))
       (= A E6)
       (= B (= 1 P4))
       (= E (<= C 9))
       (= F (and (not U4) D4))
       (= G (and (not V4) E4))
       (= H (and (not W4) F4))
       (= I (and (not X4) G4))
       (= J (and (not Y4) H4))
       (= K (and (not A5) I4))
       (= L (and (not B5) J4))
       (= M (and (not C5) K4))
       (= N (and (not D5) L4))
       (= O (and (not E5) M4))
       (= P (<= D 9))
       (= W a!1)
       (= B1 (and A2 W (<= V 3) (>= V 1)))
       (= D1 (and (not B1) W (<= X 3) (>= X 1)))
       (= F1 (= I3 4))
       (= O1 (or T1 R1))
       (= R1 (and (<= V2 0) (= H3 2)))
       (= T1 (and A2 (not R1) H1 (= I1 3)))
       (= W1 (and Z1 (not O1) (= M1 3)))
       (= B2 (or W1 O1))
       (= F2 (and H1 F1 T (= I3 4)))
       (= O2 (= 3 A4))
       (= Q2 (= 2 A4))
       (= S2 (= 1 A4))
       a!2
       a!3
       (= G3 (and (not F2) (<= H3 3) (>= H3 1)))
       (= R3 A)
       (= G6 Z3)
       (= H6 Y3)
       (= J6 D4)
       (= K6 D4)
       (= L6 E4)
       (= M6 F4)
       (= N6 G4)
       (= O6 H4)
       (= P6 E4)
       (= Q6 I4)
       (= R6 J4)
       (= S6 K4)
       (= T6 L4)
       (= U6 M4)
       (= V6 F4)
       (= A7 G4)
       (= B7 H4)
       (= C7 I4)
       (= H7 O3)
       (= I7 J4)
       (= J7 B4)
       (= P7 M4)
       (= Q7 K4)
       (= R7 L4)
       (= S7 C4)
       (= K2 (+ (- 1) J5))
       (= L2 (+ (- 1) U5))
       (= M2 (+ (- 1) V5))
       (= N2 (+ (- 1) W5))
       (= P2 (+ (- 1) X5))
       (= R2 (+ (- 1) D6))
       a!5
       (= F6 A4)
       (= I6 X3)
       (= W6 W3)
       (= X6 V3)
       (= Y6 U3)
       (= Z6 T3)
       (= D7 Q3)
       (= E7 A4)
       (= F7 P3)
       (= K7 N3)
       (= L7 M3)
       (= M7 L3)
       (= N7 K3)
       (= O7 S3)
       (= T7 J3)
       (or (not (<= Z 3)) (not (>= Z 1)) (= V Z))
       (or (<= X3 0) (= R 1))
       (or (not (<= X3 0)) (= R 0))
       (or (and (<= Z 3) (>= Z 1)) (= V 1))
       (or (not F) (= C 0))
       a!14
       (or (not Q) (= S 1))
       (or (= S 0) Q)
       (or B1 (= X V))
       (or (= E1 J2) B1)
       a!15
       a!16
       (or D1 (= Y X))
       a!17
       (or (= V2 W2) F1)
       (or (not F1) (= V2 X3))
       (or (not K1) (= L1 1))
       (or (= L1 0) K1)
       (or R1 (= G1 H3))
       (or R1 (= I1 G1))
       (or (= U1 I2) R1)
       (or (not R1) a!18)
       a!19
       a!20
       (or T1 (= J1 I1))
       (or T1 (= M1 J1))
       (or (= X1 U1) T1)
       (or (not T1) a!21)
       a!22
       a!23
       (or W1 (= N1 M1))
       (or (= E2 X1) W1)
       a!24
       (or (and (= U2 V2) (= P1 N1)) W1)
       (or (not W1) a!25)
       a!26
       (or F2 (= Z I3))
       (or F2 (= I2 J2))
       (or (not F2) (= H3 Y))
       (or F2 (= H3 Z))
       (or (not F2) a!27)
       a!29
       (or (not G2) (= C3 4))
       (or G2 (= C3 I3))
       (or T2 (= Y1 P1))
       (or T2 (= C2 Y1))
       (or T2 (= H2 E2))
       (or (not T2) a!30)
       a!31
       a!32
       (or E3 (= F3 C2))
       (or (not E3) a!33)
       (or (not O3) (= P3 C3))
       (or (not O3) (= Q3 W2))
       a!34
       a!37
       a!39
       a!42
       a!43
       (or (not R3) (= K1 C4))
       (or (= Z3 B) R3)
       (or a!44 R3)
       (or (not R3) (= J2 0))
       (or R3 (= J2 O5))
       (or (not R3) (= W2 0))
       (or R3 (= W2 N5))
       (or (not R3) (= I3 0))
       (or R3 (= I3 P5))
       (or (not R3) (= J3 639))
       (or (not R3) (= K3 639))
       (or (not R3) (= L3 639))
       (or (not R3) (= M3 639))
       (or (not R3) (= N3 639))
       (or (not R3) (= T3 639))
       (or (and a!45 a!46 a!47 a!48 a!49) R3)
       a!61
       (or (not R3) (and B3 A3 Z2 Y2 X2))
       (or a!75 R3)
       (or (not R3) a!77)
       a!79
       a!81
       a!83
       a!85
       a!87
       a!89
       a!91
       (or (and (or Z3 Y3) a!92) R3)
       a!93
       (or (not R3) O3)
       (or (not R3) Y3)
       (or (not R3) Z3)
       (or (not D4) (= D 0))
       a!102
       (or (not N4) (= U 1))
       (or N4 (= U 0))
       (or (not R3) O4)
       (= G7 true)
       (not U7)
       (not (= (= R 0) T))))))))))))))))
      )
      (top_step B4
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
          K6
          L6
          M6
          N6
          O6
          P6
          Q6
          R6
          S6
          T6
          U6
          V6
          W6
          X6
          Y6
          Z6
          A7
          B7
          C7
          D7
          E7
          F7
          G7
          H7
          I7
          J7
          K7
          L7
          M7
          N7
          O7
          P7
          Q7
          R7
          S7
          T7
          U7)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      INIT_STATE
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Int) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Int) (E2 Bool) (F2 Bool) (G2 Int) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Bool) (O3 Bool) (P3 Bool) (Q3 Bool) (R3 Int) (S3 Bool) (T3 Int) (U3 Bool) (V3 Bool) (W3 Int) (X3 Bool) (Y3 Bool) (Z3 Bool) (A4 Bool) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Bool) (P4 Bool) (Q4 Bool) (R4 Int) (S4 Int) (T4 Int) (U4 Bool) (V4 Bool) (W4 Bool) (X4 Bool) (Y4 Int) (Z4 Int) (A5 Int) (B5 Int) (C5 Int) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Int) (I5 Bool) (J5 Bool) ) 
    (=>
      (and
        (top_step Q1
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
          J5
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
          I5)
        INIT_STATE
        (top_reset A
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
           S3)
        true
      )
      (MAIN T3
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
      J5)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Int) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Int) (D2 Bool) (E2 Int) (F2 Bool) (G2 Bool) (H2 Int) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Int) (D3 Int) (E3 Int) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Bool) (P3 Bool) (Q3 Bool) (R3 Bool) (S3 Int) (T3 Bool) (U3 Bool) ) 
    (=>
      (and
        (top_step B
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
          U3
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
          T3)
        (MAIN O
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
      A)
        true
      )
      (MAIN E2
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
      U3)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Int) (P1 Bool) (Q1 Bool) ) 
    (=>
      (and
        (MAIN A
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
      Q1)
        (not Q1)
      )
      ERR
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        ERR
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
