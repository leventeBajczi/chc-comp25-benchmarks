(set-logic HORN)


(declare-fun |ERR| ( ) Bool)
(declare-fun |MAIN| ( Int Bool Bool Int Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Bool Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Int Bool Bool ) Bool)
(declare-fun |top_step| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Bool Int Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Bool Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Int Bool Int Bool Bool Int Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Bool Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Int Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |top_reset| ( Int Bool Bool Int Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Bool Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Int Bool Int Bool Bool Int Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Bool Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Int Int Bool Int Bool ) Bool)

(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Bool) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Bool) (Q1 Int) (R1 Bool) (S1 Int) (T1 Bool) (U1 Bool) (V1 Int) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Int) (N2 Int) (O2 Int) (P2 Bool) (Q2 Int) (R2 Int) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Int) (W2 Int) (X2 Int) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Bool) (I3 Int) (J3 Bool) ) 
    (=>
      (and
        (and (= U1 C)
     (= W1 E)
     (= X1 F)
     (= Y1 G)
     (= A2 I)
     (= B2 J)
     (= C2 K)
     (= D2 L)
     (= E2 M)
     (= F2 N)
     (= G2 O)
     (= H2 P)
     (= I2 Q)
     (= J2 R)
     (= K2 S)
     (= L2 T)
     (= P2 X)
     (= S2 A1)
     (= T2 B1)
     (= U2 C1)
     (= Y2 G1)
     (= Z2 H1)
     (= A3 I1)
     (= B3 J1)
     (= H3 P1)
     (= S1 A)
     (= V1 D)
     (= Z1 H)
     (= M2 U)
     (= N2 V)
     (= O2 W)
     (= Q2 Y)
     (= R2 Z)
     (= V2 D1)
     (= W2 E1)
     (= X2 F1)
     (= C3 K1)
     (= D3 L1)
     (= E3 M1)
     (= F3 N1)
     (= G3 O1)
     (= I3 Q1)
     (= J3 true)
     (= T1 B))
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
           F3
           G3
           H3
           I3
           J3)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Bool) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Int) (F1 Bool) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Bool) (P1 Int) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Int) (V1 Bool) (W1 Bool) (X1 Int) (Y1 Int) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Int) (D2 Bool) (E2 Int) (F2 Bool) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Bool) (O2 Int) (P2 Int) (Q2 Bool) (R2 Bool) (S2 Int) (T2 Int) (U2 Int) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Int) (O3 Bool) (P3 Bool) (Q3 Int) (R3 Bool) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Bool) (B4 Int) (C4 Int) (D4 Int) (E4 Int) (F4 Int) (G4 Bool) (H4 Bool) (I4 Int) (J4 Int) (K4 Int) (L4 Int) (M4 Bool) (N4 Bool) (O4 Int) (P4 Int) (Q4 Bool) (R4 Bool) (S4 Int) (T4 Bool) (U4 Bool) (V4 Bool) (W4 Bool) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Int) (I5 Bool) (J5 Bool) (K5 Int) (L5 Bool) (M5 Bool) (N5 Bool) (O5 Int) (P5 Bool) (Q5 Bool) (R5 Bool) (S5 Bool) (T5 Bool) (U5 Bool) (V5 Bool) (W5 Bool) (X5 Bool) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Int) (C6 Int) (D6 Int) (E6 Bool) (F6 Int) (G6 Int) (H6 Bool) (I6 Bool) (J6 Bool) (K6 Int) (L6 Int) (M6 Int) (N6 Bool) (O6 Bool) (P6 Bool) (Q6 Bool) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Int) (Y6 Bool) (Z6 Int) (A7 Bool) (B7 Bool) (C7 Int) (D7 Bool) (E7 Bool) (F7 Bool) (G7 Int) (H7 Bool) (I7 Bool) (J7 Bool) (K7 Bool) (L7 Bool) (M7 Bool) (N7 Bool) (O7 Bool) (P7 Bool) (Q7 Bool) (R7 Bool) (S7 Bool) (T7 Int) (U7 Int) (V7 Int) (W7 Bool) (X7 Int) (Y7 Int) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Int) (D8 Int) (E8 Int) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Int) (K8 Int) (L8 Int) (M8 Int) (N8 Int) (O8 Bool) (P8 Int) (Q8 Bool) ) 
    (=>
      (and
        (let ((a!1 (and (or (not (<= Z 3)) (not (>= Z 1))) (<= V 3) (>= V 1)))
      (a!2 (= R2 (and (not B2) (not (<= S2 0)) (= P1 2))))
      (a!3 (= P3 (and (not R2) (not B2) (or (not A2) Z1) (= C2 2))))
      (a!4 (div (+ C4 (* (- 60) (div C4 60))) 10))
      (a!6 (or (and (or (not O) (= C 9)) (or O (= C 10))) N))
      (a!15 (or (not B1) (and (or A1 (= X V)) (or (not A1) (= X 2)))))
      (a!16 (or (not B1) (and (or (= E1 J2) A1) (or (not A1) (= E1 2)))))
      (a!17 (or (not D1) (and (or C1 (= Y X)) (or (not C1) (= Y 3)))))
      (a!18 (and (or (and (<= S3 3) (>= S3 1)) (= G1 S3))
                 (or (not (<= S3 3)) (not (>= S3 1)) (= G1 0))))
      (a!19 (or (not R1) (and (or Q1 (= I1 G1)) (or (not Q1) (= I1 4)))))
      (a!20 (or (not R1) (and (or (= U1 I2) Q1) (or (not Q1) (= U1 1)))))
      (a!21 (and (or (= J1 I1) (= I1 3)) (or (not (= I1 3)) (= J1 1))))
      (a!22 (or (not T1) (and (or S1 (= M1 J1)) (or (not S1) (= M1 2)))))
      (a!23 (or (not T1) (and (or (= X1 U1) S1) (or (not S1) (= X1 2)))))
      (a!24 (or (not W1)
                (and (or V1 (= P1 N1)) (or (not V1) (= P1 4)) (= S2 0))))
      (a!25 (and (or (and (<= M1 3) (>= M1 1)) (= N1 M1))
                 (or (not (<= M1 3)) (not (>= M1 1)) (= N1 0))))
      (a!26 (or (not W1) (and (or (= E2 X1) V1) (or (not V1) (= E2 1)))))
      (a!27 (and (or (= T3 4) (= Z T3)) (or (not (= T3 4)) (= Z 0))))
      (a!28 (or (not D1) (and (or (= I2 E1) C1) (or (not C1) (= I2 3)))))
      (a!30 (and (or (= Y1 P1) (= P1 2)) (or (not (= P1 2)) (= Y1 1))))
      (a!31 (or (not R2) (and (or D2 (= C2 Y1)) (or (not D2) (= C2 2)))))
      (a!32 (or (not R2) (and (or (= H2 E2) D2) (or (not D2) (= H2 2)))))
      (a!33 (and (or (= Q3 C2) (= C2 2)) (or (not (= C2 2)) (= Q3 1))))
      (a!34 (or (not A4) (and (or (= O4 J2) G2) (or (not G2) (= O4 1)))))
      (a!35 (or (not P3) (and (or O3 (= O4 H2)) (or (not O3) (= O4 3)))))
      (a!38 (and (or (= C4 S2) R2) (or (not R2) (= C4 (+ (- 1) S2)))))
      (a!40 (or (not P3) (and (or (= B4 Q3) O3) (or (not O3) (= B4 3)))))
      (a!43 (or (not H4) (and (or (not G4) (= S4 F4)) (or (= S4 0) G4))))
      (a!44 (or (= K1 (and (not W6) U4)) Q4))
      (a!45 (or (= L4 (+ V3 (* 10 D4) (* 60 P4))) U4 (not N4)))
      (a!46 (= G5 (or (not R4) (not (<= S4 0)))))
      (a!47 (= E3 (or S5 (not W4) (and (not N5) V4) U4 (= V3 1) (not N4))))
      (a!48 (= D3
               (or Y5
                   (not X4)
                   (and (not N5) V4)
                   (and (not S5) W4)
                   U4
                   (= V3 2)
                   (not N4))))
      (a!49 (= C3
               (or E6
                   (not Y4)
                   (and (not N5) V4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 3)
                   (not N4))))
      (a!50 (= B3
               (or H6
                   (not Z4)
                   (and (not N5) V4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 4)
                   (not N4))))
      (a!51 (= A3
               (or I6
                   (not A5)
                   (and (not N5) V4)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 5)
                   (not N4))))
      (a!52 (= Z2
               (or J6
                   (not B5)
                   (and (not N5) V4)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 6)
                   (not N4))))
      (a!53 (= Y2
               (or Q6
                   (not C5)
                   (and (not N5) V4)
                   (and (not J6) B5)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 7)
                   (not N4))))
      (a!54 (= X2
               (or J5
                   (not D5)
                   (and (not N5) V4)
                   (and (not Q6) C5)
                   (and (not J6) B5)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 8)
                   (not N4))))
      (a!55 (= W2
               (or I5
                   (not E5)
                   (and (not N5) V4)
                   (and (not J5) D5)
                   (and (not Q6) C5)
                   (and (not J6) B5)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 9)
                   (not N4))))
      (a!56 (= V2
               (or (and (not N5) V4)
                   (and (not I5) E5)
                   (and (not J5) D5)
                   (and (not Q6) C5)
                   (and (not J6) B5)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= V3 V6)
                   (not N4))))
      (a!58 (and E3
                 D3
                 C3
                 B3
                 A3
                 Z2
                 Y2
                 X2
                 W2
                 V2
                 (= F3 (or U4 (= V3 0) (not V4) (not N4)))))
      (a!59 (or (and (or (not E5) (= K4 9)) (or E5 (= K4 10))) D5))
      (a!71 (and (or Q6 (not C5))
                 (or J6 (not B5))
                 (or I6 (not A5))
                 (or H6 (not Z4))
                 (or E6 (not Y4))
                 (or Y5 (not X4))
                 (or S5 (not W4))
                 (or N5 (not V4))
                 (or J5 (not D5))
                 (or I5 (not E5))))
      (a!72 (div (+ L4 (* (- 60) (div L4 60))) 10))
      (a!73 (= G3
               (or (and (not N5) V4)
                   (and (not I5) E5)
                   (and (not J5) D5)
                   (and (not Q6) C5)
                   (and (not J6) B5)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= D4 G6)
                   (not N4))))
      (a!76 (= J3
               (or (and (not N5) V4)
                   (and (not I5) E5)
                   (and (not J5) D5)
                   (and (not Q6) C5)
                   (and (not J6) B5)
                   (and (not I6) A5)
                   (and (not H6) Z4)
                   (and (not E6) Y4)
                   (and (not Y5) X4)
                   (and (not S5) W4)
                   U4
                   (= P4 H5)
                   (not N4))))
      (a!78 (and (= K4 B6) (= J4 C6) (= I4 D6)))
      (a!79 (or (and (or (not O) (= K4 9)) (or (= K4 10) O)) N))
      (a!92 (and (not E5)
                 (not D5)
                 (not C5)
                 (not B5)
                 (not A5)
                 (not Z4)
                 (not Y4)
                 (not X4)
                 (not W4)
                 (not V4)))
      (a!95 (= L4 (+ K4 (* 10 J4) (* 60 I4))))
      (a!99 (and (or (<= L2 0) (= Z3 L2)) (or (not (<= L2 0)) (= Z3 0))))
      (a!101 (and (or (<= M2 0) (= X3 M2)) (or (not (<= M2 0)) (= X3 0))))
      (a!103 (and (or (<= K2 0) (= E4 K2)) (or (not (<= K2 0)) (= E4 0))))
      (a!105 (and (or (<= P2 0) (= U3 P2)) (or (not (<= P2 0)) (= U3 0))))
      (a!107 (or (not H4) (and (or (not G4) (= Y3 F4)) (or G4 (= Y3 0)))))
      (a!109 (or (not N4) (and (or (not L5) (not M4)) (or L5 (= M4 M5)))))
      (a!110 (and (or (<= O2 0) (= W3 O2)) (or (not (<= O2 0)) (= W3 0))))
      (a!112 (or (and (or (not N6) (not A4)) (or N6 (= A4 O6))) Q4))
      (a!113 (or (and (or (not E5) (= D 9)) (or E5 (= D 10))) D5)))
(let ((a!5 (= V3 (+ C4 (* (- 60) (div C4 60)) (* (- 10) a!4))))
      (a!7 (or (and a!6 (or (not N) (= C 8))) M))
      (a!29 (or (not F2) (and a!28 (or (= I2 E1) D1))))
      (a!36 (or (not R3) (and a!35 (or P3 (= O4 H2)))))
      (a!39 (or (and (or (not R3) a!38) (or R3 (= C4 T2))) A4))
      (a!41 (or (not R3) (and a!40 (or (= B4 Q3) P3))))
      (a!57 (and (= F3 (or N5 U4 (= V3 0) (not V4) (not N4)))
                 a!47
                 a!48
                 a!49
                 a!50
                 a!51
                 a!52
                 a!53
                 a!54
                 a!55
                 a!56))
      (a!60 (or (and a!59 (or (not D5) (= K4 8))) C5))
      (a!74 (and (= I3 (or a!71 U4 (= D4 V6) (not N4)))
                 (= H3 (or (= D4 a!72) a!71 U4 (not N4)))
                 a!73))
      (a!75 (= K3 (or (= P4 (div L4 60)) a!71 U4 (not N4))))
      (a!80 (or (and a!79 (or (not N) (= K4 8))) M))
      (a!93 (= K3 (or (= P4 (div L4 60)) a!92 U4 (not N4))))
      (a!96 (and (or (and (not N4) M4) a!95) (or (not M4) N4 (= L4 0))))
      (a!97 (or (and (not N4) M4) (and (or N4 (= L4 O5)) (or (not N4) a!95))))
      (a!100 (or (and (or a!99 N2) (or (not N2) (= Z3 639))) Q4))
      (a!102 (or (and (or (not N2) a!101) (or (= X3 639) N2)) Q4))
      (a!104 (or (and (or (not Q2) a!103) (or Q2 (= E4 639))) Q4))
      (a!106 (or (and (or a!105 Q2) (or (not Q2) (= U3 639))) Q4))
      (a!108 (or (and a!107 (or H4 (= Y3 639))) Q4))
      (a!111 (or (and (or a!110 R4) (or (not R4) (= W3 639))) Q4))
      (a!114 (or (and a!113 (or (not D5) (= D 8))) C5)))
(let ((a!8 (or (and a!7 (or (not M) (= C 7))) L))
      (a!37 (or (and a!36 (or R3 (= O4 I2))) A4))
      (a!42 (or (and a!41 (or (= B4 S3) R3)) A4))
      (a!61 (or (and a!60 (or (not C5) (= K4 7))) B5))
      (a!77 (and (= L3 (or a!71 U4 (= P4 G6) (not N4))) a!75 a!76))
      (a!81 (or (and a!80 (or (not M) (= K4 7))) L))
      (a!94 (and J3 (= L3 (or a!92 U4 (= P4 0) (not N4))) a!93))
      (a!98 (or (and a!97 (or (not M4) N4 (= L4 0))) Q4))
      (a!115 (or (and a!114 (or (not C5) (= D 7))) B5)))
(let ((a!9 (or (and a!8 (or (not L) (= C 6))) K))
      (a!62 (or (and a!61 (or (not B5) (= K4 6))) A5))
      (a!82 (or (and a!81 (or (not L) (= K4 6))) K))
      (a!116 (or (and a!115 (or (not B5) (= D 6))) A5)))
(let ((a!10 (or (and a!9 (or (not K) (= C 5))) J))
      (a!63 (or (and a!62 (or (not A5) (= K4 5))) Z4))
      (a!83 (or (and a!82 (or (not K) (= K4 5))) J))
      (a!117 (or (and a!116 (or (not A5) (= D 5))) Z4)))
(let ((a!11 (or (and a!10 (or (not J) (= C 4))) I))
      (a!64 (or (and a!63 (or (not Z4) (= K4 4))) Y4))
      (a!84 (or (and a!83 (or (not J) (= K4 4))) I))
      (a!118 (or (and a!117 (or (not Z4) (= D 4))) Y4)))
(let ((a!12 (or (and a!11 (or (not I) (= C 3))) H))
      (a!65 (or (and a!64 (or (not Y4) (= K4 3))) X4))
      (a!85 (or (and a!84 (or (not I) (= K4 3))) H))
      (a!119 (or (and a!118 (or (not Y4) (= D 3))) X4)))
(let ((a!13 (or (and a!12 (or (not H) (= C 2))) G))
      (a!66 (or (and a!65 (or (not X4) (= K4 2))) W4))
      (a!86 (or (and a!85 (or (not H) (= K4 2))) G))
      (a!120 (or (and a!119 (or (not X4) (= D 2))) W4)))
(let ((a!14 (or (and a!13 (or (not G) (= C 1))) F))
      (a!67 (or (and a!66 (or (not W4) (= K4 1))) V4))
      (a!87 (or (and a!86 (or (not G) (= K4 1))) F))
      (a!121 (or (and a!120 (or (not W4) (= D 1))) V4)))
(let ((a!68 (or (not P) (and a!67 (or (not V4) (= K4 0)))))
      (a!88 (or (not E) (and a!87 (or (not F) (= K4 0)) (= J4 B6) (= I4 C6)))))
(let ((a!69 (or (and a!68 (or (= K4 0) P)) U4))
      (a!89 (and (or (and (or E a!78) a!88) U4)
                 (or (not U4) (and (= K4 0) (= J4 0) (= I4 0))))))
(let ((a!70 (or (not Q4)
                (and a!69 (or (not U4) (= K4 0)) (= J4 0) (= I4 0) (= Q T4))))
      (a!90 (or (not M4) (and a!69 (or (not U4) (= K4 0)) (= J4 0) (= I4 0)))))
(let ((a!91 (and (or (not N4) (and (or a!89 M4) a!90))
                 (or N4 a!78)
                 (= Q (and (not P6) T4)))))
  (and (not (= (= S 0) H1))
       (not (= (= U 0) A2))
       (not (= (= V 2) A1))
       (not (= (= X 3) C1))
       (not (= (= G1 4) Q1))
       (not (= (= J1 2) S1))
       (not (= (= L1 0) Z1))
       (not (= (= N1 4) V1))
       (not (= (= Y1 2) D2))
       (not (= (= Q3 3) O3))
       (not (= (= T3 4) G2))
       (not (= (<= F4 0) G4))
       (= A Y6)
       (= B (= 1 K5))
       (= E (<= C 9))
       (= F (and (not P5) V4))
       (= G (and (not Q5) W4))
       (= H (and (not R5) X4))
       (= I (and (not T5) Y4))
       (= J (and (not U5) Z4))
       (= K (and (not V5) A5))
       (= L (and (not W5) B5))
       (= M (and (not X5) C5))
       (= N (and (not Z5) D5))
       (= O (and (not A6) E5))
       (= P (<= D 9))
       (= W a!1)
       (= B1 (and A2 W (<= V 3) (>= V 1)))
       (= D1 (and (not B1) W (<= X 3) (>= X 1)))
       (= F1 (= T3 4))
       (= O1 (or T1 R1))
       (= R1 (and (<= T2 0) (= S3 2)))
       (= T1 (and A2 (not R1) H1 (= I1 3)))
       (= W1 (and Z1 (not O1) (= M1 3)))
       (= B2 (or W1 O1))
       (= F2 (and H1 F1 T (= T3 4)))
       (= N2 (= 3 O4))
       (= Q2 (= 1 O4))
       a!2
       a!3
       (= R3 (and (not F2) (<= S3 3) (>= S3 1)))
       (= H4 R4)
       (= Q4 A)
       (= R4 (= 2 O4))
       (= A7 E5)
       (= B7 D5)
       (= D7 N4)
       (= E7 M4)
       (= F7 V4)
       (= H7 V4)
       (= I7 W4)
       (= J7 X4)
       (= K7 W4)
       (= L7 Y4)
       (= M7 Z4)
       (= N7 A5)
       (= O7 B5)
       (= P7 C5)
       (= Q7 X4)
       (= R7 D5)
       (= S7 E5)
       (= W7 Y4)
       (= Z7 Z4)
       (= A8 A5)
       (= B8 B5)
       (= G8 A4)
       (= H8 T4)
       (= I8 C5)
       (= O8 U4)
       (= K2 (+ (- 1) F6))
       (= L2 (+ (- 1) R6))
       (= M2 (+ (- 1) T6))
       (= O2 (+ (- 1) U6))
       (= P2 (+ (- 1) X6))
       a!5
       (= D4 a!4)
       (= F4 (+ (- 1) S6))
       (= P4 (div C4 60))
       (= Z6 P4)
       (= C7 O4)
       (= G7 L4)
       (= T7 K4)
       (= U7 J4)
       (= V7 I4)
       (= X7 E4)
       (= Y7 D4)
       (= C8 C4)
       (= D8 O4)
       (= E8 B4)
       (= J8 Z3)
       (= K8 Y3)
       (= L8 X3)
       (= M8 W3)
       (= N8 V3)
       (= P8 U3)
       (or (not (<= Z 3)) (not (>= Z 1)) (= V Z))
       (or (<= L4 0) (= R 1))
       (or (not (<= L4 0)) (= R 0))
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
       (or (= T2 U2) F1)
       (or (not F1) (= T2 L4))
       (or (not K1) (= L1 1))
       (or (= L1 0) K1)
       (or R1 (= G1 S3))
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
       (or (and (= S2 T2) (= P1 N1)) W1)
       (or (not W1) a!25)
       a!26
       (or F2 (= Z T3))
       (or F2 (= I2 J2))
       (or (not F2) (= S3 Y))
       (or F2 (= S3 Z))
       (or (not F2) a!27)
       a!29
       (or (not G2) (= N3 4))
       (or G2 (= N3 T3))
       (or R2 (= Y1 P1))
       (or R2 (= C2 Y1))
       (or R2 (= H2 E2))
       (or (not R2) a!30)
       a!31
       a!32
       (or P3 (= Q3 C2))
       (or (not P3) a!33)
       (or (not A4) (= B4 N3))
       (or (not A4) (= C4 U2))
       a!34
       a!37
       a!39
       a!42
       (or (= S4 639) H4)
       a!43
       a!44
       (or (not Q4) (= K1 U4))
       (or (= M3 a!45) Q4)
       (or (= N4 B) Q4)
       (or a!46 Q4)
       (or (not Q4) (= J2 0))
       (or Q4 (= J2 L6))
       (or (not Q4) (= U2 0))
       (or Q4 (= U2 K6))
       (or (not Q4) (= T3 0))
       (or Q4 (= T3 M6))
       (or (not Q4) (= U3 639))
       (or (not Q4) (= W3 639))
       (or (not Q4) (= X3 639))
       (or (not Q4) (= Y3 639))
       (or (not Q4) (= Z3 639))
       (or (not Q4) (= E4 639))
       (or a!57 Q4)
       (or (not Q4) a!58)
       a!70
       (or a!74 Q4)
       (or a!77 Q4)
       (or a!91 Q4)
       (or (not Q4) (and I3 H3 G3))
       (or (not Q4) a!94)
       (or (not Q4) a!96)
       a!98
       a!100
       a!102
       a!104
       a!106
       a!108
       (or (and (or N4 M4) a!109) Q4)
       a!111
       a!112
       (or (not Q4) M3)
       (or (not Q4) A4)
       (or (not Q4) M4)
       (or (not Q4) N4)
       (or (not V4) (= D 0))
       a!121
       (or (not F5) (= U 1))
       (or F5 (= U 0))
       (or (not Q4) G5)
       (= F8 true)
       (not Q8)
       (not (= (= R 0) T))))))))))))))))
      )
      (top_step T4
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
          U7
          V7
          W7
          X7
          Y7
          Z7
          A8
          B8
          C8
          D8
          E8
          F8
          G8
          H8
          I8
          J8
          K8
          L8
          M8
          N8
          O8
          P8
          Q8)
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
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Bool) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Bool) (Q1 Int) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Int) (G2 Bool) (H2 Bool) (I2 Int) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Int) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Int) (A3 Int) (B3 Int) (C3 Bool) (D3 Int) (E3 Int) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Int) (J3 Int) (K3 Int) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Bool) (V3 Int) (W3 Bool) (X3 Int) (Y3 Bool) (Z3 Bool) (A4 Int) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Int) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Bool) (N4 Bool) (O4 Bool) (P4 Bool) (Q4 Bool) (R4 Int) (S4 Int) (T4 Int) (U4 Bool) (V4 Int) (W4 Int) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Int) (B5 Int) (C5 Int) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Int) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Bool) (N5 Int) (O5 Bool) (P5 Bool) ) 
    (=>
      (and
        (top_step S1
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
          P5
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
          O5)
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
           Q1
           R1
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
           W3)
        true
      )
      (MAIN X3
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
      P5)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Int) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Bool) (V Int) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Bool) (E2 Int) (F2 Bool) (G2 Int) (H2 Bool) (I2 Bool) (J2 Int) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Int) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Int) (B3 Int) (C3 Int) (D3 Bool) (E3 Int) (F3 Int) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Int) (K3 Int) (L3 Int) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Bool) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Bool) (W3 Int) (X3 Bool) (Y3 Bool) ) 
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
          Y3
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
          X3)
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
      E2
      F2
      A)
        true
      )
      (MAIN G2
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
      Y3)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Bool) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Bool) (Q1 Int) (R1 Bool) (S1 Bool) ) 
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
      Q1
      R1
      S1)
        (not S1)
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
