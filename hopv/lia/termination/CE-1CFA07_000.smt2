(set-logic HORN)


(declare-fun |f_1034$unknown:59| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |fail$unknown:66| ( Int ) Bool)
(declare-fun |app_without_checking_1355$unknown:33| ( Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |app_without_checking_1355$unknown:28| ( Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |f_1034$unknown:64| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |app_1038$unknown:16| ( Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (|app_1038$unknown:16| K J I H G F E D C B A)
        (and (= L 1) (= 0 H))
      )
      (|app_without_checking_1355$unknown:33| K J I H G F E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) ) 
    (=>
      (and
        (|f_1034$unknown:59| A C B G1 S1 R1 Q1 D P1 O1 N1 M1 L1 K1 F J1 I1 H1)
        (and (= D 0)
     (= J 0)
     (= I 0)
     (= H 0)
     (= G 0)
     (= F 0)
     (= K 0)
     (= C1 0)
     (= B1 0)
     (= A1 0)
     (= Z 0)
     (= Y 0)
     (= X 0)
     (= W 0)
     (= V 0)
     (= U 0)
     (= T 0)
     (= S 0)
     (= R 0)
     (= Q 0)
     (= P 0)
     (= O 0)
     (= N 0)
     (= M 0)
     (= L 0)
     (= R1 0)
     (= Q1 0)
     (= P1 0)
     (= O1 0)
     (= N1 0)
     (= M1 0)
     (= L1 0)
     (= K1 0)
     (= J1 0)
     (= I1 0)
     (= H1 0)
     (= F1 0)
     (= E1 0)
     (= D1 0)
     (= L2 0)
     (= K2 0)
     (= J2 0)
     (= I2 0)
     (= H2 0)
     (= G2 0)
     (= F2 0)
     (= E2 0)
     (= D2 0)
     (= C2 0)
     (= B2 0)
     (= A2 0)
     (= Z1 0)
     (= Y1 0)
     (= X1 0)
     (= W1 1)
     (= V1 0)
     (= U1 0)
     (= T1 0)
     (= S1 0)
     (= E 0))
      )
      (|app_without_checking_1355$unknown:33| A C B G1 F1 E1 D1 E C1 B1 A1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (|app_1038$unknown:16| K J I H G F E D C B A)
        (and (= L 1) (not (= 0 H)))
      )
      (|fail$unknown:66| L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (v_12 Int) (v_13 Int) ) 
    (=>
      (and
        (|app_without_checking_1355$unknown:33| K J I H G F E D C B A)
        (and (= L 1) (= v_12 K) (= v_13 D))
      )
      (|app_without_checking_1355$unknown:28| K v_12 D L G F E v_13 C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) ) 
    (=>
      (and
        (|app_without_checking_1355$unknown:28| C B A U A1 Z Y G X W V)
        (and (= E 0)
     (= W 0)
     (= V 0)
     (= T 0)
     (= S 0)
     (= R 0)
     (= Q 0)
     (= P 0)
     (= O 0)
     (= N 0)
     (= M 0)
     (= L 0)
     (= K 0)
     (= J 0)
     (= I 0)
     (= H 0)
     (= G 0)
     (= F 0)
     (= L1 0)
     (= K1 0)
     (= J1 0)
     (= I1 0)
     (= H1 0)
     (= G1 0)
     (= F1 0)
     (= E1 0)
     (= D1 0)
     (= C1 0)
     (= B1 0)
     (= A1 0)
     (= Z 0)
     (= Y 0)
     (= X 0)
     (= F2 0)
     (= E2 0)
     (= D2 0)
     (= C2 0)
     (= B2 0)
     (= A2 0)
     (= Z1 0)
     (= Y1 0)
     (= X1 0)
     (= W1 0)
     (= V1 0)
     (= U1 0)
     (= T1 0)
     (= S1 0)
     (= R1 0)
     (= Q1 1)
     (= P1 0)
     (= O1 0)
     (= N1 0)
     (= M1 0)
     (= D 0))
      )
      (|f_1034$unknown:64| C B A U T S R H Q P O N M L J F2 E2 D2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) ) 
    (=>
      (and
        (and (= F 0)
     (= E 0)
     (= D 0)
     (= C 0)
     (= B 0)
     (= G 0)
     (= Y 0)
     (= X 0)
     (= W 0)
     (= V 0)
     (= U 0)
     (= T 0)
     (= S 0)
     (= R 0)
     (= Q 0)
     (= P 0)
     (= O 0)
     (= N 0)
     (= M 0)
     (= L 0)
     (= K 0)
     (= J 0)
     (= I 0)
     (= H 0)
     (= N1 0)
     (= M1 0)
     (= L1 0)
     (= K1 0)
     (= J1 0)
     (= I1 0)
     (= H1 0)
     (= G1 0)
     (= F1 0)
     (= E1 0)
     (= D1 0)
     (= C1 0)
     (= B1 0)
     (= A1 0)
     (= Z 0)
     (= H2 0)
     (= G2 0)
     (= F2 0)
     (= E2 0)
     (= D2 0)
     (= C2 0)
     (= B2 0)
     (= A2 0)
     (= Z1 0)
     (= Y1 0)
     (= X1 0)
     (= W1 0)
     (= V1 0)
     (= U1 0)
     (= T1 0)
     (= S1 1)
     (= R1 0)
     (= Q1 0)
     (= P1 0)
     (= O1 0)
     (= A 0))
      )
      (|f_1034$unknown:64| S1 R1 Q1 P1 O1 N1 M1 A L1 K1 J1 I1 H1 G1 C F1 E1 D1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) ) 
    (=>
      (and
        (|f_1034$unknown:64| R Q P O N M L K J I H G F E D C B A)
        true
      )
      (|f_1034$unknown:59| R Q P O N M L K J I H G F E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) ) 
    (=>
      (and
        (|f_1034$unknown:59| A C B W1 T S R H Q P O N M L J Z1 Y1 X1)
        (and (= P 0)
     (= O 0)
     (= N 0)
     (= M 0)
     (= L 0)
     (= K 0)
     (= J 0)
     (= I 0)
     (= H 0)
     (= G 0)
     (= F 0)
     (= E 0)
     (= D 0)
     (= F1 0)
     (= E1 0)
     (= D1 0)
     (= C1 0)
     (= B1 0)
     (= A1 0)
     (= Z 0)
     (= Y 0)
     (= X 0)
     (= W 0)
     (= V 0)
     (= U 0)
     (= T 0)
     (= S 0)
     (= R 0)
     (= Z1 0)
     (= Y1 0)
     (= X1 0)
     (= V1 0)
     (= U1 0)
     (= T1 0)
     (= S1 0)
     (= R1 0)
     (= Q1 0)
     (= P1 0)
     (= O1 0)
     (= N1 0)
     (= M1 0)
     (= L1 0)
     (= K1 0)
     (= J1 1)
     (= I1 0)
     (= H1 0)
     (= G1 0)
     (= Q 0))
      )
      (|app_1038$unknown:16| A C B W1 V1 U1 T1 I S1 R1 Q1)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (|fail$unknown:66| A)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
