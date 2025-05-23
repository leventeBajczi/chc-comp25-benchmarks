(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Bool) (U Bool) (V Bool) (W Bool) ) 
    (=>
      (and
        (and (not V) (not U) (not T) (not W))
      )
      (state W V U T F E G H I J K L M N O Q S P R D C B A)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Bool) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) ) 
    (=>
      (and
        (state B3 A3 Z2 Y2 M K O Q S U W Y A1 C1 E1 I1 M1 F1 J1 H E C A)
        (let ((a!1 (or (and (= R1 I) (= R1 0.0) (= D Y1) (not (= D 0.0)))
               (and (= R1 0.0) (= I 3221225659.0) (= D Y1) (= D 0.0))))
      (a!6 (or (and (= R1 I) (= R1 0.0) (= D Q1) (not (= D 0.0)))
               (and (= R1 0.0) (= I 3221225659.0) (= D Q1) (= D 0.0))))
      (a!12 (or (and (= R1 I) (= R1 0.0) (= D D2) (not (= D 0.0)))
                (and (= R1 0.0) (= I 3221225659.0) (= D D2) (= D 0.0))))
      (a!15 (or (and (= R1 I) (= R1 0.0) (= D S2) (not (= D 0.0)))
                (and (= R1 0.0) (= I 3221225659.0) (= D S2) (= D 0.0))))
      (a!18 (or (and (= R1 I) (= R1 0.0) (= D I2) (not (= D 0.0)))
                (and (= R1 0.0) (= I 3221225659.0) (= D I2) (= D 0.0))))
      (a!20 (or (and (= R1 I) (= R1 0.0) (= D N2) (not (= D 0.0)))
                (and (= R1 0.0) (= I 3221225659.0) (= D N2) (= D 0.0)))))
(let ((a!2 (or (and a!1
                    (= Z1 3.0)
                    (= T1 0.0)
                    (= S1 1.0)
                    (= K1 X1)
                    (= K1 0.0)
                    (= N 0.0)
                    (= N 1.0)
                    (= B T1))
               (and a!1
                    (= Z1 3.0)
                    (= T1 0.0)
                    (= S1 1.0)
                    (= K1 X1)
                    (= K1 0.0)
                    (not (= N 0.0))
                    (= N 1.0)
                    (= B 1.0))))
      (a!7 (or (and a!6
                    (= U1 3.0)
                    (= T1 0.0)
                    (= S1 1.0)
                    (= K1 P1)
                    (= K1 0.0)
                    (= N 0.0)
                    (= N 1.0)
                    (= B T1))
               (and a!6
                    (= U1 3.0)
                    (= T1 0.0)
                    (= S1 1.0)
                    (= K1 P1)
                    (= K1 0.0)
                    (not (= N 0.0))
                    (= N 1.0)
                    (= B 1.0))))
      (a!13 (or (and a!12
                     (= E2 3.0)
                     (= T1 0.0)
                     (= K1 C2)
                     (= K1 0.0)
                     (= N 0.0)
                     (= N 1.0)
                     (= G 1.0)
                     (= B T1))
                (and a!12
                     (= E2 3.0)
                     (= T1 0.0)
                     (= K1 C2)
                     (= K1 0.0)
                     (not (= N 0.0))
                     (= N 1.0)
                     (= G 1.0)
                     (= B 1.0))))
      (a!16 (or (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (= K1 1.0)
                     (not (= K1 2.0))
                     (not (= K1 23.0))
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 23.0))
                     (= K1 5.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (= K1 3.0)
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (= K1 6.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (= K1 13.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (= K1 4.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (= K1 7.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (= K1 8.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (= K1 9.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (= K1 12.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (= K1 10.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (= K1 11.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (= K1 15.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (not (= K1 15.0))
                     (= K1 16.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (not (= K1 15.0))
                     (not (= K1 16.0))
                     (= K1 17.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (not (= K1 15.0))
                     (not (= K1 16.0))
                     (not (= K1 17.0))
                     (= K1 18.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (not (= K1 15.0))
                     (not (= K1 16.0))
                     (not (= K1 17.0))
                     (not (= K1 18.0))
                     (= K1 19.0)
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (not (= K1 15.0))
                     (not (= K1 16.0))
                     (not (= K1 17.0))
                     (not (= K1 18.0))
                     (not (= K1 19.0))
                     (not (= K1 20.0))
                     (= B 0.0))
                (and a!15
                     (= T2 3.0)
                     (= S1 1.0)
                     (= K1 R2)
                     (not (= K1 0.0))
                     (not (= K1 1.0))
                     (not (= K1 2.0))
                     (not (= K1 3.0))
                     (not (= K1 23.0))
                     (not (= K1 5.0))
                     (not (= K1 6.0))
                     (not (= K1 13.0))
                     (not (= K1 4.0))
                     (not (= K1 7.0))
                     (not (= K1 8.0))
                     (not (= K1 9.0))
                     (not (= K1 12.0))
                     (not (= K1 10.0))
                     (not (= K1 11.0))
                     (not (= K1 15.0))
                     (not (= K1 16.0))
                     (not (= K1 17.0))
                     (not (= K1 18.0))
                     (not (= K1 19.0))
                     (= K1 20.0)
                     (= B 0.0))))
      (a!19 (or (and a!18
                     (not (= K2 0.0))
                     (= J2 3.0)
                     (= G2 1.0)
                     (= S1 1.0)
                     (= K1 H2)
                     (not (= K1 0.0))
                     (= K1 23.0)
                     (= L 3221225473.0)
                     (= G 3.0)
                     (= B 0.0))
                (and a!18
                     (= K2 0.0)
                     (= J2 3.0)
                     (= S1 1.0)
                     (= K1 H2)
                     (not (= K1 0.0))
                     (= K1 23.0)
                     (= L 0.0)
                     (= G 3.0)
                     (= B 0.0))
                (and a!18
                     (not (= K2 0.0))
                     (= J2 3.0)
                     (not (= G2 1.0))
                     (= S1 1.0)
                     (= K1 H2)
                     (not (= K1 0.0))
                     (= K1 23.0)
                     (= L 259.0)
                     (= G 3.0)
                     (= B 0.0))))
      (a!21 (or (and a!20
                     (not (= P2 0.0))
                     (= O2 3.0)
                     (= L2 1.0)
                     (= S1 1.0)
                     (= K1 M2)
                     (not (= K1 0.0))
                     (= K1 2.0)
                     (not (= K1 23.0))
                     (= J 3221225473.0)
                     (= G 3.0)
                     (= B 0.0))
                (and a!20
                     (= P2 0.0)
                     (= O2 3.0)
                     (= S1 1.0)
                     (= K1 M2)
                     (not (= K1 0.0))
                     (= K1 2.0)
                     (not (= K1 23.0))
                     (= J 0.0)
                     (= G 3.0)
                     (= B 0.0))
                (and a!20
                     (not (= P2 0.0))
                     (= O2 3.0)
                     (not (= L2 1.0))
                     (= S1 1.0)
                     (= K1 M2)
                     (not (= K1 0.0))
                     (= K1 2.0)
                     (not (= K1 23.0))
                     (= J 259.0)
                     (= G 3.0)
                     (= B 0.0)))))
(let ((a!3 (or (and a!2 (not (= A2 0.0)) (= W1 1.0) (= H1 3221225473.0))
               (and a!2 (= A2 0.0) (= H1 0.0))
               (and a!2 (not (= A2 0.0)) (not (= W1 1.0)) (= H1 259.0))))
      (a!8 (or (and a!7 (not (= V1 0.0)) (= O1 1.0) (= H1 3221225473.0))
               (and a!7 (= V1 0.0) (= H1 0.0))
               (and a!7 (not (= V1 0.0)) (not (= O1 1.0)) (= H1 259.0))))
      (a!14 (or (and a!13 (not (= F2 0.0)) (= B2 1.0) (= H1 3221225473.0))
                (and a!13 (= F2 0.0) (= H1 0.0))
                (and a!13 (not (= F2 0.0)) (not (= B2 1.0)) (= H1 259.0))))
      (a!17 (or (and a!16
                     (not (= U2 0.0))
                     (= Q2 1.0)
                     (= G1 3221225473.0)
                     (= G 3.0))
                (and a!16 (= U2 0.0) (= G1 0.0) (= G 3.0))
                (and a!16
                     (not (= U2 0.0))
                     (not (= Q2 1.0))
                     (= G1 259.0)
                     (= G 3.0)))))
(let ((a!4 (or (and a!3 (= S1 1.0) (= D1 H1) (= G 7.0))
               (and a!3
                    (not (= S1 1.0))
                    (= S1 3.0)
                    (not (= S1 5.0))
                    (= D1 H1)
                    (= G 4.0))
               (and a!3
                    (not (= S1 1.0))
                    (= S1 5.0)
                    (not (= H1 259.0))
                    (= D1 H1)
                    (= G 1.0))
               (and a!3
                    (not (= S1 1.0))
                    (= S1 5.0)
                    (= H1 259.0)
                    (= D1 H1)
                    (= G 6.0))))
      (a!9 (or (and a!8 (= S1 1.0) (= N1 7.0) (= D1 H1))
               (and a!8
                    (not (= S1 1.0))
                    (= S1 3.0)
                    (not (= S1 5.0))
                    (= N1 4.0)
                    (= D1 H1))
               (and a!8
                    (not (= S1 1.0))
                    (= S1 5.0)
                    (= N1 1.0)
                    (not (= H1 259.0))
                    (= D1 H1))
               (and a!8
                    (not (= S1 1.0))
                    (= S1 5.0)
                    (= N1 6.0)
                    (= H1 259.0)
                    (= D1 H1)))))
(let ((a!5 (or (and a!4 (= X 259.0) (= P H1) (= P X) (not (= G 6.0)))
               (and a!4 (= X 259.0) (= P H1) (= P X) (= G 6.0) (not (= B 1.0)))))
      (a!10 (or (and a!9 (not (= N1 6.0)) (= X 259.0) (= P H1) (= P X))
                (and a!9
                     (= N1 6.0)
                     (= X 259.0)
                     (= P H1)
                     (= P X)
                     (not (= B 1.0))))))
(let ((a!11 (or (and a!10 (not (= N1 6.0)) (= G N1))
                (and a!9 (not (= X 259.0)) (= P H1) (= P X) (= G N1))
                (and a!9
                     (= N1 6.0)
                     (= X 259.0)
                     (= P H1)
                     (= P X)
                     (= G 1.0)
                     (= B 1.0)))))
  (or (and (not X2)
           (not W2)
           (not V2)
           F
           (not Y2)
           Z2
           A3
           (not B3)
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= K1 J1)
           (= G1 F1)
           (= I H)
           (= G E)
           (= D C)
           (= B A))
      (and (not X2)
           (not W2)
           (not V2)
           F
           (not Y2)
           Z2
           (not A3)
           B3
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= K1 J1)
           (= G1 F1)
           (= I H)
           (= G E)
           (= D C)
           (= B A))
      (and (not X2)
           (not W2)
           (not V2)
           F
           (not Y2)
           Z2
           (not A3)
           (not B3)
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= K1 J1)
           (= G1 F1)
           (= I H)
           (= G E)
           (= D C)
           (= B A))
      (and (not X2)
           (not W2)
           (not V2)
           F
           (not Y2)
           (not Z2)
           A3
           B3
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= K1 J1)
           (= G1 F1)
           (= I H)
           (= G E)
           (= D C)
           (= B A))
      (and (not X2)
           (not W2)
           (not V2)
           F
           (not Y2)
           (not Z2)
           A3
           (not B3)
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= K1 J1)
           (= G1 F1)
           (= I H)
           (= G E)
           (= D C)
           (= B A))
      (and (not X2)
           (not W2)
           (not V2)
           F
           (not Y2)
           (not Z2)
           (not A3)
           B3
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= K1 J1)
           (= G1 F1)
           (= I H)
           (= G E)
           (= D C)
           (= B A))
      (and (not X2) (not W2) (not V2) F Y2 (not Z2) (not A3) (not B3))
      (and (not X2)
           W2
           V2
           (not F)
           (not Y2)
           (not Z2)
           (not A3)
           (not B3)
           a!5
           (= K J)
           (= M L)
           (= S R)
           (= U T)
           (= W V)
           (= A1 Z)
           (= C1 B1)
           (= M1 L1)
           (= G1 F1)
           (= G 6.0))
      (and X2
           (not W2)
           V2
           (not F)
           (not Y2)
           (not Z2)
           (not A3)
           (not B3)
           a!11
           (= K J)
           (= M L)
           (= S R)
           (= U T)
           (= W V)
           (= A1 Z)
           (= C1 B1)
           (= M1 L1)
           (= G1 F1)
           (not (= G 1.0)))
      (and (not X2)
           (not W2)
           V2
           (not F)
           (not Y2)
           (not Z2)
           (not A3)
           (not B3)
           a!14
           (= K J)
           (= M L)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= M1 L1)
           (= G1 F1)
           (not (= G 1.0))
           (not (= G 3.0))
           (not (= G 5.0)))
      (and (not X2)
           W2
           (not V2)
           (not F)
           (not Y2)
           (not Z2)
           (not A3)
           (not B3)
           a!17
           (= K J)
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (not (= G 1.0))
           (not (= G 3.0))
           (not (= G 5.0)))
      (and X2
           W2
           (not V2)
           (not F)
           (not Y2)
           (not Z2)
           (not A3)
           (not B3)
           a!19
           (= K J)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= G1 F1)
           (not (= G 1.0))
           (not (= G 3.0))
           (not (= G 5.0)))
      (and X2
           (not W2)
           (not V2)
           (not F)
           (not Y2)
           (not Z2)
           (not A3)
           (not B3)
           a!21
           (= M L)
           (= O N)
           (= Q P)
           (= S R)
           (= U T)
           (= W V)
           (= Y X)
           (= A1 Z)
           (= C1 B1)
           (= E1 D1)
           (= I1 H1)
           (= M1 L1)
           (= G1 F1)
           (not (= G 1.0))
           (not (= G 3.0))
           (not (= G 5.0))))))))))
      )
      (state W2 X2 V2 F L J N P R T V X Z B1 D1 H1 L1 G1 K1 I G D B)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Bool) (U Bool) (V Bool) (W Bool) ) 
    (=>
      (and
        (state W V U T F E G H I J K L M N O Q S P R D C B A)
        (and (not V) (not U) (= T true) (not W))
      )
      false
    )
  )
)

(check-sat)
(exit)
