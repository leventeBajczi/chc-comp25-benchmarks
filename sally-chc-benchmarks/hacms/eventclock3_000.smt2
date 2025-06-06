(set-logic HORN)


(declare-fun |invariant| ( Real Bool Real Bool Real Real Real Real Real Real Real Real Bool Real ) Bool)

(assert
  (forall ( (A Real) (B Bool) (C Real) (D Bool) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Bool) (N Real) ) 
    (=>
      (and
        (and (= L (- 1.0))
     (= K (- 1.0))
     (= H 0.0)
     (= G 0.0)
     (= F 0.0)
     (= C 0.0)
     (= A 0.0)
     (not (<= 20.0 J))
     (not (<= 20.0 I))
     (<= 0.0 J)
     (<= 0.0 I)
     (or (= F 0.0) (= F 1.0) (= F 2.0))
     (or (= E 0.0) (= E 1.0) (= E 2.0))
     (or (= C 0.0) (= C 1.0) (= C 2.0))
     (or (= G 0.0) (= G 1.0))
     (not D)
     (not B)
     (= N 0.0))
      )
      (invariant A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Bool) (D Bool) (E Real) (F Real) (G Bool) (H Bool) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Bool) (Z Bool) (A1 Real) (B1 Real) ) 
    (=>
      (and
        (invariant A C E G I K M O Q S U W Y A1)
        (let ((a!1 (and (or C (not Y) (not (= I 1.0)) (not (= U (- 1.0))))
                (= V U)
                (= D C)))
      (a!2 (or (and (= B 0.0) (= F 1.0) (= I 1.0) (= K 0.0) (= L 1.0))
               (and (= B 0.0) (= F 0.0) (not (= I 1.0)) (= K 0.0) (= L 0.0))
               (and (not G)
                    (not (<= 1.0 A))
                    (= B (+ 1.0 A))
                    (= F 1.0)
                    (= K 1.0)
                    (= L 1.0))
               (and (not G) (<= 1.0 A) (= B 0.0) (= F 2.0) (= K 1.0) (= L 0.0))
               (and G (= B 0.0) (= F 0.0) (= K 1.0) (= L 2.0))
               (and (= B 0.0) (= F 2.0) (= I 2.0) (= K 2.0) (= L 0.0))
               (and (= B 0.0) (= F 0.0) (not (= I 2.0)) (= K 2.0) (= L 2.0))))
      (a!4 (and (or (not C) (<= A1 0.0) (not (= W (- 1.0)))) (= X W)))
      (a!6 (or (and H
                    (not (<= B1 0.0))
                    (not (<= 5.0 B1))
                    (= E 1.0)
                    (= M 0.0)
                    (= N 1.0))
               (and (not H) (= B1 0.0) (not (= E 1.0)) (= M 0.0) (= N 0.0))
               (and (not H) (= B1 0.0) (= E 2.0) (= M 1.0) (= N 0.0))
               (and H
                    (not (<= B1 0.0))
                    (not (<= 5.0 B1))
                    (not (= E 2.0))
                    (= M 1.0)
                    (= N 1.0)))))
(let ((a!3 (and (or a!1
                    (and (not C) D Y (not Z) (= U (- 1.0)) (= V O) (= I 1.0)))
                a!2
                (<= O (+ (- 20.0) R))
                (<= R (+ 20.0 O))
                (= O Q)
                (= T S)
                (= X W)
                (= B1 A1)
                (= N M)
                (= H G)))
      (a!5 (or a!4 (and C (not (<= A1 0.0)) (= W (- 1.0)) (= X O)))))
(let ((a!7 (or a!3
               (and a!5
                    a!6
                    (<= O (+ (- 20.0) T))
                    (<= T (+ 20.0 O))
                    (= O S)
                    (= V U)
                    (= B A)
                    (= F E)
                    (= L K)
                    (= R Q)
                    (= D C)
                    (= Z Y)))))
(let ((a!8 (or (and a!7 (= P O))
               (and (or (= P Q) (= P S))
                    (not (<= Q O))
                    (not (<= S O))
                    (<= P Q)
                    (<= P S)
                    (= T S)
                    (= V U)
                    (= X W)
                    (= B1 A1)
                    (= B A)
                    (= F E)
                    (= L K)
                    (= N M)
                    (= R Q)
                    (= D C)
                    (= H G)
                    (= Z Y)))))
  (and (or (= K 0.0) (= K 1.0) (= K 2.0))
       (or (= J 0.0) (= J 1.0) (= J 2.0))
       (or (= I 0.0) (= I 1.0) (= I 2.0))
       (or (= F 0.0) (= F 1.0) (= F 2.0))
       (or (= E 0.0) (= E 1.0) (= E 2.0))
       (or (= N 0.0) (= N 1.0))
       (or (= M 0.0) (= M 1.0))
       a!8
       (or (= L 0.0) (= L 1.0) (= L 2.0)))))))
      )
      (invariant B D F H J L N P R T V X Z B1)
    )
  )
)
(assert
  (forall ( (A Real) (B Bool) (C Real) (D Bool) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Bool) (N Real) ) 
    (=>
      (and
        (invariant A B C D E F G H I J K L M N)
        (<= K (+ (- 41.0) L))
      )
      false
    )
  )
)

(check-sat)
(exit)
