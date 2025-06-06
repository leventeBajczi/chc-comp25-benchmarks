(set-logic HORN)


(declare-fun |state| ( Int Bool Int Bool Int Int Int Int Int Bool ) Bool)

(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (let ((a!1 (= (or (and (<= I 1) (<= (- 1) I)) B) D))
      (a!2 (= (or (not D) (and (<= E 20) (<= 0 E))) C))
      (a!3 (or (<= I 0) (<= 10 H) (= (+ I H (* (- 1) G)) 0)))
      (a!4 (or (= H G) (and (not (<= I 0)) (not (<= 10 H)))))
      (a!5 (or (and (<= H 0) (<= 0 I)) (= (+ I H (* (- 1) J)) 0))))
  (and (= F E)
       (= A 0)
       (= A H)
       a!1
       a!2
       a!3
       (or (not (<= 0 I)) (not (<= H 0)) (= J G))
       a!4
       a!5
       (= B true)
       (= J F)))
      )
      (state A B I D H J F G E C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Bool) (F Bool) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (state A B S N R T P Q O M)
        (let ((a!1 (= (or (not N) (and (<= O 20) (<= 0 O))) M))
      (a!2 (= (or D (and (<= K 1) (<= (- 1) K))) F))
      (a!3 (= (or (not F) (and (<= G 20) (<= 0 G))) E))
      (a!4 (= (or B (and (<= S 1) (<= (- 1) S))) N))
      (a!5 (or (<= S 0) (<= 10 R) (= (+ S R (* (- 1) Q)) 0)))
      (a!6 (or (<= K 0) (<= 10 J) (= (+ K J (* (- 1) I)) 0)))
      (a!7 (or (= R Q) (and (not (<= S 0)) (not (<= 10 R)))))
      (a!8 (or (and (<= R 0) (<= 0 S)) (= (+ S R (* (- 1) T)) 0)))
      (a!9 (or (and (<= J 0) (<= 0 K)) (= (+ K J (* (- 1) L)) 0)))
      (a!10 (or (= J I) (and (not (<= K 0)) (not (<= 10 J))))))
  (and (= P O)
       (= P C)
       (= H G)
       (= H L)
       (= J C)
       (= A R)
       a!1
       a!2
       a!3
       a!4
       (= N D)
       a!5
       (or (not (<= 0 S)) (not (<= R 0)) (= T Q))
       (or (not (<= 0 K)) (not (<= J 0)) (= L I))
       a!6
       a!7
       a!8
       a!9
       a!10
       (= T P)))
      )
      (state C D K F J L H I G E)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (state A B I D H J F G E C)
        (not C)
      )
      false
    )
  )
)

(check-sat)
(exit)
