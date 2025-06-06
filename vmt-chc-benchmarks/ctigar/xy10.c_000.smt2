(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Int Int Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Bool) ) 
    (=>
      (and
        (and (not B) (not G) (not F) (= A true))
      )
      (state B A G F C D E)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) ) 
    (=>
      (and
        (state B A O N H J L)
        (let ((a!1 (and (<= H L) (<= 1 (+ J (* (- 1) L)))))
      (a!2 (and (not F)
                E
                (not D)
                (not C)
                (= J I)
                (= L K)
                (= (+ H (* (- 1) G)) (- 10))))
      (a!3 (and (not F) E (not D) C (= H G) (= L K) (= (+ J (* (- 1) I)) (- 1))))
      (a!4 (and F (not E) (not D) C (= H G) (= J I) (= L K)))
      (a!5 (and (not F) (not E) (not D) (not C) (= H G) (= J I) (= L K)))
      (a!6 (not (<= 1 (+ J (* (- 1) L))))))
  (and (or A
           N
           O
           (not B)
           (= M 0)
           (and (not F) E D (not C) (= H G) (= J I) (= L K)))
       (or A
           N
           O
           (not B)
           (not (= M 0))
           (and (not F) (not E) D C (= H G) (= J I) (= L K)))
       (or A N (not O) (not B) a!1 (and (not F) E D C (= H G) (= J I) (= L K)))
       (or N O (not B) (not A) a!2)
       (or A B N (not O) a!3)
       (or B O (not N) (not A) a!4)
       (or N
           (not O)
           (not B)
           (not A)
           (and F (not E) (not D) (not C) (= H G) (= J I) (= L K)))
       (or B
           N
           (not O)
           (not A)
           (and (not F) (not E) D (not C) (= H G) (= J I) (= L K)))
       (or A B N O a!5)
       (or A B O (not N) a!5)
       (or B
           N
           O
           (not A)
           (and (not F) (not E) D (not C) (= I 0) (= G 0) (= L K)))
       (or A N (not O) (not B) (not (<= H L)) a!6 a!4)))
      )
      (state D C E F G I K)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Bool) ) 
    (=>
      (and
        (state B A G F C D E)
        (and (not B) (not G) (= F true) (= A true))
      )
      false
    )
  )
)

(check-sat)
(exit)
