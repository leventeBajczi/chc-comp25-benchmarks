(set-logic HORN)

(declare-datatypes ((Tok_0 0) (list_0 0)) (((C_0 ) (D_0 ) (X_0 ) (Y_0 ) (Pl_0 ))
                                           ((nil_0 ) (cons_0  (head_0 Tok_0) (tail_0 list_0)))))
(declare-datatypes ((E_0 0)) (((Plus_0  (projPlus_0 E_0) (projPlus_1 E_0)) (EX_0 ) (EY_0 ))))

(declare-fun |lin_0| ( list_0 E_0 ) Bool)
(declare-fun |x_1| ( list_0 list_0 list_0 ) Bool)
(declare-fun |diseqE_0| ( E_0 E_0 ) Bool)

(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (Plus_0 B C)) (= v_3 EX_0))
      )
      (diseqE_0 A v_3)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (Plus_0 B C)) (= v_3 EY_0))
      )
      (diseqE_0 A v_3)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (Plus_0 B C)) (= v_3 EX_0))
      )
      (diseqE_0 v_3 A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (v_3 E_0) ) 
    (=>
      (and
        (and (= A (Plus_0 B C)) (= v_3 EY_0))
      )
      (diseqE_0 v_3 A)
    )
  )
)
(assert
  (forall ( (v_0 E_0) (v_1 E_0) ) 
    (=>
      (and
        (and true (= v_0 EX_0) (= v_1 EY_0))
      )
      (diseqE_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 E_0) (v_1 E_0) ) 
    (=>
      (and
        (and true (= v_0 EY_0) (= v_1 EX_0))
      )
      (diseqE_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (diseqE_0 C E)
        (and (= B (Plus_0 C D)) (= A (Plus_0 E F)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A E_0) (B E_0) (C E_0) (D E_0) (E E_0) (F E_0) ) 
    (=>
      (and
        (diseqE_0 D F)
        (and (= B (Plus_0 C D)) (= A (Plus_0 E F)))
      )
      (diseqE_0 B A)
    )
  )
)
(assert
  (forall ( (A list_0) (B list_0) (C list_0) (D Tok_0) (E list_0) (F list_0) ) 
    (=>
      (and
        (x_1 C E F)
        (and (= A (cons_0 D E)) (= B (cons_0 D C)))
      )
      (x_1 B A F)
    )
  )
)
(assert
  (forall ( (A list_0) (v_1 list_0) (v_2 list_0) ) 
    (=>
      (and
        (and true (= v_1 nil_0) (= v_2 A))
      )
      (x_1 A v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 list_0) (v_1 E_0) ) 
    (=>
      (and
        (and true (= v_0 (cons_0 Y_0 nil_0)) (= v_1 EY_0))
      )
      (lin_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 list_0) (v_1 E_0) ) 
    (=>
      (and
        (and true (= v_0 (cons_0 X_0 nil_0)) (= v_1 EX_0))
      )
      (lin_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A E_0) (B list_0) (C list_0) (D list_0) (E list_0) (F list_0) (G list_0) (H E_0) (I E_0) (v_9 list_0) (v_10 list_0) (v_11 list_0) ) 
    (=>
      (and
        (x_1 G v_9 F)
        (lin_0 B H)
        (lin_0 C I)
        (x_1 D C v_10)
        (x_1 E v_11 D)
        (x_1 F B E)
        (let ((a!1 (= v_11 (cons_0 D_0 (cons_0 Pl_0 (cons_0 C_0 nil_0))))))
  (and (= v_9 (cons_0 C_0 nil_0))
       (= v_10 (cons_0 D_0 nil_0))
       a!1
       (= A (Plus_0 H I))))
      )
      (lin_0 G A)
    )
  )
)
(assert
  (forall ( (A list_0) (B E_0) (C E_0) ) 
    (=>
      (and
        (diseqE_0 B C)
        (lin_0 A C)
        (lin_0 A B)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
