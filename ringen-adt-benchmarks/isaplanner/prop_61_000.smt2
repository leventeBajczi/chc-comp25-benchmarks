(set-logic HORN)

(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0  (projS_0 Nat_0)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0  (head_0 Nat_0) (tail_0 list_0)))))

(declare-fun |diseqNat_0| ( Nat_0 Nat_0 ) Bool)
(declare-fun |lastOfTwo_0| ( Nat_0 list_0 list_0 ) Bool)
(declare-fun |x_5| ( list_0 list_0 list_0 ) Bool)
(declare-fun |last_0| ( Nat_0 list_0 ) Bool)

(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Nat_0) ) 
    (=>
      (and
        (and (= A (S_0 B)) (= v_2 Z_0))
      )
      (diseqNat_0 v_2 A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Nat_0) ) 
    (=>
      (and
        (and (= A (S_0 B)) (= v_2 Z_0))
      )
      (diseqNat_0 A v_2)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (C Nat_0) (D Nat_0) ) 
    (=>
      (and
        (diseqNat_0 C D)
        (and (= A (S_0 D)) (= B (S_0 C)))
      )
      (diseqNat_0 B A)
    )
  )
)
(assert
  (forall ( (A list_0) (B list_0) (C Nat_0) (D Nat_0) (E list_0) (F Nat_0) ) 
    (=>
      (and
        (last_0 C A)
        (and (= B (cons_0 F (cons_0 D E))) (= A (cons_0 D E)))
      )
      (last_0 C B)
    )
  )
)
(assert
  (forall ( (A list_0) (B Nat_0) ) 
    (=>
      (and
        (= A (cons_0 B nil_0))
      )
      (last_0 B A)
    )
  )
)
(assert
  (forall ( (v_0 Nat_0) (v_1 list_0) ) 
    (=>
      (and
        (and true (= v_0 Z_0) (= v_1 nil_0))
      )
      (last_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A list_0) (B list_0) (C Nat_0) (D Nat_0) (E list_0) (F list_0) ) 
    (=>
      (and
        (last_0 C A)
        (and (= B (cons_0 D E)) (= A (cons_0 D E)))
      )
      (lastOfTwo_0 C F B)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B list_0) (v_2 list_0) ) 
    (=>
      (and
        (last_0 A B)
        (= v_2 nil_0)
      )
      (lastOfTwo_0 A B v_2)
    )
  )
)
(assert
  (forall ( (A list_0) (B list_0) (C list_0) (D Nat_0) (E list_0) (F list_0) ) 
    (=>
      (and
        (x_5 C E F)
        (and (= B (cons_0 D C)) (= A (cons_0 D E)))
      )
      (x_5 B A F)
    )
  )
)
(assert
  (forall ( (A list_0) (v_1 list_0) (v_2 list_0) ) 
    (=>
      (and
        (and true (= v_1 nil_0) (= v_2 A))
      )
      (x_5 A v_1 v_2)
    )
  )
)
(assert
  (forall ( (A list_0) (B Nat_0) (C Nat_0) (D list_0) (E list_0) ) 
    (=>
      (and
        (x_5 A D E)
        (lastOfTwo_0 C D E)
        (last_0 B A)
        (diseqNat_0 B C)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
