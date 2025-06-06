(set-logic HORN)

(declare-datatypes ((Bool_0 0)) (((false_0 ) (true_0 ))))
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0  (p_0 Nat_0)))))

(declare-fun |diseqNat_0| ( Nat_0 Nat_0 ) Bool)
(declare-fun |diseqBool_0| ( Bool_0 Bool_0 ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |leq_0| ( Bool_0 Nat_0 Nat_0 ) Bool)

(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 true_0))
      )
      (diseqBool_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 false_0))
      )
      (diseqBool_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Nat_0) ) 
    (=>
      (and
        (and (= A (succ_0 B)) (= v_2 zero_0))
      )
      (diseqNat_0 v_2 A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Nat_0) ) 
    (=>
      (and
        (and (= A (succ_0 B)) (= v_2 zero_0))
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
        (and (= B (succ_0 C)) (= A (succ_0 D)))
      )
      (diseqNat_0 B A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (C Bool_0) (D Nat_0) (E Nat_0) ) 
    (=>
      (and
        (leq_0 C E D)
        (and (= B (succ_0 E)) (= A (succ_0 D)))
      )
      (leq_0 C B A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Bool_0) (v_3 Nat_0) ) 
    (=>
      (and
        (and (= A (succ_0 B)) (= v_2 false_0) (= v_3 zero_0))
      )
      (leq_0 v_2 A v_3)
    )
  )
)
(assert
  (forall ( (A Nat_0) (v_1 Bool_0) (v_2 Nat_0) ) 
    (=>
      (and
        (and true (= v_1 true_0) (= v_2 zero_0))
      )
      (leq_0 v_1 v_2 A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Bool_0) (v_3 Bool_0) ) 
    (=>
      (and
        (diseqNat_0 A B)
        (leq_0 v_2 A B)
        (leq_0 v_3 B A)
        (and (= v_2 true_0) (= v_3 true_0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Bool_0) (B Nat_0) (C Nat_0) (v_3 Bool_0) (v_4 Bool_0) (v_5 Nat_0) ) 
    (=>
      (and
        (diseqBool_0 A v_3)
        (leq_0 A B C)
        (leq_0 v_4 C B)
        (diseqNat_0 C v_5)
        (and (= v_3 true_0) (= v_4 true_0) (= v_5 C))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Bool_0) (B Nat_0) (C Nat_0) (v_3 Bool_0) (v_4 Bool_0) (v_5 Nat_0) ) 
    (=>
      (and
        (diseqBool_0 A v_3)
        (leq_0 v_4 B C)
        (leq_0 A C B)
        (diseqNat_0 B v_5)
        (and (= v_3 true_0) (= v_4 true_0) (= v_5 B))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Bool_0) (B Bool_0) (C Nat_0) (D Nat_0) (v_4 Bool_0) (v_5 Bool_0) ) 
    (=>
      (and
        (diseqBool_0 A v_4)
        (leq_0 B C D)
        (leq_0 A D C)
        (diseqNat_0 D C)
        (diseqBool_0 B v_5)
        (and (= v_4 true_0) (= v_5 true_0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
