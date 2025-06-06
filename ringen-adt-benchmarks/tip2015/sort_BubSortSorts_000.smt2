(set-logic HORN)

(declare-datatypes ((pair_0 0) (Nat_0 0) (list_0 0) (Bool_0 0)) (((pair_1  (projpair_0 Bool_0) (projpair_1 list_0)))
                                                                 ((Z_2 ) (Z_3  (unS_0 Nat_0)))
                                                                 ((nil_0 ) (cons_0  (head_0 Nat_0) (tail_0 list_0)))
                                                                 ((false_0 ) (true_0 ))))

(declare-fun |gt_0| ( Nat_0 Nat_0 ) Bool)
(declare-fun |bubble_0| ( pair_0 list_0 ) Bool)
(declare-fun |ordered_0| ( Bool_0 list_0 ) Bool)
(declare-fun |bubsort_0| ( list_0 list_0 ) Bool)
(declare-fun |diseqBool_0| ( Bool_0 Bool_0 ) Bool)
(declare-fun |le_0| ( Nat_0 Nat_0 ) Bool)

(assert
  (forall ( (A Nat_0) (v_1 Nat_0) ) 
    (=>
      (and
        (and true (= v_1 Z_2))
      )
      (le_0 v_1 A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (C Nat_0) (D Nat_0) ) 
    (=>
      (and
        (le_0 C D)
        (and (= B (Z_3 C)) (= A (Z_3 D)))
      )
      (le_0 B A)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (v_2 Nat_0) ) 
    (=>
      (and
        (and (= A (Z_3 B)) (= v_2 Z_2))
      )
      (gt_0 A v_2)
    )
  )
)
(assert
  (forall ( (A Nat_0) (B Nat_0) (C Nat_0) (D Nat_0) ) 
    (=>
      (and
        (gt_0 C D)
        (and (= B (Z_3 C)) (= A (Z_3 D)))
      )
      (gt_0 B A)
    )
  )
)
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
  (forall ( (A list_0) (B list_0) (C Bool_0) (D Nat_0) (E list_0) (F Nat_0) ) 
    (=>
      (and
        (ordered_0 C A)
        (le_0 F D)
        (and (= B (cons_0 F (cons_0 D E))) (= A (cons_0 D E)))
      )
      (ordered_0 C B)
    )
  )
)
(assert
  (forall ( (A list_0) (B Nat_0) (C list_0) (D Nat_0) (v_4 Bool_0) ) 
    (=>
      (and
        (gt_0 D B)
        (and (= A (cons_0 D (cons_0 B C))) (= v_4 false_0))
      )
      (ordered_0 v_4 A)
    )
  )
)
(assert
  (forall ( (A list_0) (B Nat_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and (= A (cons_0 B nil_0)) (= v_2 true_0))
      )
      (ordered_0 v_2 A)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 list_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 nil_0))
      )
      (ordered_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A list_0) (B pair_0) (C list_0) (D pair_0) (E Bool_0) (F list_0) (G Nat_0) (H list_0) (I Nat_0) ) 
    (=>
      (and
        (bubble_0 B A)
        (le_0 I G)
        (and (= D (pair_1 E (cons_0 I F)))
     (= A (cons_0 G H))
     (= C (cons_0 I (cons_0 G H)))
     (= B (pair_1 E F)))
      )
      (bubble_0 D C)
    )
  )
)
(assert
  (forall ( (A list_0) (B pair_0) (C list_0) (D pair_0) (E Bool_0) (F list_0) (G Nat_0) (H list_0) (I Nat_0) ) 
    (=>
      (and
        (bubble_0 B A)
        (gt_0 I G)
        (and (= D (pair_1 true_0 (cons_0 G F)))
     (= A (cons_0 I H))
     (= C (cons_0 I (cons_0 G H)))
     (= B (pair_1 E F)))
      )
      (bubble_0 D C)
    )
  )
)
(assert
  (forall ( (A list_0) (B pair_0) (C Nat_0) ) 
    (=>
      (and
        (and (= A (cons_0 C nil_0)) (= B (pair_1 false_0 (cons_0 C nil_0))))
      )
      (bubble_0 B A)
    )
  )
)
(assert
  (forall ( (v_0 pair_0) (v_1 list_0) ) 
    (=>
      (and
        (and true (= v_0 (pair_1 false_0 nil_0)) (= v_1 nil_0))
      )
      (bubble_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A pair_0) (B list_0) (C list_0) (D list_0) ) 
    (=>
      (and
        (bubble_0 A D)
        (bubsort_0 B C)
        (= A (pair_1 true_0 C))
      )
      (bubsort_0 B D)
    )
  )
)
(assert
  (forall ( (A pair_0) (B list_0) (C Bool_0) (D list_0) (v_4 Bool_0) (v_5 list_0) ) 
    (=>
      (and
        (bubble_0 A B)
        (diseqBool_0 C v_4)
        (and (= v_4 true_0) (= A (pair_1 C D)) (= v_5 B))
      )
      (bubsort_0 B v_5)
    )
  )
)
(assert
  (forall ( (A list_0) (B Bool_0) (C list_0) (v_3 Bool_0) ) 
    (=>
      (and
        (diseqBool_0 B v_3)
        (ordered_0 B A)
        (bubsort_0 A C)
        (= v_3 true_0)
      )
      false
    )
  )
)

(check-sat)
(exit)
