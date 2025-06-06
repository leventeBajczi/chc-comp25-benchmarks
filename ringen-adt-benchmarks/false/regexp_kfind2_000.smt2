(set-logic HORN)

(declare-datatypes ((T_0 0) (pair_0 0) (list_1 0)) (((A_0 ) (B_0 ) (C_0 ))
                                                    ((pair_1  (projpair_0 list_1) (projpair_1 list_1)))
                                                    ((nil_1 ) (cons_1  (head_1 T_0) (tail_1 list_1)))))
(declare-datatypes ((Bool_0 0)) (((false_0 ) (true_0 ))))
(declare-datatypes ((list_2 0)) (((nil_2 ) (cons_2  (head_2 pair_0) (tail_2 list_2)))))
(declare-datatypes ((R_0 0)) (((Nil_3 ) (Eps_0 ) (Atom_0  (projAtom_0 T_0)) (x_0  (proj_0 R_0) (proj_1 R_0)) (x_1  (proj_2 R_0) (proj_3 R_0)) (Star_0  (projStar_0 R_0)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0  (head_0 Bool_0) (tail_0 list_0)))))

(declare-fun |splits_1| ( list_2 list_1 ) Bool)
(declare-fun |and_0| ( Bool_0 Bool_0 Bool_0 ) Bool)
(declare-fun |reck_0| ( Bool_0 R_0 list_1 ) Bool)
(declare-fun |step_0| ( R_0 R_0 T_0 ) Bool)
(declare-fun |rec_0| ( Bool_0 R_0 list_1 ) Bool)
(declare-fun |diseqBool_0| ( Bool_0 Bool_0 ) Bool)
(declare-fun |splits_0| ( list_2 T_0 list_2 ) Bool)
(declare-fun |eps_1| ( Bool_0 R_0 ) Bool)
(declare-fun |reck_1| ( list_0 R_0 R_0 list_2 ) Bool)
(declare-fun |diseqT_0| ( T_0 T_0 ) Bool)
(declare-fun |or_0| ( Bool_0 list_0 ) Bool)
(declare-fun |or_1| ( Bool_0 Bool_0 Bool_0 ) Bool)

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
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 false_0) (= v_2 false_0))
      )
      (and_0 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 true_0) (= v_2 false_0))
      )
      (and_0 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 false_0) (= v_2 true_0))
      )
      (and_0 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 true_0) (= v_2 true_0))
      )
      (and_0 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 false_0) (= v_2 false_0))
      )
      (or_1 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 true_0) (= v_2 false_0))
      )
      (or_1 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 false_0) (= v_2 true_0))
      )
      (or_1 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 Bool_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 true_0) (= v_2 true_0))
      )
      (or_1 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (v_0 T_0) (v_1 T_0) ) 
    (=>
      (and
        (and true (= v_0 A_0) (= v_1 B_0))
      )
      (diseqT_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 T_0) (v_1 T_0) ) 
    (=>
      (and
        (and true (= v_0 A_0) (= v_1 C_0))
      )
      (diseqT_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 T_0) (v_1 T_0) ) 
    (=>
      (and
        (and true (= v_0 B_0) (= v_1 A_0))
      )
      (diseqT_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 T_0) (v_1 T_0) ) 
    (=>
      (and
        (and true (= v_0 C_0) (= v_1 A_0))
      )
      (diseqT_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 T_0) (v_1 T_0) ) 
    (=>
      (and
        (and true (= v_0 B_0) (= v_1 C_0))
      )
      (diseqT_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 T_0) (v_1 T_0) ) 
    (=>
      (and
        (and true (= v_0 C_0) (= v_1 B_0))
      )
      (diseqT_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A list_2) (B list_2) (C list_2) (D list_1) (E list_1) (F list_2) (G T_0) ) 
    (=>
      (and
        (splits_0 C G F)
        (let ((a!1 (= B (cons_2 (pair_1 (cons_1 G D) E) C))))
  (and a!1 (= A (cons_2 (pair_1 D E) F))))
      )
      (splits_0 B G A)
    )
  )
)
(assert
  (forall ( (A T_0) (v_1 list_2) (v_2 list_2) ) 
    (=>
      (and
        (and true (= v_1 nil_2) (= v_2 nil_2))
      )
      (splits_0 v_1 A v_2)
    )
  )
)
(assert
  (forall ( (A list_1) (B list_2) (C list_2) (D list_2) (E T_0) (F list_1) ) 
    (=>
      (and
        (splits_0 D E C)
        (splits_1 C F)
        (let ((a!1 (= B (cons_2 (pair_1 nil_1 (cons_1 E F)) D))))
  (and a!1 (= A (cons_1 E F))))
      )
      (splits_1 B A)
    )
  )
)
(assert
  (forall ( (v_0 list_2) (v_1 list_1) ) 
    (=>
      (and
        (and true (= v_0 (cons_2 (pair_1 nil_1 nil_1) nil_2)) (= v_1 nil_1))
      )
      (splits_1 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A list_0) (B Bool_0) (C Bool_0) (D Bool_0) (E list_0) ) 
    (=>
      (and
        (or_1 B D C)
        (or_0 C E)
        (= A (cons_0 D E))
      )
      (or_0 B A)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 list_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 nil_0))
      )
      (or_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and (= A (Star_0 B)) (= v_2 true_0))
      )
      (eps_1 v_2 A)
    )
  )
)
(assert
  (forall ( (A R_0) (B Bool_0) (C Bool_0) (D Bool_0) (E R_0) (F R_0) ) 
    (=>
      (and
        (and_0 B C D)
        (eps_1 C E)
        (eps_1 D F)
        (= A (x_1 E F))
      )
      (eps_1 B A)
    )
  )
)
(assert
  (forall ( (A R_0) (B Bool_0) (C Bool_0) (D Bool_0) (E R_0) (F R_0) ) 
    (=>
      (and
        (or_1 B C D)
        (eps_1 C E)
        (eps_1 D F)
        (= A (x_0 E F))
      )
      (eps_1 B A)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 R_0) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 Eps_0))
      )
      (eps_1 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A R_0) (B T_0) (v_2 Bool_0) ) 
    (=>
      (and
        (and (= A (Atom_0 B)) (= v_2 false_0))
      )
      (eps_1 v_2 A)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 R_0) ) 
    (=>
      (and
        (and true (= v_0 false_0) (= v_1 Nil_3))
      )
      (eps_1 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (C R_0) (D R_0) (E T_0) ) 
    (=>
      (and
        (step_0 C D E)
        (and (= A (Star_0 D)) (= B (x_1 C (Star_0 D))))
      )
      (step_0 B A E)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (C R_0) (D R_0) (E R_0) (F R_0) (G T_0) (v_7 Bool_0) ) 
    (=>
      (and
        (eps_1 v_7 E)
        (step_0 C E G)
        (step_0 D F G)
        (and (= v_7 true_0) (= B (x_0 (x_1 C F) D)) (= A (x_1 E F)))
      )
      (step_0 B A G)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (C R_0) (D Bool_0) (E R_0) (F R_0) (G T_0) (v_7 Bool_0) ) 
    (=>
      (and
        (eps_1 D E)
        (diseqBool_0 D v_7)
        (step_0 C E G)
        (and (= v_7 true_0) (= B (x_0 (x_1 C F) Nil_3)) (= A (x_1 E F)))
      )
      (step_0 B A G)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (C R_0) (D R_0) (E R_0) (F R_0) (G T_0) ) 
    (=>
      (and
        (step_0 D F G)
        (step_0 C E G)
        (and (= B (x_0 C D)) (= A (x_0 E F)))
      )
      (step_0 B A G)
    )
  )
)
(assert
  (forall ( (A R_0) (B T_0) (v_2 R_0) ) 
    (=>
      (and
        (and (= A (Atom_0 B)) (= v_2 Eps_0))
      )
      (step_0 v_2 A B)
    )
  )
)
(assert
  (forall ( (A R_0) (B T_0) (C T_0) (v_3 R_0) ) 
    (=>
      (and
        (diseqT_0 B C)
        (and (= A (Atom_0 B)) (= v_3 Nil_3))
      )
      (step_0 v_3 A C)
    )
  )
)
(assert
  (forall ( (A T_0) (v_1 R_0) (v_2 R_0) ) 
    (=>
      (and
        (and true (= v_1 Nil_3) (= v_2 Eps_0))
      )
      (step_0 v_1 v_2 A)
    )
  )
)
(assert
  (forall ( (A T_0) (v_1 R_0) (v_2 R_0) ) 
    (=>
      (and
        (and true (= v_1 Nil_3) (= v_2 Nil_3))
      )
      (step_0 v_1 v_2 A)
    )
  )
)
(assert
  (forall ( (A list_1) (B Bool_0) (C R_0) (D T_0) (E list_1) (F R_0) ) 
    (=>
      (and
        (rec_0 B C E)
        (step_0 C F D)
        (= A (cons_1 D E))
      )
      (rec_0 B F A)
    )
  )
)
(assert
  (forall ( (A Bool_0) (B R_0) (v_2 list_1) ) 
    (=>
      (and
        (eps_1 A B)
        (= v_2 nil_1)
      )
      (rec_0 A B v_2)
    )
  )
)
(assert
  (forall ( (A list_1) (B R_0) (C list_1) (D R_0) (E Bool_0) (F Bool_0) (G T_0) (H list_1) (I R_0) (v_9 Bool_0) ) 
    (=>
      (and
        (eps_1 F I)
        (diseqBool_0 F v_9)
        (rec_0 E B A)
        (and (= v_9 true_0)
     (= D (Star_0 I))
     (= A (cons_1 G H))
     (= C (cons_1 G H))
     (= B (x_1 I (Star_0 I))))
      )
      (reck_0 E D C)
    )
  )
)
(assert
  (forall ( (A list_1) (B R_0) (C T_0) (D list_1) (E R_0) (v_5 Bool_0) (v_6 Bool_0) ) 
    (=>
      (and
        (eps_1 v_5 E)
        (and (= v_5 true_0) (= A (cons_1 C D)) (= B (Star_0 E)) (= v_6 false_0))
      )
      (reck_0 v_6 B A)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (v_2 Bool_0) (v_3 list_1) ) 
    (=>
      (and
        (and (= A (Star_0 B)) (= v_2 true_0) (= v_3 nil_1))
      )
      (reck_0 v_2 A v_3)
    )
  )
)
(assert
  (forall ( (A R_0) (B Bool_0) (C list_2) (D list_0) (E R_0) (F R_0) (G list_1) ) 
    (=>
      (and
        (or_0 B D)
        (splits_1 C G)
        (reck_1 D E F C)
        (= A (x_1 E F))
      )
      (reck_0 B A G)
    )
  )
)
(assert
  (forall ( (A R_0) (B Bool_0) (C Bool_0) (D Bool_0) (E R_0) (F R_0) (G list_1) ) 
    (=>
      (and
        (or_1 B C D)
        (reck_0 C E G)
        (reck_0 D F G)
        (= A (x_0 E F))
      )
      (reck_0 B A G)
    )
  )
)
(assert
  (forall ( (A list_1) (B R_0) (C T_0) (D list_1) (E T_0) (F T_0) (v_6 Bool_0) ) 
    (=>
      (and
        (and (= A (cons_1 E (cons_1 C D))) (= B (Atom_0 F)) (= v_6 false_0))
      )
      (reck_0 v_6 B A)
    )
  )
)
(assert
  (forall ( (A list_1) (B R_0) (C T_0) (v_3 Bool_0) ) 
    (=>
      (and
        (and (= A (cons_1 C nil_1)) (= B (Atom_0 C)) (= v_3 true_0))
      )
      (reck_0 v_3 B A)
    )
  )
)
(assert
  (forall ( (A list_1) (B R_0) (C T_0) (D T_0) (v_4 Bool_0) ) 
    (=>
      (and
        (diseqT_0 D C)
        (and (= A (cons_1 C nil_1)) (= B (Atom_0 D)) (= v_4 false_0))
      )
      (reck_0 v_4 B A)
    )
  )
)
(assert
  (forall ( (A R_0) (B T_0) (v_2 Bool_0) (v_3 list_1) ) 
    (=>
      (and
        (and (= A (Atom_0 B)) (= v_2 false_0) (= v_3 nil_1))
      )
      (reck_0 v_2 A v_3)
    )
  )
)
(assert
  (forall ( (A list_1) (B T_0) (C list_1) (v_3 Bool_0) (v_4 R_0) ) 
    (=>
      (and
        (and (= A (cons_1 B C)) (= v_3 false_0) (= v_4 Eps_0))
      )
      (reck_0 v_3 v_4 A)
    )
  )
)
(assert
  (forall ( (v_0 Bool_0) (v_1 R_0) (v_2 list_1) ) 
    (=>
      (and
        (and true (= v_0 true_0) (= v_1 Eps_0) (= v_2 nil_1))
      )
      (reck_0 v_0 v_1 v_2)
    )
  )
)
(assert
  (forall ( (A list_1) (v_1 Bool_0) (v_2 R_0) ) 
    (=>
      (and
        (and true (= v_1 false_0) (= v_2 Nil_3))
      )
      (reck_0 v_1 v_2 A)
    )
  )
)
(assert
  (forall ( (A list_2) (B list_0) (C Bool_0) (D Bool_0) (E Bool_0) (F list_0) (G list_1) (H list_1) (I list_2) (J R_0) (K R_0) ) 
    (=>
      (and
        (and_0 C D E)
        (reck_0 D J G)
        (rec_0 E K H)
        (reck_1 F J K I)
        (and (= A (cons_2 (pair_1 G H) I)) (= B (cons_0 C F)))
      )
      (reck_1 B J K A)
    )
  )
)
(assert
  (forall ( (A R_0) (B R_0) (v_2 list_0) (v_3 list_2) ) 
    (=>
      (and
        (and true (= v_2 nil_0) (= v_3 nil_2))
      )
      (reck_1 v_2 A B v_3)
    )
  )
)
(assert
  (forall ( (A R_0) (v_1 Bool_0) (v_2 list_1) ) 
    (=>
      (and
        (reck_0 v_1 A v_2)
        (let ((a!1 (cons_1 A_0 (cons_1 B_0 (cons_1 A_0 (cons_1 B_0 nil_1))))))
  (and (= v_1 true_0) (= v_2 a!1)))
      )
      false
    )
  )
)

(check-sat)
(exit)
