(set-logic HORN)

(declare-datatypes ((Bin_0 0)) (((One_0 ) (ZeroAnd_0  (projZeroAnd_0 Bin_0)) (OneAnd_0  (projOneAnd_0 Bin_0)))))

(declare-fun |diseqBin_0| ( Bin_0 Bin_0 ) Bool)
(declare-fun |s_0| ( Bin_0 Bin_0 ) Bool)
(declare-fun |plus_0| ( Bin_0 Bin_0 Bin_0 ) Bool)

(assert
  (forall ( (A Bin_0) (B Bin_0) (v_2 Bin_0) ) 
    (=>
      (and
        (and (= A (ZeroAnd_0 B)) (= v_2 One_0))
      )
      (diseqBin_0 v_2 A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (v_2 Bin_0) ) 
    (=>
      (and
        (and (= A (OneAnd_0 B)) (= v_2 One_0))
      )
      (diseqBin_0 v_2 A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (v_2 Bin_0) ) 
    (=>
      (and
        (and (= A (ZeroAnd_0 B)) (= v_2 One_0))
      )
      (diseqBin_0 A v_2)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (v_2 Bin_0) ) 
    (=>
      (and
        (and (= A (OneAnd_0 B)) (= v_2 One_0))
      )
      (diseqBin_0 A v_2)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) ) 
    (=>
      (and
        (and (= A (OneAnd_0 D)) (= B (ZeroAnd_0 C)))
      )
      (diseqBin_0 B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) ) 
    (=>
      (and
        (and (= A (ZeroAnd_0 D)) (= B (OneAnd_0 C)))
      )
      (diseqBin_0 B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) ) 
    (=>
      (and
        (diseqBin_0 C D)
        (and (= A (ZeroAnd_0 D)) (= B (ZeroAnd_0 C)))
      )
      (diseqBin_0 B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) ) 
    (=>
      (and
        (diseqBin_0 C D)
        (and (= A (OneAnd_0 D)) (= B (OneAnd_0 C)))
      )
      (diseqBin_0 B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) ) 
    (=>
      (and
        (s_0 C D)
        (and (= A (OneAnd_0 D)) (= B (ZeroAnd_0 C)))
      )
      (s_0 B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) ) 
    (=>
      (and
        (and (= B (OneAnd_0 C)) (= A (ZeroAnd_0 C)))
      )
      (s_0 B A)
    )
  )
)
(assert
  (forall ( (v_0 Bin_0) (v_1 Bin_0) ) 
    (=>
      (and
        (and true (= v_0 (ZeroAnd_0 One_0)) (= v_1 One_0))
      )
      (s_0 v_0 v_1)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) (E Bin_0) (F Bin_0) (G Bin_0) ) 
    (=>
      (and
        (s_0 E D)
        (plus_0 D G F)
        (and (= B (OneAnd_0 G)) (= C (ZeroAnd_0 E)) (= A (OneAnd_0 F)))
      )
      (plus_0 C B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) (E Bin_0) (F Bin_0) ) 
    (=>
      (and
        (plus_0 D F E)
        (and (= B (OneAnd_0 F)) (= C (OneAnd_0 D)) (= A (ZeroAnd_0 E)))
      )
      (plus_0 C B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) (v_4 Bin_0) ) 
    (=>
      (and
        (s_0 C A)
        (and (= A (OneAnd_0 D)) (= B (OneAnd_0 D)) (= v_4 One_0))
      )
      (plus_0 C B v_4)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) (E Bin_0) (F Bin_0) ) 
    (=>
      (and
        (plus_0 D F E)
        (and (= B (ZeroAnd_0 F)) (= C (OneAnd_0 D)) (= A (OneAnd_0 E)))
      )
      (plus_0 C B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) (E Bin_0) (F Bin_0) ) 
    (=>
      (and
        (plus_0 D F E)
        (and (= B (ZeroAnd_0 F)) (= C (ZeroAnd_0 D)) (= A (ZeroAnd_0 E)))
      )
      (plus_0 C B A)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) (v_4 Bin_0) ) 
    (=>
      (and
        (s_0 C A)
        (and (= A (ZeroAnd_0 D)) (= B (ZeroAnd_0 D)) (= v_4 One_0))
      )
      (plus_0 C B v_4)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (v_2 Bin_0) ) 
    (=>
      (and
        (s_0 A B)
        (= v_2 One_0)
      )
      (plus_0 A v_2 B)
    )
  )
)
(assert
  (forall ( (A Bin_0) (B Bin_0) (C Bin_0) (D Bin_0) ) 
    (=>
      (and
        (diseqBin_0 A B)
        (plus_0 B D C)
        (plus_0 A C D)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
