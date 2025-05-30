(set-logic HORN)

(declare-datatypes ((listOfInt 0)) (((conslistOfInt  (headlistOfInt Int) (taillistOfInt listOfInt)) (nillistOfInt ))))

(declare-fun |ff| ( ) Bool)
(declare-fun |sort| ( listOfInt listOfInt ) Bool)
(declare-fun |sorted| ( listOfInt Bool ) Bool)
(declare-fun |insort| ( Int listOfInt listOfInt ) Bool)

(assert
  (forall ( (A listOfInt) (B Int) (v_2 listOfInt) ) 
    (=>
      (and
        (and (= A (conslistOfInt B nillistOfInt)) (= v_2 nillistOfInt))
      )
      (insort B v_2 A)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C Int) (D Int) (E listOfInt) ) 
    (=>
      (and
        (and (= B (conslistOfInt D E))
     (<= C (+ (- 1) D))
     (= A (conslistOfInt C (conslistOfInt D E))))
      )
      (insort C B A)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C Int) (D Int) (E listOfInt) (F listOfInt) ) 
    (=>
      (and
        (insort C E F)
        (and (= B (conslistOfInt D E)) (>= C D) (= A (conslistOfInt D F)))
      )
      (insort C B A)
    )
  )
)
(assert
  (forall ( (A Bool) (v_1 listOfInt) ) 
    (=>
      (and
        (and (= A true) (= v_1 nillistOfInt))
      )
      (sorted v_1 A)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B Int) (C Bool) ) 
    (=>
      (and
        (and (= C true) (= A (conslistOfInt B nillistOfInt)))
      )
      (sorted A C)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B Int) (C Int) (D listOfInt) (E Bool) ) 
    (=>
      (and
        (and (>= B (+ 1 C)) (not E) (= A (conslistOfInt B (conslistOfInt C D))))
      )
      (sorted A E)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C Int) (D Int) (E listOfInt) (F Bool) ) 
    (=>
      (and
        (sorted A F)
        (and (= B (conslistOfInt C (conslistOfInt D E)))
     (<= C D)
     (= A (conslistOfInt D E)))
      )
      (sorted B F)
    )
  )
)
(assert
  (forall ( (v_0 listOfInt) (v_1 listOfInt) ) 
    (=>
      (and
        (and true (= v_0 nillistOfInt) (= v_1 nillistOfInt))
      )
      (sort v_0 v_1)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B Int) (C listOfInt) (D listOfInt) (E listOfInt) ) 
    (=>
      (and
        (insort B E D)
        (sort C E)
        (= A (conslistOfInt B C))
      )
      (sort A D)
    )
  )
)
(assert
  (forall ( (A Bool) (B listOfInt) (C listOfInt) ) 
    (=>
      (and
        (sorted C A)
        (sort B C)
        (= A true)
      )
      ff
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        ff
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
