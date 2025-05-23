(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) (P (Array Int Int)) (Q Int) ) 
    (=>
      (and
        (and (not (= (select P N) 0))
     (= A B)
     (= I N)
     (= M (- 1))
     (not (= L (- 1)))
     (= L M)
     (= K (+ (- 1) (* (- 1) L)))
     (= H Q)
     (= G J)
     (= D E)
     (= C K)
     (>= I 0)
     (>= Q 0)
     (>= N 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (<= 0 L)
     (= (select O F) (select P F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) (Q (Array Int Int)) ) 
    (=>
      (and
        (and (= (select P F) (select Q F))
     (= (select Q N) 0)
     (= A B)
     (= I N)
     (= O (- 1))
     (not (= M (- 1)))
     (= M O)
     (= L (+ (- 1) (* (- 1) M)))
     (= H K)
     (= G J)
     (= D E)
     (= C L)
     (>= I 0)
     (>= N 0)
     (>= K 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (<= 0 O)
     (<= 0 M)
     (not (= P Q)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O (Array Int Int)) (P Int) (Q Int) ) 
    (=>
      (and
        (and (= (select O L) 0)
     (= A B)
     (= I L)
     (= Q (+ (- 1) (* (- 1) K)))
     (= M (- 1))
     (not (= K (- 1)))
     (= K M)
     (= H P)
     (= G J)
     (= D E)
     (= C Q)
     (>= I 0)
     (>= P 0)
     (>= L 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (not (<= 0 M))
     (<= 0 K)
     (= (select N F) (select O F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) (Q (Array Int Int)) ) 
    (=>
      (and
        (and (= (select P F) (select Q F))
     (= A B)
     (= I L)
     (not (= O (- 1)))
     (not (= N (- 1)))
     (= N O)
     (= M (+ (- 1) (* (- 1) N)))
     (= H K)
     (= G J)
     (= D E)
     (= C M)
     (>= I 0)
     (>= L 0)
     (>= K 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (<= 0 O)
     (<= 0 N)
     (not (= P Q)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O (Array Int Int)) (P Int) (Q Int) ) 
    (=>
      (and
        (and (= A B)
     (= I K)
     (= Q (+ (- 1) (* (- 1) L)))
     (not (= M (- 1)))
     (not (= L (- 1)))
     (= L M)
     (= H P)
     (= G J)
     (= D E)
     (= C Q)
     (>= I 0)
     (>= P 0)
     (>= K 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (not (<= 0 M))
     (<= 0 L)
     (= (select N F) (select O F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P (Array Int Int)) (Q Int) ) 
    (=>
      (and
        (let ((a!1 (= (store M N (+ (- 1) (* (- 1) O))) P)))
  (and (= (select M F) (select P F))
       (not (= (select P L) 0))
       (= A B)
       (not (= O (- 1)))
       (= O K)
       (= N Q)
       (= K (- 1))
       (= J (+ (- 1) (* (- 1) O)))
       (= H L)
       (= G I)
       (= D E)
       (= C J)
       (>= I 0)
       (>= Q 0)
       (>= N 0)
       (>= L 0)
       (>= H 0)
       (>= G 0)
       (not (<= 0 O))
       (not a!1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q (Array Int Int)) ) 
    (=>
      (and
        (and (= (select Q L) 0)
     (= A B)
     (not (= P (- 1)))
     (= P M)
     (= O J)
     (= M (- 1))
     (= K (+ (- 1) (* (- 1) P)))
     (= H L)
     (= G I)
     (= D E)
     (= C K)
     (>= I 0)
     (>= O 0)
     (>= L 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (not (<= 0 P))
     (<= 0 M)
     (= (select N F) (select Q F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q Int) ) 
    (=>
      (and
        (let ((a!1 (= (store L M (+ (- 1) (* (- 1) N))) (store O P Q))))
  (and (= (select L F) (select O F))
       (= (select O J) 0)
       (= A B)
       (= Q (+ (- 1) (* (- 1) N)))
       (not (= N (- 1)))
       (= N K)
       (= M P)
       (= K (- 1))
       (= H J)
       (= G I)
       (= D E)
       (= C Q)
       (>= I 0)
       (>= P 0)
       (>= M 0)
       (>= J 0)
       (>= H 0)
       (>= G 0)
       (not (<= 0 N))
       (not (<= 0 K))
       (not a!1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q (Array Int Int)) ) 
    (=>
      (and
        (and (= A B)
     (not (= P (- 1)))
     (= P M)
     (= O J)
     (not (= M (- 1)))
     (= L (+ (- 1) (* (- 1) P)))
     (= H K)
     (= G I)
     (= D E)
     (= C L)
     (>= I 0)
     (>= O 0)
     (>= K 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (not (<= 0 P))
     (<= 0 M)
     (= (select N F) (select Q F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q Int) ) 
    (=>
      (and
        (let ((a!1 (= (store L M (+ (- 1) (* (- 1) N))) (store O P Q))))
  (and (= (select L F) (select O F))
       (= A B)
       (= Q (+ (- 1) (* (- 1) N)))
       (not (= N (- 1)))
       (= N K)
       (= M P)
       (not (= K (- 1)))
       (= H J)
       (= G I)
       (= D E)
       (= C Q)
       (>= I 0)
       (>= P 0)
       (>= M 0)
       (>= J 0)
       (>= H 0)
       (>= G 0)
       (not (<= 0 N))
       (not (<= 0 K))
       (not a!1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        END_QUERY
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
