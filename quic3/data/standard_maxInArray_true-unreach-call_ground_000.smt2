(set-logic HORN)


(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@bb12.i| ( Int (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |main@bb36.i| ( (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |main@entry| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        true
      )
      (main@entry A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q Int) (R Int) ) 
    (=>
      (and
        (main@entry Q B)
        (and (= A B)
     (= C R)
     (= E F)
     (= F R)
     (not (<= P 0))
     (or (not K) (not J) (= H G))
     (or (not K) (not J) (= N H))
     (or (not K) (not J) (= I 0))
     (or (not K) (not J) (= L 0))
     (or (not K) (not J) (= M L))
     (or (not K) (not J) (= O I))
     (or (not J) (and K J))
     (= D true)
     (= J true)
     (not (= (<= C 0) D)))
      )
      (main@bb12.i M N O P Q R)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K Bool) (L Int) (M Bool) (N Int) (O Bool) (P Bool) (Q Int) (R Int) (S (Array Int Int)) (T Int) (U Int) (V (Array Int Int)) (W Int) (X Bool) (Y Bool) (Z Int) (A1 Int) (B1 (Array Int Int)) (C1 Int) (D1 Int) (E1 Int) (F1 Int) ) 
    (=>
      (and
        (main@bb12.i R F L D1 E1 F1)
        (let ((a!1 (or (not O) (not (= (<= H L) K)))))
  (and (= A (* 16777216 F1))
       (= B (div A 16777216))
       (or (not M) (not (<= I 0)) (<= D1 0))
       (or (not O) (not (<= G 0)) (<= D1 0))
       (or (not O) D (not C))
       (or (not O) (not M) K)
       (or (not P) (not O) (= Q L))
       (or (not P) (not O) (= T Q))
       (or (not P) (not O) (not K))
       (or (not Y) (and Y M) (and P O))
       (or (not Y) (not M) (= N J))
       (or (not Y) (not M) (= T N))
       (or (not Y) (not X) (= V S))
       (or (not Y) (not X) (= B1 V))
       (or (not Y) (not X) (= W T))
       (or (not Y) (not X) (= Z U))
       (or (not Y) (not X) (= A1 Z))
       (or (not Y) (not X) (= C1 W))
       (or (not M) (= I (+ D1 R)))
       (or (not M) (= J (select S I)))
       (or (not M) (not (<= D1 0)))
       (or (not M) (and O M))
       (or (not O) (= S (store F G H)))
       a!1
       (or (not O) (= E E1))
       (or (not O) (= G (+ D1 R)))
       (or (not O) (not (<= D1 0)))
       (or (not O) (and O C))
       (or (not P) O)
       (or (not X) (and Y X))
       (or (not Y) (= U (+ 1 R)))
       (= X true)
       (not (= (<= B R) D))))
      )
      (main@bb12.i A1 B1 C1 D1 E1 F1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (main@bb12.i C I J K A M)
        (and (= B (* 16777216 M))
     (= D (div B 16777216))
     (or (not G) (not F) (= H 0))
     (or (not G) (not F) (= L H))
     (or (not G) (not F) (not E))
     (or (not F) (and G F))
     (= F true)
     (not (= (<= D C) E)))
      )
      (main@bb36.i I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Bool) (L Bool) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q Int) (R Int) ) 
    (=>
      (and
        (main@bb36.i N O P I R)
        (let ((a!1 (or (not G) (not (= (<= F O) H)))))
  (and (= A (* 16777216 R))
       (= B (div A 16777216))
       (or (<= P 0) (not G) (not (<= E 0)))
       (or (not L) (not H) (not G))
       (or (not L) (not K) (= M J))
       (or (not L) (not K) (= Q M))
       a!1
       (or (not G) (= E (+ P I)))
       (or (not G) (= F (select N E)))
       (or (not G) (not (<= P 0)))
       (or (not G) (and D G))
       (or (not K) (and L K))
       (or (not L) (= J (+ 1 I)))
       (or (not L) (and L G))
       (= C true)
       (= K true)
       (not (= (<= B I) C))))
      )
      (main@bb36.i N O P Q R)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) ) 
    (=>
      (and
        (main@bb36.i H K G F A)
        (let ((a!1 (or (not L) (not (= (<= J K) M)))))
  (and (= B (* 16777216 A))
       (= C (div B 16777216))
       (or (<= G 0) (not L) (not (<= I 0)))
       (or M (not N) (not L))
       a!1
       (or (not L) (= I (+ G F)))
       (or (not L) (= J (select H I)))
       (or (not L) (not (<= G 0)))
       (or (not L) (and E L))
       (or (not N) (and N L))
       (or (not O) (and O N))
       (or (not P) (and P O))
       (= D true)
       (= P true)
       (not (= (<= C F) D))))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
