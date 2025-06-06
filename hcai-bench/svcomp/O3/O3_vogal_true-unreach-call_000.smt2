(set-logic HORN)


(declare-fun |main@.preheader2| ( Int (Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun |main@_bb| ( Int (Array Int Int) Int Int Int ) Bool)
(declare-fun |main@precall.split| ( ) Bool)
(declare-fun |main@.preheader| ( Int Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |main@entry| ( Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q Int) (R (Array Int Int)) (S Int) (T Int) (U Bool) (V Int) (W Bool) (X Bool) (Y Int) (Z Int) (A1 (Array Int Int)) (B1 Int) (C1 Int) (D1 Int) ) 
    (=>
      (and
        (main@entry Q)
        (and (= E (store B C B1))
     (= I (store E F G))
     (= M (store I J K))
     (= R (store M N O))
     (= A1 (store R S T))
     (= A Q)
     (= C Z)
     (= D Q)
     (= F (+ 1 Z))
     (= H Q)
     (= J (+ 2 Z))
     (= L Q)
     (= N (+ 3 Z))
     (= P Q)
     (= S (+ 4 Z))
     (not (<= Z 0))
     (or (not X) (not W) (= V B1))
     (or (not X) (not W) (= Y 0))
     (or (not X) (not W) (= C1 V))
     (or (not X) (not W) (= D1 Y))
     (or (not (<= C 0)) (<= Z 0))
     (or (not (<= F 0)) (<= Z 0))
     (or (not (<= J 0)) (<= Z 0))
     (or (not (<= N 0)) (<= Z 0))
     (or (not (<= S 0)) (<= Z 0))
     (or (not W) (and X W))
     (= U true)
     (= W true)
     (= U (= T 0)))
      )
      (main@_bb Z A1 B1 C1 D1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (main@_bb L M N A B)
        (and (= G (+ 1 B))
     (or (not J) (not (<= E 0)) (<= L 0))
     (or (not J) (not I) (= H F))
     (or (not J) (not I) (= K G))
     (or (not J) (not I) (= O H))
     (or (not J) (not I) (= P K))
     (or (not C) (not J) (not D))
     (or (not I) (and J I))
     (or (not J) (= E (+ L G)))
     (or (not J) (= F (select M E)))
     (or (not J) (not (<= L 0)))
     (or (not J) (and C J))
     (= I true)
     (= D (= A 0)))
      )
      (main@_bb L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Bool) (L Bool) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q Int) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (main@_bb N O P A D)
        (and (= B (+ 1 D))
     (or (not L) (not K) (= M 0))
     (or (not L) (not K) (= Q I))
     (or (not L) (not K) (= I P))
     (or (not L) (not K) (= J 0))
     (or (not L) (not K) (= R J))
     (or (not L) (not K) (= S M))
     (or (not G) (not E) (= F D))
     (or (not G) (not E) (= T F))
     (or (not G) (not E) C)
     (or (not L) (not G) (not H))
     (or (not L) (and G L))
     (or (not K) (and K L))
     (or (not G) (= H (= T 0)))
     (or (not G) (and G E))
     (= K true)
     (= C (= A 0)))
      )
      (main@.preheader2 N O P Q R S T)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U (Array Int Int)) (V Int) (W Int) (X Int) (Y Int) (Z Int) ) 
    (=>
      (and
        (main@.preheader2 T U V D H C Z)
        (let ((a!1 (ite (>= M 0)
                (or (not (<= Z M)) (not (>= Z 0)))
                (and (not (<= Z M)) (not (<= 0 Z))))))
  (and (= E (= D 65))
       (= J a!1)
       (= N (+ F G))
       (= B (ite A 1 0))
       (= F (ite E 1 0))
       (= G (+ B C))
       (= M (+ 1 H))
       (or (not R) (not (<= K 0)) (<= T 0))
       (or (not R) (not I) J)
       (or (not R) (not Q) (= S N))
       (or (not R) (not Q) (= W O))
       (or (not R) (not Q) (= O L))
       (or (not R) (not Q) (= P M))
       (or (not R) (not Q) (= X P))
       (or (not R) (not Q) (= Y S))
       (or (not R) (= K (+ T M)))
       (or (not R) (= L (select U K)))
       (or (not R) (not (<= T 0)))
       (or (not R) (and R I))
       (or (not Q) (and Q R))
       (= Q true)
       (= A (= D 97))))
      )
      (main@.preheader2 T U V W X Y Z)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Bool) (F Int) (G Int) (H Bool) (I Bool) (J Int) (K Bool) (L Bool) (M Int) (N Int) (O Int) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X (Array Int Int)) ) 
    (=>
      (and
        (main@_bb W X M A D)
        (and (= B (+ 1 D))
     (or (not I) (not E) (= G F))
     (or (not I) (not E) (= F D))
     (or (not I) (not E) C)
     (or (not Q) (not P) (= R 0))
     (or (not Q) (not P) (= U R))
     (or (not Q) (not P) (= N M))
     (or (not Q) (not P) (= T N))
     (or (not Q) (not P) (= V O))
     (or (not Q) (not P) (= O 0))
     (or (not K) (not I) (= J 0))
     (or (not K) (not I) (= S J))
     (or (not K) (not I) H)
     (or (not K) (not Q) (not L))
     (or (not I) (= H (= G 0)))
     (or (not I) (and I E))
     (or (not P) (and Q P))
     (or (not Q) (and K Q))
     (or (not K) (= L (= M 0)))
     (or (not K) (and K I))
     (= P true)
     (= C (= A 0)))
      )
      (main@.preheader S T U V W X)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) (K Bool) (L Int) (M Bool) (N Int) (O Int) (P Bool) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Bool) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 (Array Int Int)) ) 
    (=>
      (and
        (main@.preheader2 D1 E1 T D H C J)
        (let ((a!1 (ite (>= I 0)
                (or (not (<= J I)) (not (>= J 0)))
                (and (not (<= J I)) (not (<= 0 J))))))
  (and (= E (= D 65))
       (= K a!1)
       (= F (ite E 1 0))
       (= B (ite A 1 0))
       (= G (+ B C))
       (= I (+ 1 H))
       (= L (+ F G))
       (or (not P) (not M) (= N L))
       (or (not P) (not M) (= O N))
       (or (not P) (not M) (not K))
       (or (not X) (not W) (= Y 0))
       (or (not X) (not W) (= B1 Y))
       (or (not X) (not W) (= U T))
       (or (not X) (not W) (= A1 U))
       (or (not X) (not W) (= C1 V))
       (or (not X) (not W) (= V 0))
       (or (not R) (not P) (= Q O))
       (or (not R) (not P) (= Z Q))
       (or (not R) (not X) (not S))
       (or (not P) (and P M))
       (or (not W) (and X W))
       (or (not X) (and R X))
       (or (not R) (= S (= T 0)))
       (or (not R) (and R P))
       (= W true)
       (= A (= D 97))))
      )
      (main@.preheader Z A1 B1 C1 D1 E1)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X (Array Int Int)) ) 
    (=>
      (and
        (main@.preheader S D C H W X)
        (and (= J (= K 0))
     (= E (= D 65))
     (= L (+ 1 H))
     (= G (+ B C))
     (= B (ite A 1 0))
     (= F (ite E 1 0))
     (= I (+ W L))
     (= K (select X I))
     (= M (+ F G))
     (not (<= W 0))
     (or (not Q) (not P) (= R M))
     (or (not Q) (not P) (= U R))
     (or (not Q) (not P) (= N K))
     (or (not Q) (not P) (= T N))
     (or (not Q) (not P) (= V O))
     (or (not Q) (not P) (= O L))
     (or (not Q) (not P) (not J))
     (or (not (<= I 0)) (<= W 0))
     (or (not P) (and Q P))
     (= P true)
     (= A (= D 97)))
      )
      (main@.preheader S T U V W X)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Bool) (F Int) (G Bool) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Int) (R Int) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) ) 
    (=>
      (and
        (main@_bb A B M C F)
        (and (= D (+ 1 F))
     (or (not O) (= P 0) (not V))
     (or (not O) (= Q P) (not V))
     (or (not O) N (not V))
     (or (not K) (not G) (= H F))
     (or (not K) (not G) (= I H))
     (or (not K) (not G) E)
     (or (not O) (not K) (= L 0))
     (or (not O) (not K) (= R L))
     (or (not O) (not K) J)
     (or (not V) (= T (= Q R)))
     (or (not V) (not (= T U)))
     (or (not V) (and O V))
     (or (not V) (not S))
     (or (not V) U)
     (or (not W) (and W V))
     (or (not O) (= N (= M 0)))
     (or (not O) (and K O))
     (or (not K) (= J (= I 0)))
     (or (not K) (and K G))
     (= W true)
     (= E (= C 0)))
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Int) (O Bool) (P Int) (Q Int) (R Bool) (S Int) (T Int) (U Bool) (V Bool) (W Int) (X Int) (Y Int) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) ) 
    (=>
      (and
        (main@.preheader2 A B T F J E L)
        (let ((a!1 (ite (>= K 0)
                (or (not (<= L K)) (not (>= L 0)))
                (and (not (<= L K)) (not (<= 0 L))))))
  (and (= G (= F 65))
       (= M a!1)
       (= I (+ D E))
       (= D (ite C 1 0))
       (= H (ite G 1 0))
       (= K (+ 1 J))
       (= N (+ H I))
       (or (not V) (= W 0) (not C1))
       (or (not V) (= X W) (not C1))
       (or (not V) U (not C1))
       (or (not R) (not O) (= P N))
       (or (not R) (not O) (= Q P))
       (or (not R) (not O) (not M))
       (or (not V) (not R) (= S Q))
       (or (not V) (not R) (= Y S))
       (or (not C1) (= A1 (= X Y)))
       (or (not C1) (not (= A1 B1)))
       (or (not C1) (and V C1))
       (or (not C1) (not Z))
       (or (not C1) B1)
       (or (not D1) (and D1 C1))
       (or (not V) (= U (= T 0)))
       (or (not V) (and R V))
       (or (not R) (and R O))
       (= D1 true)
       (= C (= F 97))))
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Bool) (O Int) (P Bool) (Q Int) (R Int) (S Bool) (T Int) (U Int) (V Int) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) ) 
    (=>
      (and
        (main@.preheader V D C H J K)
        (and (= A (= D 97))
     (= N (= M 0))
     (= B (ite A 1 0))
     (= F (ite E 1 0))
     (= O (+ F G))
     (= G (+ B C))
     (= I (+ 1 H))
     (= L (+ J I))
     (= M (select K L))
     (not (<= J 0))
     (or (not S) (not P) (= Q O))
     (or (not S) (not P) (= R Q))
     (or (not S) (= T R) (not Z))
     (or (not S) (= U T) (not Z))
     (or (not S) N (not P))
     (or (not (<= L 0)) (<= J 0))
     (or (not Z) (= X (= U V)))
     (or (not Z) (not (= X Y)))
     (or (not Z) (and S Z))
     (or (not Z) (not W))
     (or (not Z) Y)
     (or (not A1) (and A1 Z))
     (or (not S) (and S P))
     (= A1 true)
     (= E (= D 65)))
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@precall.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
