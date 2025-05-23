(set-logic HORN)


(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@entry| ( Int Int ) Bool)
(declare-fun |main@bb13.i| ( Int Int Int (Array Int Int) Int (Array Int Int) Int Int (Array Int Int) ) Bool)
(declare-fun |main@bb44.i| ( Int (Array Int Int) Int (Array Int Int) Int Int ) Bool)
(declare-fun |main@bb30.i| ( Int (Array Int Int) Int (Array Int Int) Int Int (Array Int Int) Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Bool) (D (Array Int Int)) (E (Array Int Int)) (F (Array Int Int)) (G (Array Int Int)) (H Bool) (I Bool) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) (P (Array Int Int)) (Q Int) (R Int) (S (Array Int Int)) ) 
    (=>
      (and
        (main@entry K B)
        (and (= A B)
     (not (<= L 0))
     (not (<= O 0))
     (not (<= Q 0))
     (or (not I) (not H) (= F D))
     (or (not I) (not H) (= G E))
     (or (not I) (not H) (= N G))
     (or (not I) (not H) (= P F))
     (or (not I) (not H) (= J 0))
     (or (not I) (not H) (= M J))
     (or (not H) (and I H))
     (= C true)
     (= H true)
     (not (= (<= R 0) C)))
      )
      (main@bb13.i K L M N O P Q R S)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K (Array Int Int)) (L Int) (M (Array Int Int)) (N (Array Int Int)) (O Bool) (P Bool) (Q Int) (R Int) (S Int) (T Int) (U (Array Int Int)) (V Int) (W (Array Int Int)) (X Int) (Y Int) (Z (Array Int Int)) ) 
    (=>
      (and
        (main@bb13.i R S I D V F X Y Z)
        (and (or (not (<= E 0)) (not P) (<= S 0))
     (or (not (<= G 0)) (not P) (<= V 0))
     (or (not P) (not A) B)
     (or (not P) (not O) (= M J))
     (or (not P) (not O) (= N K))
     (or (not P) (not O) (= U N))
     (or (not P) (not O) (= W M))
     (or (not P) (not O) (= Q L))
     (or (not P) (not O) (= T Q))
     (or (not O) (and P O))
     (or (not P) (= J (store F G H)))
     (or (not P) (= K (store D E H)))
     (or (not P) (= C R))
     (or (not P) (= E (+ S I)))
     (or (not P) (= G (+ V I)))
     (or (not P) (= L (+ 1 I)))
     (or (not P) (not (<= S 0)))
     (or (not P) (not (<= V 0)))
     (or (not P) (and P A))
     (= O true)
     (not (= (<= Y I) B)))
      )
      (main@bb13.i R S T U V W X Y Z)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D (Array Int Int)) (E (Array Int Int)) (F Bool) (G Bool) (H Int) (I Int) (J (Array Int Int)) (K Int) (L (Array Int Int)) (M Int) (N Int) (O (Array Int Int)) (P Int) ) 
    (=>
      (and
        (main@bb13.i A I B J K L N P D)
        (and (or (not F) (= E D) (not G))
     (or (not F) (= O E) (not G))
     (or (not F) (= H 0) (not G))
     (or (not F) (= M H) (not G))
     (or (not F) (not C) (not G))
     (or (not F) (and F G))
     (= F true)
     (not (= (<= P B) C)))
      )
      (main@bb30.i I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J (Array Int Int)) (K Bool) (L Bool) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q (Array Int Int)) (R Int) (S Int) (T (Array Int Int)) (U Int) ) 
    (=>
      (and
        (main@bb30.i N O P Q G S D U)
        (and (or (not L) (<= S 0) (not (<= E 0)))
     (or (not L) (<= P 0) (not (<= C 0)))
     (or (not L) B (not A))
     (or (not K) (not L) (= J H))
     (or (not K) (= T J) (not L))
     (or (not K) (not L) (= M I))
     (or (not K) (= R M) (not L))
     (or (not L) (= H (store D E F)))
     (or (not L) (= E (+ S G)))
     (or (not L) (= I (+ 1 G)))
     (or (not L) (= F (select Q C)))
     (or (not L) (= C (+ P G)))
     (or (not L) (not (<= S 0)))
     (or (not L) (not (<= P 0)))
     (or (not L) (and L A))
     (or (not K) (and K L))
     (= K true)
     (not (= (<= U G) B)))
      )
      (main@bb30.i N O P Q R S T U)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Bool) (E Bool) (F Bool) (G Int) (H Int) (I (Array Int Int)) (J Int) (K (Array Int Int)) (L Int) (M Int) ) 
    (=>
      (and
        (main@bb30.i H I A B C J K M)
        (and (or (not F) (not E) (= G 0))
     (or (not F) (not E) (= L G))
     (or (not D) (not E) (not F))
     (or (not E) (and F E))
     (= E true)
     (not (= (<= M C) D)))
      )
      (main@bb44.i H I J K L M)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Bool) (L Bool) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q (Array Int Int)) (R Int) (S Int) ) 
    (=>
      (and
        (main@bb44.i N O P Q I S)
        (and (or (<= P 0) (not G) (not (<= D 0)))
     (or (<= N 0) (not (<= C 0)) (not G))
     (or (not L) (not K) (= M J))
     (or (not L) (not K) (= R M))
     (or H (not L) (not G))
     (or (not G) (= H (= E F)))
     (or (not G) (= F (select Q D)))
     (or (not G) (= C (+ N I)))
     (or (not G) (= E (select O C)))
     (or (not G) (= D (+ P I)))
     (or (not G) (not (<= P 0)))
     (or (not G) (not (<= N 0)))
     (or (not G) (and G B))
     (or (not K) (and L K))
     (or (not L) (= J (+ 1 I)))
     (or (not L) (and L G))
     (= A true)
     (= K true)
     (not (= (<= S I) A)))
      )
      (main@bb44.i N O P Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) ) 
    (=>
      (and
        (main@bb44.i D E H I G A)
        (and (or (<= D 0) (not M) (not (<= F 0)))
     (or (not M) (not (<= J 0)) (<= H 0))
     (or (not O) (not N) (not M))
     (or (not M) (= N (= K L)))
     (or (not M) (= F (+ D G)))
     (or (not M) (= J (+ H G)))
     (or (not M) (= K (select E F)))
     (or (not M) (= L (select I J)))
     (or (not M) (not (<= D 0)))
     (or (not M) (not (<= H 0)))
     (or (not M) (and M C))
     (or (not O) (and O M))
     (or (not P) (and P O))
     (or (not Q) (and Q P))
     (= B true)
     (= Q true)
     (not (= (<= A G) B)))
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
