(set-logic HORN)


(declare-fun |mesi_reset| ( Int Int Int Int Bool Int Int Int Int Bool ) Bool)
(declare-fun |ERR| ( ) Bool)
(declare-fun |MAIN| ( Bool Bool Int Int Int Int Bool Bool ) Bool)
(declare-fun |excludes4_fun| ( Bool Bool Bool Bool Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |top_reset| ( Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Int Bool ) Bool)
(declare-fun |Sofar_step| ( Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |mesi_step| ( Bool Bool Bool Bool Int Int Int Int Int Int Int Int Bool Int Int Int Int Bool ) Bool)
(declare-fun |Abs_fun| ( Int Int ) Bool)
(declare-fun |top_step| ( Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Bool Bool Bool Int Int Int Int Bool ) Bool)
(declare-fun |Sofar_reset| ( Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (or (not (<= 0 A)) (= B A)) (or (<= 0 A) (= B (* (- 1) A))))
      )
      (Abs_fun A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) ) 
    (=>
      (and
        (and (= D true) (= C A))
      )
      (Sofar_reset A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (and (= B A)
     (= G D)
     (or B (= D (and E C)))
     (or (not B) (= D C))
     (not H)
     (= A F))
      )
      (Sofar_step C D E F G H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) ) 
    (=>
      (and
        (not (= (or (and D C) (and D B) (and D A) (and C B) (and C A) (and B A)) E))
      )
      (excludes4_fun A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) ) 
    (=>
      (and
        (and (= G B) (= H C) (= I D) (= J true) (= F A))
      )
      (mesi_reset A B C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T Int) (U Int) (V Int) (W Int) (X Bool) ) 
    (=>
      (and
        (let ((a!1 (and (= N O) (= M P) (= L Q) (= K R)))
      (a!2 (and (= N (+ (- 1) O R Q P)) (= M 0) (= L 1) (= K 0)))
      (a!6 (or (not D)
               (and (= N O) (= M P) (= L (+ (- 1) Q)) (= K (+ (- 1) R)))))
      (a!8 (or (not E)
               (and (= N (+ (- 1) O)) (= M (+ (- 2) P Q R)) (= L 0) (= K 0)))))
(let ((a!3 (or (not J) (and (or B a!1) (or (not B) a!2))))
      (a!4 (or (not I) (and (or C a!1) (or (not C) a!2)))))
(let ((a!5 (and (or I (and a!3 (or J a!1))) a!4)))
(let ((a!7 (and (or H a!5) (or (not H) (and (or D a!1) a!6)))))
(let ((a!9 (and (or G a!7) (or (not G) (and (or E a!1) a!8)))))
  (and (= U M)
       (= V L)
       (= W K)
       (= A S)
       (= B (>= O 1))
       (= C (>= P 1))
       (= D (>= Q 1))
       (= E (>= O 1))
       (= F A)
       (or (not F) (and (= N 3) (= M 0) (= L 0) (= K 0)))
       (or F a!9)
       (not X)
       (= T N)))))))
      )
      (mesi_step G H I J K L M N O P Q R S T U V W X)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Bool) ) 
    (=>
      (and
        (Sofar_reset A B H I)
        (mesi_reset C D E F G J K L M N)
        true
      )
      (top_reset A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Bool) ) 
    (=>
      (and
        (mesi_step R S T U I J K L A B C D E F1 G1 H1 I1 J1)
        (excludes4_fun R S T U F)
        (Sofar_step F M G H D1 E1)
        (Abs_fun I N)
        (Abs_fun J O)
        (Abs_fun K P)
        (Abs_fun L Q)
        (let ((a!1 (= V (or (not M) (<= (+ N O P Q) 3)))))
  (and (= B Z) (= C A1) (= D B1) a!1 (= E C1) (= G W) (= H X) (= A Y)))
      )
      (top_step R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      INIT_STATE
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Bool) (Z Bool) ) 
    (=>
      (and
        (top_step H I J K Z L M N O P Q R S T U V W X Y)
        INIT_STATE
        (top_reset A B C D E F G L M N O P Q R)
        true
      )
      (MAIN S T U V W X Y Z)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T Bool) ) 
    (=>
      (and
        (top_step B C D E T F G H I J K L M N O P Q R S)
        (MAIN F G H I J K L A)
        true
      )
      (MAIN M N O P Q R S T)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Bool) ) 
    (=>
      (and
        (MAIN A B C D E F G H)
        (not H)
      )
      ERR
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        ERR
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
