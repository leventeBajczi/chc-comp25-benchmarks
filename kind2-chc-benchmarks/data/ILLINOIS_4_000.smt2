(set-logic HORN)


(declare-fun |excludes9_fun| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |ERR| ( ) Bool)
(declare-fun |illinois_step| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Bool Int Int Int Int Int Bool ) Bool)
(declare-fun |top_step| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Int Int Int Int Int Bool Bool Bool Int Int Int Int Int Bool Bool Bool ) Bool)
(declare-fun |top_reset| ( Int Int Int Int Int Bool Bool Bool Int Int Int Int Int Bool Bool Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |Sofar_step| ( Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |Sofar_reset| ( Bool Bool Bool Bool ) Bool)
(declare-fun |illinois_reset| ( Int Int Int Int Int Bool Int Int Int Int Int Bool ) Bool)
(declare-fun |MAIN| ( Int Int Int Int Int Bool Bool Bool Bool ) Bool)

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
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) ) 
    (=>
      (and
        (= J
   (or (and (not I)
            (not H)
            (not G)
            (not F)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not I) (not H) (not G) (not F) (not E) (not D) (not C) (not B) A)
       (and (not I) (not H) (not G) (not F) (not E) (not D) (not C) B (not A))
       (and (not I) (not H) (not G) (not F) (not E) (not D) C (not B) (not A))
       (and (not I) (not H) (not G) (not F) (not E) D (not C) (not B) (not A))
       (and (not I) (not H) (not G) (not F) E (not D) (not C) (not B) (not A))
       (and (not I) (not H) (not G) F (not E) (not D) (not C) (not B) (not A))
       (and (not I) (not H) G (not F) (not E) (not D) (not C) (not B) (not A))
       (and (not I) H (not G) (not F) (not E) (not D) (not C) (not B) (not A))
       (and I (not H) (not G) (not F) (not E) (not D) (not C) (not B) (not A))))
      )
      (excludes9_fun A B C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) ) 
    (=>
      (and
        (and (= H B) (= I C) (= J D) (= K E) (= L true) (= G A))
      )
      (illinois_reset A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Bool) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) ) 
    (=>
      (and
        (let ((a!1 (= D (and (>= D1 1) (>= (+ Z A1) 1))))
      (a!2 (and (or (= W C1) J) (or (not J) (= W (+ (- 1) C1)))))
      (a!4 (or (not Q) (and (or (= W C1) I) (or (not I) (= W 1)))))
      (a!5 (and (or (= W C1) H) (or (not H) (= W (+ 1 C1)))))
      (a!7 (and (or (= W C1) G) (or (not G) (= W (+ 1 C1)))))
      (a!9 (and (or (= W C1) F) (or (not F) (= W (+ (- 1) C1)))))
      (a!10 (and (or (= X A1) E) (or (not E) (= X (+ (- 1) A1)))))
      (a!12 (or (not Q) (and (or I (= X A1)) (or (not I) (= X 0)))))
      (a!13 (and (or G (= X A1)) (or (not G) (= X (+ (- 1) A1)))))
      (a!15 (or (not N) (and (or (not D) (= X B1)) (or (= X A1) D))))
      (a!16 (and (or (= X A1) C) (or (not C) (= X (+ 1 A1)))))
      (a!18 (or (not (<= U 0)) (= V (+ 1 (* (- 1) U)))))
      (a!20 (and (or E (= V D1)) (or (not E) (= V (+ 1 D1)))))
      (a!22 (and (or (= V D1) B) (or (not B) (= V (+ 1 D1)))))
      (a!24 (and (or J (= V D1)) (or (not J) (= V (+ 1 D1)))))
      (a!26 (and (or I (= V D1)) (or (not I) (= V (+ (- 1) D1 C1 Z A1)))))
      (a!28 (and (or H (= V D1)) (or (not H) (= V (+ (- 1) D1 Z)))))
      (a!30 (and (or D (= V D1)) (or (not D) (= V (+ (- 1) D1)))))
      (a!32 (and (or F (= V D1)) (or (not F) (= V (+ (- 1) D1)))))
      (a!34 (and (or C (= V D1)) (or (not C) (= V (+ (- 1) D1)))))
      (a!36 (and (or B (= Y Z)) (or (not B) (= Y (+ (- 1) Z)))))
      (a!38 (or (not Q) (and (or I (= Y Z)) (or (not I) (= Y 0)))))
      (a!39 (or (not P) (and (or H (= Y Z)) (or (not H) (= Y 0)))))
      (a!41 (and (or D (= Y Z)) (or (not D) (= Y (+ 1 Z A1)))))
      (a!43 (and (or F (= Y Z)) (or (not F) (= Y (+ 2 Z))))))
(let ((a!3 (or Q (and (or (not R) a!2) (or R (= W C1)))))
      (a!11 (or Q (and (or (not T) a!10) (or T (= X A1)))))
      (a!19 (or (not K) (and (or (<= U 0) (= V U)) a!18)))
      (a!21 (or S (and (or (not T) a!20) (or T (= V D1)))))
      (a!37 (or Q (and (or (not S) a!36) (or S (= Y Z))))))
(let ((a!6 (or O (and (or P (and a!3 a!4)) (or (not P) a!5))))
      (a!14 (or N (and (or O (and a!11 a!12)) (or (not O) a!13))))
      (a!23 (or R (and a!21 (or (not S) a!22))))
      (a!40 (or N (and (or P (and a!37 a!38)) a!39))))
(let ((a!8 (or M (and a!6 (or (not O) a!7))))
      (a!25 (or Q (and a!23 (or (not R) a!24))))
      (a!42 (or M (and a!40 (or (not N) a!41)))))
(let ((a!17 (or K
                (and a!8
                     (or (not M) a!9)
                     (or L (and a!14 a!15))
                     (or (not L) a!16))))
      (a!27 (or P (and a!25 (or (not Q) a!26))))
      (a!44 (or K (and a!42 (or (not M) a!43)))))
(let ((a!29 (or N (and a!27 (or (not P) a!28)))))
(let ((a!31 (or M (and a!29 (or (not N) a!30)))))
(let ((a!33 (or L (and a!31 (or (not M) a!32)))))
(let ((a!35 (or K (and a!33 (or (not L) a!34)))))
  (and (= G1 X)
       (= H1 0)
       (= I1 W)
       (= J1 V)
       (= A E1)
       (= B (>= Z 1))
       (= C (and (>= D1 1) (= C1 0) (= A1 0) (= Z 0)))
       a!1
       (= E (>= A1 1))
       (= F (and (>= D1 1) (>= C1 1)))
       (= G (>= A1 1))
       (= H (>= Z 1))
       (= I (>= D1 1))
       (= J (>= C1 1))
       (= K A)
       (or (not K) (= Y 0))
       a!17
       (or (not K) (and (= X 0) (= W 0)))
       a!19
       a!35
       a!44
       (not K1)
       (= F1 Y)))))))))))
      )
      (illinois_step L M N O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Bool) ) 
    (=>
      (and
        (illinois_reset A B C D E F I J K L M N)
        (Sofar_reset G H O P)
        true
      )
      (top_reset A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Int) (Z Bool) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Bool) (O1 Bool) (P1 Bool) ) 
    (=>
      (and
        (excludes9_fun P Q R S T U V W X B)
        (Sofar_step A N C D O1 P1)
        (illinois_step P Q R S T U V W X Y E O F G H I J K L M I1 J1 K1 L1 M1 N1)
        (let ((a!1 (= A (and B (not (<= Y 0))))))
  (and (= I B1)
       (= J C1)
       (= K D1)
       (= L E1)
       (= M F1)
       (= C G1)
       (= D H1)
       (= Z (or (not N) (>= O 0)))
       a!1
       (= H A1)))
      )
      (top_step P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Bool) (Y Bool) (Z Bool) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) ) 
    (=>
      (and
        (top_step I J K L M N O P Q R I1 S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1)
        INIT_STATE
        (top_reset A B C D E F G H S T U V W X Y Z)
        true
      )
      (MAIN A1 B1 C1 D1 E1 F1 G1 H1 I1)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) ) 
    (=>
      (and
        (top_step B C D E F G H I J K B1 L M N O P Q R S T U V W X Y Z A1)
        (MAIN L M N O P Q R S A)
        true
      )
      (MAIN T U V W X Y Z A1 B1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) ) 
    (=>
      (and
        (MAIN A B C D E F G H I)
        (not I)
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
