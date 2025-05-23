(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (and (= J G)
     (= I D)
     (= H 2)
     (= C 2)
     (= B 1)
     (= A 1)
     (not (<= D (- 1)))
     (or (not (= G E)) (not (= F 1)))
     (= K 1))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (+ J (* (- 1) G)) 4))))
  (and (= H 2)
       (= C 2)
       (= B 1)
       (= A 1)
       (not (<= D (- 1)))
       (or (= K 1) a!1)
       (or (not (= J G)) (= K 1))
       (or (not (= J E)) (= K F))
       (= I D)))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (and (= K 1)
     (= I D)
     (= H 2)
     (= C 2)
     (= B 1)
     (= A 1)
     (not (<= D (- 1)))
     (= (+ J (* (- 1) G)) 4))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) ) 
    (=>
      (and
        (INV_MAIN_42 L M N O P Q R S T U V)
        (INV_MAIN_42 W X Y Z A1 B1 C1 D1 E1 F1 G1)
        (let ((a!1 (not (>= (+ H (* (- 1) I)) 1))) (a!2 (not (>= (+ C (* (- 1) D)) 1))))
  (and (= (+ V G1 (* (- 1) K)) 0)
       (= (+ U (* (- 4) H) (* (- 1) G)) (- 8))
       (= (+ L A (* (- 1) B)) 0)
       (= (+ F1 (* (- 4) H) (* (- 1) G)) (- 12))
       (= (+ W A (* (- 1) B)) 0)
       (= (+ S (* (- 1) H)) (- 1))
       (= (+ N (* (- 1) C)) (- 1))
       (= (+ D1 (* (- 1) H)) (- 1))
       (= (+ Y (* (- 1) C)) (- 1))
       (= T I)
       (= R G)
       (= Q F)
       (= P E)
       (= O D)
       (= M A)
       (= E1 I)
       (= C1 G)
       (= B1 F)
       (= A1 E)
       (= Z D)
       (= X A)
       a!1
       a!2
       (= (+ J (* (- 4) H) (* (- 1) G)) (- 4))))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) ) 
    (=>
      (and
        (INV_MAIN_42 L M N O P Q R S T U V)
        (INV_MAIN_42 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1)
        (INV_MAIN_42 W X Y Z A1 B1 C1 D1 E1 F1 G1)
        (let ((a!1 (not (>= (+ H (* (- 1) I)) 1)))
      (a!2 (not (>= (+ C (* (- 1) D)) 1)))
      (a!3 (not (= (+ J (* (- 4) H) (* (- 1) G)) (- 4))))
      (a!5 (not (= (+ J (* (- 4) H) (* (- 1) G)) (- 8))))
      (a!6 (not (= (+ J (* (- 4) H) (* (- 1) G)) (- 12)))))
(let ((a!4 (or (= (+ V G1 (* (- 1) K)) 0) a!3)))
  (and (= (+ L A (* (- 1) B)) 0)
       (= (+ F1 (* (- 4) H) (* (- 1) G)) (- 12))
       (= (+ W A (* (- 1) B)) 0)
       (= (+ H1 A (* (- 1) B)) 0)
       (= (+ S (* (- 1) H)) (- 1))
       (= (+ N (* (- 1) C)) (- 1))
       (= (+ D1 (* (- 1) H)) (- 1))
       (= (+ Y (* (- 1) C)) (- 1))
       (= (+ O1 (* (- 1) H)) (- 1))
       (= (+ J1 (* (- 1) C)) (- 1))
       (= T I)
       (= R G)
       (= Q F)
       (= P E)
       (= O D)
       (= M A)
       (= E1 I)
       (= C1 G)
       (= B1 F)
       (= A1 E)
       (= Z D)
       (= X A)
       (= R1 K)
       (= Q1 J)
       (= P1 I)
       (= N1 G)
       (= M1 F)
       (= L1 E)
       (= K1 D)
       (= I1 A)
       a!1
       a!2
       a!4
       (or (= V K) a!5)
       (or (= G1 K) a!6)
       (= (+ U (* (- 4) H) (* (- 1) G)) (- 8)))))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) ) 
    (=>
      (and
        (INV_MAIN_42 L M N O P Q R S T U V)
        (let ((a!1 (not (>= (+ I (* (- 1) H)) 1))) (a!2 (not (>= (+ C (* (- 1) D)) 1))))
  (and (= (+ N (* (- 1) C)) (- 1))
       (= V K)
       (= U J)
       (= T I)
       (= S H)
       (= R G)
       (= Q F)
       (= P E)
       (= O D)
       (= M A)
       a!1
       a!2
       (= (+ L A (* (- 1) B)) 0)))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) ) 
    (=>
      (and
        (INV_MAIN_42 L M N O P Q R S T U V)
        (INV_MAIN_42 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1)
        (INV_MAIN_42 W X Y Z A1 B1 C1 D1 E1 F1 G1)
        (let ((a!1 (not (>= (+ H (* (- 1) I)) 1)))
      (a!2 (not (>= (+ D (* (- 1) C)) 1)))
      (a!3 (not (= (+ J (* (- 4) H) (* (- 1) G)) (- 4))))
      (a!5 (not (= (+ J (* (- 4) H) (* (- 1) G)) (- 8))))
      (a!6 (not (= (+ J (* (- 4) H) (* (- 1) G)) (- 12)))))
(let ((a!4 (or (= (+ V G1 (* (- 1) K)) 0) a!3)))
  (and (= (+ F1 (* (- 4) H) (* (- 1) G)) (- 12))
       (= (+ S (* (- 1) H)) (- 1))
       (= (+ D1 (* (- 1) H)) (- 1))
       (= (+ O1 (* (- 1) H)) (- 1))
       (= T I)
       (= R G)
       (= Q F)
       (= P E)
       (= O D)
       (= N C)
       (= M B)
       (= L A)
       (= E1 I)
       (= C1 G)
       (= B1 F)
       (= A1 E)
       (= Z D)
       (= Y C)
       (= X B)
       (= W A)
       (= R1 K)
       (= Q1 J)
       (= P1 I)
       (= N1 G)
       (= M1 F)
       (= L1 E)
       (= K1 D)
       (= J1 C)
       (= I1 B)
       (= H1 A)
       a!1
       a!2
       a!4
       (or (= V K) a!5)
       (or (= G1 K) a!6)
       (= (+ U (* (- 4) H) (* (- 1) G)) (- 8)))))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) ) 
    (=>
      (and
        (INV_MAIN_42 L M N O P Q R S T U V)
        (INV_MAIN_42 W X Y Z A1 B1 C1 D1 E1 F1 G1)
        (let ((a!1 (not (>= (+ H (* (- 1) I)) 1))) (a!2 (not (>= (+ D (* (- 1) C)) 1))))
  (and (= (+ V G1 (* (- 1) K)) 0)
       (= (+ U (* (- 4) H) (* (- 1) G)) (- 8))
       (= (+ F1 (* (- 4) H) (* (- 1) G)) (- 12))
       (= (+ S (* (- 1) H)) (- 1))
       (= (+ D1 (* (- 1) H)) (- 1))
       (= T I)
       (= R G)
       (= Q F)
       (= P E)
       (= O D)
       (= N C)
       (= M B)
       (= L A)
       (= E1 I)
       (= C1 G)
       (= B1 F)
       (= A1 E)
       (= Z D)
       (= Y C)
       (= X B)
       (= W A)
       a!1
       a!2
       (= (+ J (* (- 4) H) (* (- 1) G)) (- 4))))
      )
      (INV_MAIN_42 A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J K)
        (INV_MAIN_42 L M N O P Q R S T U V)
        (let ((a!1 (not (>= (+ T (* (- 1) S)) 1)))
      (a!2 (not (>= (+ O (* (- 1) N)) 1)))
      (a!3 (not (= (+ U (* (- 4) S) (* (- 1) R)) (- 4)))))
  (and (not (= K M))
       (= I T)
       (= H S)
       (= G R)
       (= F Q)
       (= E P)
       (= D O)
       (= C N)
       (= B M)
       (= A L)
       a!1
       a!2
       (or (= K V) a!3)
       (= (+ J (* (- 4) S) (* (- 1) R)) (- 4))))
      )
      false
    )
  )
)

(check-sat)
(exit)
