(set-logic HORN)


(declare-fun |INV_MAIN_0| ( Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1))))
  (and (= (+ J (* (- 1) C)) 1)
       (= (+ H (* (- 1) A)) 1)
       (= (+ E (* (- 1) D)) (- 1))
       a!1
       (= L F)
       (= I D)
       (= G B)
       (not (= F B))
       (not (= C (- 1)))
       (= (+ K (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1)))
      (a!2 (not (= (+ K (* (- 1) D)) (- 1)))))
  (and (= (+ J (* (- 1) C)) 1)
       (= (+ H (* (- 1) A)) 1)
       (= (+ E (* (- 1) D)) (- 1))
       a!1
       (= I D)
       (= G B)
       (not (= F B))
       (not (= C (- 1)))
       (or (not (= K A)) (= L F))
       a!2))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (+ E (* (- 1) D)) (- 1))))
      (a!3 (not (= (+ K (* (- 1) D)) (- 1)))))
(let ((a!2 (and (or (not (= K E)) (= L B)) (not (= E A)) a!1))
      (a!4 (and (or (not (= E A)) (= L F)) (or (= L F) a!1) (not (= L B)))))
  (and (= (+ H (* (- 1) A)) 1)
       (= I D)
       (= G B)
       (not (= C (- 1)))
       (or (not (= K E)) (= L F))
       (or (not (= F B)) a!2)
       (or a!3 a!4)
       (or (not (= K A)) a!4)
       (= (+ J (* (- 1) C)) 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (+ E (* (- 1) D)) (- 1))))
      (a!2 (not (= (+ D (* (- 1) A)) 1))))
  (and (= (+ J (* (- 1) C)) 1)
       (= (+ H (* (- 1) A)) 1)
       a!1
       a!2
       (not (= L B))
       (= I D)
       (= G B)
       (not (= C (- 1)))
       (or (not (= E A)) (= L F))
       (= (+ K (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 W1 X1 Y1 Z1 A2 B2 C2 D2 E2 F2 G2 H2)
        (INV_MAIN_0 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ E (* (- 1) D)) (- 1))))
      (a!2 (not (= (+ K (* (- 1) I)) (- 1))))
      (a!3 (not (= (+ K (* (- 1) H)) (- 1)))))
  (and (= (+ G1 (* (- 1) I)) (- 1))
       (= (+ F1 (* (- 1) H)) (- 1))
       (= (+ B1 (* (- 1) D)) (- 1))
       (= (+ A1 (* (- 1) C)) 1)
       (= (+ Y (* (- 1) A)) (- 1))
       (= (+ W (* (- 1) H)) (- 1))
       (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= (+ U1 (* (- 1) H)) (- 1))
       (= (+ T1 (* (- 1) J)) 1)
       (= (+ S1 (* (- 1) I)) (- 1))
       (= (+ R1 (* (- 1) H)) (- 1))
       (= (+ N1 (* (- 1) D)) (- 1))
       (= (+ M1 (* (- 1) C)) 1)
       (= (+ K1 (* (- 1) A)) (- 1))
       (= (+ F2 (* (- 1) J)) 1)
       (= (+ E2 (* (- 1) I)) (- 1))
       (= (+ D2 (* (- 1) H)) (- 1))
       (= (+ Z1 (* (- 1) D)) (- 1))
       (= (+ Y1 (* (- 1) C)) 1)
       (= (+ W1 (* (- 1) A)) (- 1))
       (not (= J 0))
       (not (= C (- 1)))
       (= J1 L)
       (= I1 K)
       (= E1 G)
       (not (= D1 B))
       (= C1 A)
       (= Z B)
       (= X V1)
       (= S G)
       (= R D1)
       (= Q A)
       (= N B)
       (not (= V1 G))
       (= Q1 G)
       (= P1 F)
       (= O1 E)
       (= L1 B)
       (= H2 L)
       (= G2 K)
       (= C2 G)
       (= B2 F)
       (= A2 E)
       (= X1 B)
       (or (= D1 F) a!1)
       (or (= D1 F) (not (= E A)))
       (or (= V1 L) a!2)
       (or (= V1 L) a!3)
       (= (+ H1 (* (- 1) J)) 1)))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ E (* (- 1) D)) (- 1)))))
  (and (= (+ W (* (- 1) H)) (- 1))
       (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= (+ I1 (* (- 1) H)) (- 1))
       (= (+ H1 (* (- 1) J)) 1)
       (= (+ G1 (* (- 1) I)) (- 1))
       (= (+ F1 (* (- 1) H)) (- 1))
       (= (+ B1 (* (- 1) D)) (- 1))
       (= (+ A1 (* (- 1) C)) 1)
       (= (+ Y (* (- 1) A)) (- 1))
       (not (= L G))
       (not (= J 0))
       (not (= I H))
       (not (= C (- 1)))
       (= X L)
       (= S G)
       (not (= R B))
       (= Q A)
       (= N B)
       (= J1 L)
       (= E1 G)
       (= D1 F)
       (= C1 E)
       (= Z B)
       (or (= R F) a!1)
       (or (= R F) (not (= E A)))
       (= (+ K (* (- 1) I)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1))))
  (and (= (+ E (* (- 1) D)) (- 1))
       a!1
       (= (+ W (* (- 1) H)) (- 1))
       (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (not (= L G))
       (not (= J 0))
       (not (= I H))
       (not (= F B))
       (not (= C (- 1)))
       (= X L)
       (= S G)
       (= R F)
       (= Q A)
       (= N B)
       (= (+ K (* (- 1) I)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1)))
      (a!2 (not (= (+ K (* (- 1) I)) (- 1))))
      (a!3 (not (= (+ K (* (- 1) H)) (- 1)))))
  (and a!1
       (= (+ W (* (- 1) H)) (- 1))
       (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= (+ H1 (* (- 1) J)) 1)
       (= (+ G1 (* (- 1) I)) (- 1))
       (= (+ F1 (* (- 1) H)) (- 1))
       (= (+ B1 (* (- 1) D)) (- 1))
       (= (+ A1 (* (- 1) C)) 1)
       (= (+ Y (* (- 1) A)) (- 1))
       (not (= J 0))
       (not (= F B))
       (not (= C (- 1)))
       (not (= X G))
       (= S G)
       (= R F)
       (= Q A)
       (= N B)
       (= J1 L)
       (= I1 K)
       (= E1 G)
       (= D1 F)
       (= C1 A)
       (= Z B)
       (or (= X L) a!2)
       (or (= X L) a!3)
       (= (+ E (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1))))
  (and a!1
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= (+ B1 (* (- 1) D)) (- 1))
       (= (+ A1 (* (- 1) C)) 1)
       (= (+ Y (* (- 1) A)) (- 1))
       (not (= F B))
       (not (= C (- 1)))
       (= X G)
       (= W H)
       (= V J)
       (= U I)
       (= T H)
       (= S G)
       (= R F)
       (= Q A)
       (= N B)
       (= J1 L)
       (= I1 K)
       (= H1 J)
       (= G1 I)
       (= F1 H)
       (= E1 G)
       (= D1 F)
       (= C1 A)
       (= Z B)
       (or (not (= K H)) (= L G))
       (= (+ E (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 W1 X1 Y1 Z1 A2 B2 C2 D2 E2 F2 G2 H2)
        (INV_MAIN_0 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ E (* (- 1) D)) (- 1)))))
  (and (= (+ A1 (* (- 1) C)) 1)
       (= (+ Y (* (- 1) A)) (- 1))
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= (+ N1 (* (- 1) D)) (- 1))
       (= (+ M1 (* (- 1) C)) 1)
       (= (+ K1 (* (- 1) A)) (- 1))
       (= (+ Z1 (* (- 1) D)) (- 1))
       (= (+ Y1 (* (- 1) C)) 1)
       (= (+ W1 (* (- 1) A)) (- 1))
       (not (= C (- 1)))
       (= J1 L)
       (= I1 K)
       (= H1 J)
       (= G1 I)
       (= F1 H)
       (= E1 G)
       (not (= D1 B))
       (= C1 A)
       (= Z B)
       (= X G)
       (= W H)
       (= V J)
       (= U I)
       (= T H)
       (= S G)
       (= R D1)
       (= Q A)
       (= N B)
       (= V1 G)
       (= U1 H)
       (= T1 J)
       (= S1 I)
       (= R1 H)
       (= Q1 G)
       (= P1 F)
       (= O1 E)
       (= L1 B)
       (= H2 L)
       (= G2 K)
       (= F2 J)
       (= E2 I)
       (= D2 H)
       (= C2 G)
       (= B2 F)
       (= A2 E)
       (= X1 B)
       (or (not (= K H)) (= L G))
       (or (= D1 F) a!1)
       (or (= D1 F) (not (= E A)))
       (= (+ B1 (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1))))
  (and a!1
       (= (+ P (* (- 1) D)) (- 1))
       (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= J 1)
       (not (= F B))
       (not (= C (- 1)))
       (= X L)
       (= W K)
       (= V 1)
       (= U I)
       (= T H)
       (= S G)
       (= R F)
       (= Q A)
       (= N B)
       (= (+ E (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ E (* (- 1) D)) (- 1)))))
  (and (= (+ O (* (- 1) C)) 1)
       (= (+ M (* (- 1) A)) (- 1))
       (= (+ B1 (* (- 1) D)) (- 1))
       (= (+ A1 (* (- 1) C)) 1)
       (= (+ Y (* (- 1) A)) (- 1))
       (= J 1)
       (not (= C (- 1)))
       (= X L)
       (= W K)
       (= V 1)
       (= U I)
       (= T H)
       (= S G)
       (not (= R B))
       (= Q A)
       (= N B)
       (= J1 L)
       (= I1 K)
       (= H1 1)
       (= G1 I)
       (= F1 H)
       (= E1 G)
       (= D1 F)
       (= C1 E)
       (= Z B)
       (or (= R F) a!1)
       (or (= R F) (not (= E A)))
       (= (+ P (* (- 1) D)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ K (* (- 1) I)) (- 1))))
      (a!2 (not (= (+ K (* (- 1) H)) (- 1)))))
  (and (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ H1 (* (- 1) J)) 1)
       (= (+ G1 (* (- 1) I)) (- 1))
       (= (+ F1 (* (- 1) H)) (- 1))
       (not (= J 0))
       (= C 0)
       (not (= X G))
       (= S G)
       (= R F)
       (= Q E)
       (= P D)
       (= O 0)
       (= N B)
       (= M A)
       (= J1 L)
       (= I1 K)
       (= E1 G)
       (= D1 F)
       (= C1 E)
       (= B1 D)
       (= A1 0)
       (= Z B)
       (= Y A)
       (or (= X L) a!1)
       (or (= X L) a!2)
       (= (+ W (* (- 1) H)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (and (= (+ W (* (- 1) H)) (- 1))
     (= (+ V (* (- 1) J)) 1)
     (= (+ U (* (- 1) I)) (- 1))
     (= (+ T (* (- 1) H)) (- 1))
     (not (= L G))
     (not (= J 0))
     (not (= I H))
     (= C 0)
     (= X L)
     (= S G)
     (= R F)
     (= Q E)
     (= P D)
     (= O 0)
     (= N B)
     (= M A)
     (= (+ K (* (- 1) I)) (- 1)))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ E (* (- 1) A)) 1))))
  (and (= (+ W (* (- 1) H)) (- 1))
       (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ Q (* (- 1) A)) 1)
       (= (+ I1 (* (- 1) H)) (- 1))
       (= (+ H1 (* (- 1) J)) 1)
       (= (+ G1 (* (- 1) I)) (- 1))
       (= (+ F1 (* (- 1) H)) (- 1))
       (not (= L G))
       (not (= J 0))
       (not (= I H))
       (= X L)
       (= S G)
       (= R B)
       (= P D)
       (= O C)
       (= N B)
       (= M A)
       (= J1 L)
       (= E1 G)
       (= D1 F)
       (= C1 E)
       (= B1 D)
       (= A1 C)
       (= Z B)
       (= Y A)
       (or (= F B) a!1)
       (= (+ K (* (- 1) I)) (- 1))))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) ) 
    (=>
      (and
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (INV_MAIN_0 W1 X1 Y1 Z1 A2 B2 C2 D2 E2 F2 G2 H2)
        (INV_MAIN_0 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (let ((a!1 (not (= (+ E (* (- 1) A)) 1)))
      (a!2 (not (= (+ K (* (- 1) I)) (- 1))))
      (a!3 (not (= (+ K (* (- 1) H)) (- 1)))))
  (and (= (+ G1 (* (- 1) I)) (- 1))
       (= (+ F1 (* (- 1) H)) (- 1))
       (= (+ C1 (* (- 1) A)) 1)
       (= (+ W (* (- 1) H)) (- 1))
       (= (+ V (* (- 1) J)) 1)
       (= (+ U (* (- 1) I)) (- 1))
       (= (+ T (* (- 1) H)) (- 1))
       (= (+ Q (* (- 1) A)) 1)
       (= (+ U1 (* (- 1) H)) (- 1))
       (= (+ T1 (* (- 1) J)) 1)
       (= (+ S1 (* (- 1) I)) (- 1))
       (= (+ R1 (* (- 1) H)) (- 1))
       (= (+ F2 (* (- 1) J)) 1)
       (= (+ E2 (* (- 1) I)) (- 1))
       (= (+ D2 (* (- 1) H)) (- 1))
       (not (= J 0))
       (= J1 L)
       (= I1 K)
       (= E1 G)
       (= D1 B)
       (= B1 D)
       (= A1 C)
       (= Z B)
       (= Y A)
       (= X V1)
       (= S G)
       (= R B)
       (= P D)
       (= O C)
       (= N B)
       (= M A)
       (not (= V1 G))
       (= Q1 G)
       (= P1 F)
       (= O1 E)
       (= N1 D)
       (= M1 C)
       (= L1 B)
       (= K1 A)
       (= H2 L)
       (= G2 K)
       (= C2 G)
       (= B2 F)
       (= A2 E)
       (= Z1 D)
       (= Y1 C)
       (= X1 B)
       (= W1 A)
       (or (= F B) a!1)
       (or (= V1 L) a!2)
       (or (= V1 L) a!3)
       (= (+ H1 (* (- 1) J)) 1)))
      )
      (INV_MAIN_0 A B C D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ P (* (- 1) M)) 1))))
  (and (= (+ Q (* (- 1) M)) 1)
       a!1
       (not (= L N))
       (= K P)
       (= J V)
       (= I U)
       (= H T)
       (= G S)
       (= F N)
       (= D P)
       (= C O)
       (= B N)
       (= A M)
       (= X S)
       (= W T)
       (not (= V 1))
       (= R N)
       (not (= O 0))
       (or (not (= U P)) (= L S))
       (or (not (= T P)) (= L S))
       (= (+ E (* (- 1) M)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1))))
  (and a!1
       (= L G)
       (= K H)
       (not (= J 1))
       (= I D)
       (not (= H D))
       (not (= G B))
       (= F B)
       (not (= C 0))
       (= (+ E (* (- 1) A)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ O1 (* (- 1) K1)) 1))))
  (and (= (+ E (* (- 1) K1)) 1)
       (= X V1)
       (= W O1)
       (= V T1)
       (= U S1)
       (= T R1)
       (= S Q1)
       (= R L1)
       (= P N1)
       (= O M1)
       (= N L1)
       (= M K1)
       (= L Q1)
       (= K R1)
       (= J T1)
       (= I S1)
       (= H R1)
       (= G Q1)
       (= F L1)
       (= D N1)
       (= C M1)
       (= B L1)
       (= A K1)
       (= J1 Q1)
       (= I1 R1)
       (= H1 T1)
       (= G1 S1)
       (= F1 R1)
       (= E1 Q1)
       (= D1 P1)
       (= C1 O1)
       (= B1 N1)
       (= A1 M1)
       (= Z L1)
       (= Y K1)
       (not (= V1 P1))
       (= U1 O1)
       (not (= T1 1))
       (not (= M1 0))
       (or (not (= S1 O1)) (= V1 Q1))
       (or (not (= R1 O1)) (= V1 Q1))
       (or (= P1 L1) a!1)
       (or (not (= O1 N1)) (= P1 L1))
       (= (+ Q (* (- 1) K1)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ Q (* (- 1) M)) 1))))
  (and (= L S)
       (= K T)
       (= J V)
       (= I Q)
       (= H T)
       (= G S)
       (= F N)
       (= D P)
       (= C O)
       (= B N)
       (= A M)
       (= X S)
       (= W T)
       (not (= V 1))
       (= U Q)
       (not (= T Q))
       (not (= S R))
       (not (= O 0))
       (or (= R N) a!1)
       (or (not (= Q P)) (= R N))
       (= (+ E (* (- 1) M)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (and (= L G)
     (= K H)
     (not (= J 1))
     (not (= I D))
     (= F B)
     (not (= C 0))
     (= (+ E (* (- 1) A)) 1))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ C1 (* (- 1) Y)) 1))))
  (and (= L J1)
       (= K I1)
       (= J 1)
       (= I G1)
       (= H F1)
       (= G E1)
       (= F N)
       (= D B1)
       (= C A1)
       (= B N)
       (= A Y)
       (= X J1)
       (= W I1)
       (= V 1)
       (= U G1)
       (= T F1)
       (= S E1)
       (= R D1)
       (= Q C1)
       (= P B1)
       (= O A1)
       (= M Y)
       (not (= B1 (- 1)))
       (not (= A1 0))
       (or (= N D1) a!1)
       (= (+ E (* (- 1) Y)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (let ((a!1 (not (= (+ Q (* (- 1) M)) 1))))
  (and (= L X)
       (= K Q)
       (= J 1)
       (= I U)
       (= H T)
       (= G S)
       (= F N)
       (= D P)
       (= C O)
       (= B N)
       (= A M)
       (not (= X R))
       (= W Q)
       (= V 1)
       (not (= O 0))
       (or (= R N) a!1)
       (or (not (= Q P)) (= R N))
       (= (+ E (* (- 1) M)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (let ((a!1 (not (= (+ D (* (- 1) A)) 1))))
  (and a!1
       (not (= L B))
       (= K D)
       (= J 1)
       (= F B)
       (not (= C 0))
       (= (+ E (* (- 1) A)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (and (= K F1)
     (= J H1)
     (= I G1)
     (= H F1)
     (= G S)
     (= F D1)
     (= E C1)
     (= D B1)
     (= C 0)
     (= B Z)
     (= A Y)
     (= X J1)
     (= W I1)
     (= V H1)
     (= U G1)
     (= T F1)
     (= R D1)
     (= Q C1)
     (= P B1)
     (= O 0)
     (= N Z)
     (= M Y)
     (not (= H1 1))
     (not (= G1 (- 1)))
     (or (not (= I1 F1)) (= S J1))
     (= L S))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (INV_MAIN_0 M N O P Q R S T U V W X)
        (and (= K T)
     (= J V)
     (= I U)
     (= H T)
     (= G S)
     (= F R)
     (= E Q)
     (= D P)
     (= C 0)
     (= B N)
     (= A M)
     (not (= X R))
     (= W Q)
     (not (= V 1))
     (= O 0)
     (or (not (= U Q)) (= X S))
     (or (not (= T Q)) (= X S))
     (= L S))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (and (= K H) (not (= J 1)) (= I E) (not (= H E)) (not (= G F)) (= C 0) (= L G))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J K L)
        (and (= K E) (= J 1) (= C 0) (not (= L F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
